import OAI.Analysis.InterpolatedFactors.Spectral

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

open Filter Topology
namespace FreeGroupFactorMain.OrthogonalSpectralSum
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Op := E →L[ℂ] E

theorem projection_inner (r : Op) (hr : IsStarProjection r) (ξ η : E) :
    inner ℂ (r ξ) (r η)=inner ℂ (r ξ) η := by
  calc
    _ = inner ℂ (r (r ξ)) η := by
      simpa only [← ContinuousLinearMap.star_eq_adjoint,hr.isSelfAdjoint.star_eq] using
        ContinuousLinearMap.adjoint_inner_right r (r ξ) η
    _ = _ := by rw [← mul_apply_eq_comp,hr.isIdempotentElem.eq]

theorem eigen_root_zero (r d f a : Op) (hr : IsStarProjection r) (hd : IsStarProjection d)
    (hrd : r*d=0) (hrf : r*f=f) (hfr : f*r=f) (hda : d*a=a) (had : a*d=a)
    (ξ : E)
    (hf : ∀ z : ℂ, ∀ η, f η=z • η → inner ℂ (r ξ) η=0)
    (ha : ∀ z : ℂ, ∀ η, a η=z • η → inner ℂ (d ξ) η=0)
    (κ z : ℂ) (η : E) (he : (f+a+κ • r) η=z • η) :
    inner ℂ ((r+d) ξ) η=0 := by
  have hdr : d*r=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,hd.isSelfAdjoint.star_eq,star_zero]
      using congrArg star hrd
  have hra : r*a=0 := by rw [← hda,← mul_assoc,hrd,zero_mul]
  have hdf : d*f=0 := by rw [← hrf,← mul_assoc,hdr,zero_mul]
  have hrB : r*(f+a+κ • r)=f+κ • r := by
    rw [mul_add,mul_add,hrf,hra,add_zero,mul_smul_comm,hr.isIdempotentElem.eq]
  have hdB : d*(f+a+κ • r)=a := by
    rw [mul_add,mul_add,hdf,hda,zero_add,mul_smul_comm,hdr,smul_zero,add_zero]
  have heR : f (r η)=(z-κ) • (r η) := by
    have hh : (f+κ • r) η=z • (r η) := by
      rw [← hrB,mul_apply_eq_comp,he,map_smul]
    change f η+κ • (r η)=z • (r η) at hh
    rw [← mul_apply_eq_comp,hfr,sub_smul]
    exact eq_sub_of_add_eq hh
  have heD : a (d η)=z • (d η) := by
    rw [← mul_apply_eq_comp,had,← hdB,mul_apply_eq_comp,he,map_smul]
  have hR := hf (z-κ) (r η) heR
  have hD := ha z (d η) heD
  rw [projection_inner r hr] at hR
  rw [projection_inner d hd] at hD
  rw [add_apply,inner_add_left,hR,hD,add_zero]

end FreeGroupFactorMain.OrthogonalSpectralSum
namespace FreeGroupFactorMain.SpectralSeparation
variable {A : Type u_2} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]

omit [StarRing A] [StarModule ℂ A] in

theorem cross_zero {p f t : A} (hp : IsIdempotentElem p) (hpf : Commute p f)
    (κ : ℝ) (hκ : 2*‖f‖<κ) (ht : Commute (f+(κ:ℂ) • p) t) : p*t*(1-p)=0 := by
  let y := p*t*(1-p)
  have hpq : p*(1-p)=0 := by rw [mul_sub,mul_one,hp.eq,sub_self]
  have hfq : Commute f (1-p) := (Commute.one_right f).sub_right hpf.symm
  have hl : p*((f+(κ:ℂ) • p)*t)*(1-p)=f*y+(κ:ℂ) • y := by
    dsimp [y]
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,← mul_assoc,hp.eq,hpf.eq]

  have hr : p*(t*(f+(κ:ℂ) • p))*(1-p)=y*f := by
    dsimp [y]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_assoc,hpq,
      mul_zero,smul_zero,add_zero,hfq.eq]

  have he : f*y+(κ:ℂ) • y=y*f := by
    rw [← hl,ht.eq,hr]
  have he' : (κ:ℂ) • y=y*f-f*y :=
    eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he)
  have hκ0 : 0<κ := (mul_nonneg (by norm_num : (0:ℝ)≤2) (norm_nonneg f)).trans_lt hκ
  have hb : κ*‖y‖≤(2*‖f‖)*‖y‖ := by
    calc
      κ*‖y‖ = ‖(κ:ℂ) • y‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hκ0]
      _ = ‖y*f-f*y‖ := congrArg norm he'
      _ ≤ ‖y*f‖+‖f*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖f‖+‖f‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2*‖f‖)*‖y‖ := by ring
  have hy : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hy

theorem separated_projection_mem {p f : A} (hp : IsStarProjection p)
    (hf : IsSelfAdjoint f) (hpf : Commute p f) (κ : ℝ) (hκ : 2*‖f‖<κ) :
    p ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({f+(κ:ℂ) • p} : Set A) : Set A) := by
  have hB : IsSelfAdjoint (f+(κ:ℂ) • p) := by
    show star (_+_)=_
    simp only [star_add,hf.star_eq,star_smul,hp.isSelfAdjoint.star_eq,
      Complex.star_def,Complex.conj_ofReal]
  have hc (t : A) (ht : t ∈ StarSubalgebra.centralizer ℂ ({f+(κ:ℂ) • p} : Set A)) :
      Commute p t := by
    have hb : Commute (f+(κ:ℂ) • p) t :=
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp ht _ (Set.mem_singleton _)).1
    have hz := cross_zero hp.isIdempotentElem hpf κ hκ hb
    have hbs : Commute (f+(κ:ℂ) • p) (star t) := by
      simpa only [hB.star_eq] using hb.star_star
    have hzs := congrArg star (cross_zero hp.isIdempotentElem hpf κ hκ hbs)
    have hq : star (1-p)=1-p := hp.one_sub.isSelfAdjoint.star_eq
    simp only [star_mul,star_star,hq,hp.isSelfAdjoint.star_eq,star_zero] at hzs
    have h₁ : p*t=p*t*p := by
      simpa only [mul_sub,mul_one,sub_eq_zero] using hz
    have h₂ : t*p=p*t*p := by
      simpa only [← mul_assoc,sub_mul,one_mul,sub_eq_zero] using hzs
    exact h₁.trans h₂.symm
  rw [StarSubalgebra.mem_centralizer_iff]
  intro t ht
  exact ⟨(hc t ht).symm.eq,(hc (star t) (star_mem ht)).symm.eq⟩

end FreeGroupFactorMain.SpectralSeparation
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem single_edge_corner_commute {p v x a t : A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hvr : v*(1-p)=v)
    (hvi : star v*v=1-p) (hpx : p*x=x) (hxr : x*(1-p)=x)
    (hd : IsSelfAdjoint (x*star v))
    (ha : a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {x+star x}) : Set A))
    (has : Supported p a) (ht : Supported p t)
    (htr : Commute t (v*star v)) (htf : Commute t (x*star v)) : Commute t a := by
  have hxp : x*p=0 := right_zero hxr
  have hpsx : p*star x=0 := star_left_zero hp.isSelfAdjoint hxp
  have hsxp : star x*p=star x := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpx
  have hqpx : (1-p)*x=0 := by rw [sub_mul,one_mul,hpx,sub_self]
  have hsxq : star x*(1-p)=0 := by rw [mul_sub,mul_one,hsxp,sub_self]
  let s : Unit → A := fun _ => x+star x
  have hsa : ∀ i, IsSelfAdjoint (s i) := by
    intro i
    show star (x+star x)=x+star x
    simp only [star_add,star_star,add_comm]
  have hset : Set.range s={x+star x} := by ext z; simp [s]
  have hA : a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (Set.range s)) : Set A) := by
    simpa only [hset] using ha
  apply corner_bicommutant hp hpv hvr hvi hA has ht hsa htr
  · intro i
    dsimp [diagonal,s]
    rw [mul_add,hpx,hpsx,add_zero,hxp]
    exact Commute.zero_right _
  · intro i
    dsimp [offDiagonal,s]
    rw [mul_add,hpx,hpsx,add_zero,hxr]
    exact htf
  · intro i
    dsimp [offDiagonal,s]
    rw [mul_add,hpx,hpsx,add_zero,hxr,hd.star_eq]
    exact htf
  · intro i
    dsimp [remaining,s]
    rw [mul_assoc v (1-p),mul_add,hqpx,zero_add,← mul_assoc,
      mul_assoc (v*(1-p)),hsxq,mul_zero,zero_mul]
    exact Commute.zero_right _

theorem single_edge_corner_generated {p v x a : A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hvr : v*(1-p)=v)
    (hvi : star v*v=1-p) (hpx : p*x=x) (hxr : x*(1-p)=x)
    (hd : IsSelfAdjoint (x*star v))
    (ha : a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {x+star x}) : Set A))
    (has : Supported p a) :
    a ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (insert (v*star v) {x*star v})) : Set A) := by
  have hpsv : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hpr : Commute p (v*star v) := by
    change p*(v*star v)=(v*star v)*p
    rw [← mul_assoc,hpv,mul_assoc,hpsv]
  have hpf : Commute p (x*star v) := by
    change p*(x*star v)=(x*star v)*p
    rw [← mul_assoc,hpx,mul_assoc,hpsv]
  have htest (t : A)
      (ht : t ∈ StarSubalgebra.centralizer ℂ (insert p (insert (v*star v) {x*star v}))) :
      Commute t a := by
    have hc := (StarSubalgebra.mem_centralizer_iff ℂ).mp ht
    have htp : Commute p t := (hc p (Set.mem_insert _ _)).1
    have htr : Commute (v*star v) t := (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).1
    have htf : Commute (x*star v) t :=
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))).1
    have hts : Supported p (p*t*p) := by
      constructor
      · rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq]
      · rw [mul_assoc,hp.isIdempotentElem.eq]
    have htc : p*t*p=t*p := by rw [htp.eq,mul_assoc,hp.isIdempotentElem.eq]
    have he := single_edge_corner_commute hp hpv hvr hvi hpx hxr hd ha has hts
      ((hpr.mul_left htr.symm).mul_left hpr) ((hpf.mul_left htf.symm).mul_left hpf)
    change t*a=a*t
    calc
      t*a=(t*p)*a := by rw [mul_assoc,has.1]
      _ = (p*t*p)*a := by rw [htc]
      _ = a*(p*t*p) := he.eq
      _ = a*(t*p) := by rw [htc]
      _ = (a*p)*t := by rw [← htp.eq,mul_assoc]
      _ = a*t := by rw [has.2]
  rw [StarSubalgebra.mem_centralizer_iff]
  intro t ht
  exact ⟨(htest t ht).eq,(htest (star t) (star_mem ht)).eq⟩

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_4} [DecidableEq ι]

theorem edgeRange_mul_P (u v : ℝ) (i : ι) : edgeRange u v i*P=edgeRange u v i := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,
    (edgeRange_projection u v i).isSelfAdjoint.star_eq] using congrArg star (edgeRange_le_P u v i)

theorem edgeRange_mul_defect (u v : ℝ) (i : ι) : edgeRange u v i*edgeDefect u v i=0 := by
  rw [edgeDefect,mul_sub,edgeRange_mul_P,(edgeRange_projection u v i).isIdempotentElem.eq,sub_self]

theorem defect_mul_edgeRange (u v : ℝ) (i : ι) : edgeDefect u v i*edgeRange u v i=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,star_zero (Operator ι)]
    using congrArg star (edgeRange_mul_defect u v i)

def defectSemicircle (u v : ℝ) (i j : ι) : Operator ι :=
  defectCreation u v i j+star (defectCreation u v i j)

theorem defectSemicircle_selfAdjoint (u v : ℝ) (i j : ι) :
    IsSelfAdjoint (defectSemicircle u v i j) :=
  IsSelfAdjoint.add_star_self (defectCreation u v i j)

theorem defectSemicircle_left (u v : ℝ) (i j : ι) :
    edgeDefect u v i*defectSemicircle u v i j=defectSemicircle u v i j := by
  have hh := congrArg star (defectCreation_right u v i j)
  simp only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq] at hh
  rw [defectSemicircle,mul_add,defectCreation_left,hh]

theorem defectSemicircle_right (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*edgeDefect u v i=defectSemicircle u v i j := by
  simpa only [star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq]
    using congrArg star (defectSemicircle_left u v i j)

theorem range_mul_defectSemicircle (u v : ℝ) (i j : ι) :
    edgeRange u v i*defectSemicircle u v i j=0 := by
  rw [← defectSemicircle_left u v i j,← mul_assoc,edgeRange_mul_defect,zero_mul]

theorem defectSemicircle_mul_range (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*edgeRange u v i=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq,star_zero (Operator ι)]
    using congrArg star (range_mul_defectSemicircle u v i j)

theorem P_mul_leftModulus (u v : ℝ) (i : ι) : P*leftModulus u v i=leftModulus u v i := by
  rw [leftModulus,← mul_assoc,offDiagonal_left]

theorem leftModulus_mul_P (u v : ℝ) (i : ι) : leftModulus u v i*P=leftModulus u v i := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(leftModulus_selfAdjoint u v i).star_eq]
    using congrArg star (P_mul_leftModulus u v i)

theorem P_mul_defectSemicircle (u v : ℝ) (i j : ι) :
    P*defectSemicircle u v i j=defectSemicircle u v i j := by
  rw [← defectSemicircle_left u v i j,← mul_assoc,P_mul_edgeDefect]

theorem defectSemicircle_mul_P (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*P=defectSemicircle u v i j := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq] using congrArg star (P_mul_defectSemicircle u v i j)

theorem compressed_edge_formula (u v : ℝ) (i : ι) :
    compressed u v i=(u:ℂ) • (edgeCreation i true true+star (edgeCreation i true true)) := by
  rw [compressed_formula]
  simp only [edgeCreation,vertex,ite_true,star_mul,projection_P.isSelfAdjoint.star_eq,P_creation_true]
  have hs : star (creation i true)*P=star (creation i true) := by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq] using congrArg star (P_creation_true i)
  rw [mul_assoc,hs]

theorem defectSemicircle_smul (u v : ℝ) (i j : ι) :
    (u:ℂ) • defectSemicircle u v i j=edgeDefect u v i*S u v j*edgeDefect u v i := by
  have he : edgeDefect u v i*compressed u v j*edgeDefect u v i=
      edgeDefect u v i*S u v j*edgeDefect u v i := by
    rw [compressed,← mul_assoc,← mul_assoc,edgeDefect_mul_P,mul_assoc (edgeDefect u v i*S u v j),P_mul_edgeDefect]
  rw [← he,compressed_edge_formula,mul_smul_comm,smul_mul_assoc]
  congr 1
  simp only [defectSemicircle,defectCreation,star_mul,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,mul_add,add_mul,mul_assoc]

theorem defectSemicircle_mem_ambient (u v : ℝ) (hu : u≠0) (i j : ι) :
    defectSemicircle u v i j∈ambientAlgebra u v := by
  have hd : edgeDefect u v i∈ambientAlgebra u v :=
    sub_mem (P_mem_ambient u v) (edgeRange_mem_ambient u v i)
  have hm : (u:ℂ) • defectSemicircle u v i j∈ambientAlgebra u v := by
    rw [defectSemicircle_smul]
    exact mul_mem (mul_mem hd (S_mem_ambient u v j)) hd
  have hh := (ambientAlgebra u v).smul_mem hm (u:ℂ)⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul] using hh

def oldBaseShift (u v : ℝ) (i j : ι) : ℝ :=
  2*‖leftModulus u v i+defectSemicircle u v i j‖+1

def oldBaseGenerator (u v : ℝ) (i j : ι) : Operator ι :=
  leftModulus u v i+defectSemicircle u v i j+(oldBaseShift u v i j:ℂ) • edgeRange u v i

theorem oldBaseGenerator_selfAdjoint (u v : ℝ) (i j : ι) :
    IsSelfAdjoint (oldBaseGenerator u v i j) := by
  change star (_+_)=_+_
  simp only [star_add (R := Operator ι),star_smul,(leftModulus_selfAdjoint u v i).star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    Complex.star_def,Complex.conj_ofReal]

theorem oldBaseGenerator_left (u v : ℝ) (i j : ι) :
    P*oldBaseGenerator u v i j=oldBaseGenerator u v i j := by
  rw [oldBaseGenerator,mul_add,mul_add,P_mul_leftModulus,P_mul_defectSemicircle,
    mul_smul_comm,edgeRange_le_P]

theorem oldBaseGenerator_right (u v : ℝ) (i j : ι) :
    oldBaseGenerator u v i j*P=oldBaseGenerator u v i j := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(oldBaseGenerator_selfAdjoint u v i j).star_eq]
    using congrArg star (oldBaseGenerator_left u v i j)

theorem oldBaseGenerator_mem_ambient (u v : ℝ) (hu : u≠0) (i j : ι) :
    oldBaseGenerator u v i j∈ambientAlgebra u v :=
  add_mem (add_mem (mul_mem (offDiagonal_mem_ambient u v i) (star_mem (edgePolar_mem_ambient u v i)))
    (defectSemicircle_mem_ambient u v hu i j))
    ((ambientAlgebra u v).smul_mem (edgeRange_mem_ambient u v i) _)

theorem oldBaseGenerator_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j : ι) (z : ℂ) (η : H ι) (he : oldBaseGenerator u v i j η=z • η) :
    η ([],true)=0 := by
  have hh := OrthogonalSpectralSum.eigen_root_zero
    (edgeRange u v i) (edgeDefect u v i) (leftModulus u v i) (defectSemicircle u v i j)
    (edgeRange_projection u v i) (edgeDefect_projection u v i) (edgeRange_mul_defect u v i)
    (range_mul_leftModulus u v hv.le hvu i) (leftModulus_mul_range u v hv.le hvu i)
    (defectSemicircle_left u v i j) (defectSemicircle_right u v i j)
    (lp.single 2 ([],true) 1) (leftModulus_eigen_root_zero u v hv hvu i)
    (defectSemicircle_eigen_root_zero u v hv hvu i j) (oldBaseShift u v i j) z η he
  have hp : edgeRange u v i+edgeDefect u v i=P := by rw [edgeDefect];abel
  rw [hp,P_nil_true] at hh
  simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hh

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Bicommutant
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
def algebra (S : Set A) := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set A)

theorem subset (S : Set A) : S ⊆ algebra S :=
  fun _ h => StarAlgebra.adjoin_le_centralizer_centralizer ℂ S (StarAlgebra.subset_adjoin ℂ S h)

theorem mono (S T : Set A) (h : S ⊆ T) : algebra S ≤ algebra T :=
  StarSubalgebra.centralizer_le ℂ _ _ (StarSubalgebra.centralizer_le ℂ _ _ h)

theorem generated_le (S T : Set A) (h : T ⊆ algebra S) : algebra T ≤ algebra S := by
  apply StarSubalgebra.centralizer_le
  intro t ht
  change t ∈ StarSubalgebra.centralizer ℂ T
  rw [StarSubalgebra.mem_centralizer_iff]
  intro x hx
  exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp (h hx) t ht).1.symm,
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem (h hx)) t ht).1.symm⟩
end FreeGroupFactorMain.Bicommutant

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

def diffuseBase (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (Operator ι) :=
  Bicommutant.algebra (insert P {oldBaseGenerator u v i j})

theorem P_mem_diffuseBase (u v : ℝ) (i j : ι) : P∈diffuseBase u v i j :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem oldBaseGenerator_mem_diffuseBase (u v : ℝ) (i j : ι) :
    oldBaseGenerator u v i j∈diffuseBase u v i j :=
  Bicommutant.subset _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem edgeRange_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    edgeRange u v i∈diffuseBase u v i j := by
  have hrf : Commute (edgeRange u v i) (leftModulus u v i+defectSemicircle u v i j) := by
    change _*(_+_)=(_+_)*_
    rw [mul_add,add_mul,range_mul_leftModulus u v hv.le hvu,leftModulus_mul_range u v hv.le hvu,
      range_mul_defectSemicircle,defectSemicircle_mul_range]
  have hh := SpectralSeparation.separated_projection_mem (edgeRange_projection u v i)
    ((leftModulus_selfAdjoint u v i).add (defectSemicircle_selfAdjoint u v i j)) hrf
    (oldBaseShift u v i j) (by dsimp [oldBaseShift]; linarith)
  exact Bicommutant.mono {oldBaseGenerator u v i j} (insert P {oldBaseGenerator u v i j})
    (Set.subset_insert _ _) hh

theorem leftModulus_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    leftModulus u v i∈diffuseBase u v i j := by
  have hr := edgeRange_mem_diffuseBase u v hv hvu i j
  have he : edgeRange u v i*oldBaseGenerator u v i j-
      (oldBaseShift u v i j:ℂ) • edgeRange u v i=leftModulus u v i := by
    rw [oldBaseGenerator,mul_add,mul_add,range_mul_leftModulus u v hv.le hvu,
      range_mul_defectSemicircle,add_zero,mul_smul_comm,(edgeRange_projection u v i).isIdempotentElem.eq,
      add_sub_cancel_right]
  rw [← he]
  exact sub_mem (mul_mem hr (oldBaseGenerator_mem_diffuseBase u v i j))
    ((diffuseBase u v i j).smul_mem hr _)

theorem edgeDefect_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    edgeDefect u v i∈diffuseBase u v i j :=
  sub_mem (P_mem_diffuseBase u v i j) (edgeRange_mem_diffuseBase u v hv hvu i j)

theorem defectSemicircle_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    defectSemicircle u v i j∈diffuseBase u v i j := by
  have he : oldBaseGenerator u v i j-leftModulus u v i-
      (oldBaseShift u v i j:ℂ) • edgeRange u v i=defectSemicircle u v i j := by
    rw [oldBaseGenerator]; abel
  rw [← he]
  exact sub_mem (sub_mem (oldBaseGenerator_mem_diffuseBase u v i j)
    (leftModulus_mem_diffuseBase u v hv hvu i j))
    ((diffuseBase u v i j).smul_mem (edgeRange_mem_diffuseBase u v hv hvu i j) _)

theorem edge_corner_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι)
    (a : edgeAlgebra u v i) (ha : CornerRerouting.Supported P (a : Operator ι)) :
    (a : Operator ι)∈diffuseBase u v i j := by
  have hh := CornerRerouting.single_edge_corner_generated projection_P
    (edgePolar_left u v i) (edgePolar_right u v i) (edgePolar_initial u v hv.le hvu i)
    (offDiagonal_left u v i) (offDiagonal_right u v i) (leftModulus_selfAdjoint u v i)
    a.property ha
  apply Bicommutant.generated_le (insert P {oldBaseGenerator u v i j})
    (insert P (insert (edgeRange u v i) {leftModulus u v i})) ?_ hh
  intro x hx
  rcases hx with rfl|hx
  · exact P_mem_diffuseBase u v i j
  rcases hx with rfl|hx
  · exact edgeRange_mem_diffuseBase u v hv hvu i j
  rcases hx with rfl
  exact leftModulus_mem_diffuseBase u v hv hvu i j

end FreeGroupFactorMain.WeightedFock

end

end OAI
