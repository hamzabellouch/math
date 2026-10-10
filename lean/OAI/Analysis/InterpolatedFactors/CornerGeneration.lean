import OAI.Analysis.InterpolatedFactors.Recognition

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_1} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem filled_edge_corner_generated {p v x d a : A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hvr : v*(1-p)=v)
    (hvi : star v*v=1-p) (hpx : p*x=x) (hxr : x*(1-p)=x)
    (hf : IsSelfAdjoint (x*star v)) (hd : IsSelfAdjoint d) (hds : Supported p d)
    (ha : a∈Bicommutant.algebra (insert d (Bicommutant.algebra (insert p {x+star x}) : Set A)))
    (has : Supported p a) :
    a∈Bicommutant.algebra (insert p (insert (v*star v) (insert (x*star v) {d}))) := by
  have hvp := right_zero hvr
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hfs : Supported p (x*star v) :=
    ⟨by rw [← mul_assoc,hpx],by rw [mul_assoc,hvsp]⟩
  have hrs : Supported p (v*star v) :=
    ⟨by rw [← mul_assoc,hpv],by rw [mul_assoc,hvsp]⟩
  have htest (t : A) (ht : t∈StarSubalgebra.centralizer ℂ
      (insert p (insert (v*star v) (insert (x*star v) {d})))) : Commute t a := by
    have hc := (StarSubalgebra.mem_centralizer_iff ℂ).mp ht
    have htp : Commute p t := (hc _ (Set.mem_insert _ _)).1
    have htr : Commute (v*star v) t := (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).1
    have htf : Commute (x*star v) t :=
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))).1
    have htd : Commute d t :=
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))).1
    have hts : Supported p (p*t*p) :=
      ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by rw [mul_assoc,hp.isIdempotentElem.eq]⟩
    have hcs (z : A) (hz : Supported p z) (hzt : Commute z t) : Commute (p*t*p) z := by
      have hpz : Commute p z := hz.1.trans hz.2.symm
      exact (hpz.mul_left hzt.symm).mul_left hpz
    have hLP : Commute (lift v (p*t*p)) p :=
      lift_commute_supported hp.isSelfAdjoint hvp ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
        (hts.2.trans hts.1.symm)
    have hLV := lift_commute_edge hpv hvp hvi hvr hts (hcs _ hrs htr)
    have hLVS := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hvi hvr hts (hcs _ hrs htr)
    have hLF := lift_commute_supported hp.isSelfAdjoint hvp hfs (hcs _ hfs htf)
    have hx : x=(x*star v)*v := by rw [mul_assoc,hvi,hxr]
    have hLX : Commute (lift v (p*t*p)) x := by
      rw [hx]
      exact hLF.mul_right hLV
    have hLXS : Commute (lift v (p*t*p)) (star x) := by
      rw [hx,star_mul,hf.star_eq]
      exact hLVS.mul_right hLF
    have hLO : lift v (p*t*p)∈StarSubalgebra.centralizer ℂ (insert p {x+star x}) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro y (rfl|hy)
      · exact ⟨hLP.symm.eq,by rw [hp.isSelfAdjoint.star_eq];exact hLP.symm.eq⟩
      · rcases hy with rfl
        exact ⟨(hLX.add_right hLXS).symm.eq,by
          rw [star_add,star_star,add_comm (star x) x];exact (hLX.add_right hLXS).symm.eq⟩
    have hLD : Commute (lift v (p*t*p)) d :=
      lift_commute_supported hp.isSelfAdjoint hvp hds (hcs _ hds htd)
    have hL : lift v (p*t*p)∈StarSubalgebra.centralizer ℂ
        (insert d (Bicommutant.algebra (insert p {x+star x}) : Set A)) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro y (rfl|hy)
      · exact ⟨hLD.symm.eq,by rw [hd.star_eq];exact hLD.symm.eq⟩
      · exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hy _ hLO).1.symm,
          ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hy) _ hLO).1.symm⟩
    have he := ((StarSubalgebra.mem_centralizer_iff ℂ).mp ha _ hL).1
    rw [lift_mul_supported hvp has,supported_mul_lift hp.isSelfAdjoint hvp has] at he
    have htc : p*t*p=t*p := by rw [htp.eq,mul_assoc,hp.isIdempotentElem.eq]
    change t*a=a*t
    calc
      t*a=(t*p)*a := by rw [mul_assoc,has.1]
      _ = (p*t*p)*a := by rw [htc]
      _ = a*(p*t*p) := he
      _ = a*(t*p) := by rw [htc]
      _ = (a*p)*t := by rw [← htp.eq,mul_assoc]
      _ = a*t := by rw [has.2]
  rw [Bicommutant.algebra,StarSubalgebra.mem_centralizer_iff]
  intro t ht
  exact ⟨(htest t ht).eq,(htest (star t) (star_mem ht)).eq⟩
end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem weightedDefect_semicircle_eq (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
      (u:ℂ) • defectSemicircle u v i j := by
  simp only [weightedDefectCreation_eq,star_smul,Complex.star_def,Complex.conj_ofReal,
    defectSemicircle,smul_add]

theorem filled_corner_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι)
    (a : filledEdgeAlgebra u v i j) (ha : CornerRerouting.Supported P (a : Operator ι)) :
    (a : Operator ι)∈diffuseBase u v i j := by
  have hds : CornerRerouting.Supported P
      (weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)) := by
    rw [weightedDefect_semicircle_eq]
    exact ⟨by rw [mul_smul_comm,P_mul_defectSemicircle],
      by rw [smul_mul_assoc,defectSemicircle_mul_P]⟩
  have hh := CornerRerouting.filled_edge_corner_generated projection_P
    (edgePolar_left u v i) (edgePolar_right u v i) (edgePolar_initial u v hv.le hvu i)
    (offDiagonal_left u v i) (offDiagonal_right u v i) (leftModulus_selfAdjoint u v i)
    (IsSelfAdjoint.add_star_self (weightedDefectCreation u v i j)) hds a.property ha
  apply Bicommutant.generated_le (insert P {oldBaseGenerator u v i j})
    (insert P (insert (edgeRange u v i) (insert (leftModulus u v i)
      {weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)}))) ?_ hh
  intro x hx
  rcases hx with rfl|hx
  · exact P_mem_diffuseBase u v i j
  rcases hx with rfl|hx
  · exact edgeRange_mem_diffuseBase u v hv hvu i j
  rcases hx with rfl|hx
  · exact leftModulus_mem_diffuseBase u v hv hvu i j
  rcases hx with rfl
  rw [weightedDefect_semicircle_eq]
  exact (diffuseBase u v i j).smul_mem (defectSemicircle_mem_diffuseBase u v hv hvu i j) _
end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification CyclicSpectral
variable {ι : Type u_3} [DecidableEq ι]

theorem pRepresentation_mem_bicommutant (u v : ℝ) (i j : ι) (x : PCorner ι)
    (hx : (x:Operator ι)∈diffuseBase u v i j) :
    pRepresentation x∈Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) := by
  have hmul (a b : PCorner ι) : pRepresentation (a*b)=pRepresentation a*pRepresentation b :=
    (pRepresentation (ι := ι)).map_mul' a b
  have htest (B : PRange ι →L[ℂ] PRange ι)
      (hB : B∈StarSubalgebra.centralizer ℂ ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι))) :
      B*pRepresentation x=pRepresentation x*B := by
    let b := (pRepresentation (ι := ι)).symm B
    have hbA : Commute (oldBaseCorner u v i j) b := by
      apply (pRepresentation (ι := ι)).injective
      change pRepresentation (oldBaseCorner u v i j*b)=pRepresentation (b*oldBaseCorner u v i j)
      rw [hmul,hmul]
      simpa only [StarAlgEquiv.apply_symm_apply,oldBaseOp,b] using
        ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB _ (Set.mem_singleton _)).1
    have hb : (b:Operator ι)∈StarSubalgebra.centralizer ℂ (insert P {oldBaseGenerator u v i j}) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro T (rfl|hT)
      · exact ⟨b.property.1.trans b.property.2.symm,by
          rw [projection_P.isSelfAdjoint.star_eq];exact b.property.1.trans b.property.2.symm⟩
      · rcases hT with rfl
        have hh : oldBaseGenerator u v i j*(b:Operator ι)=(b:Operator ι)*oldBaseGenerator u v i j :=
          congrArg (fun z : PCorner ι => (z:Operator ι)) hbA.eq
        exact ⟨hh,by rw [(oldBaseGenerator_selfAdjoint u v i j).star_eq];exact hh⟩
    have hh : b*x=x*b := Subtype.ext (((StarSubalgebra.mem_centralizer_iff ℂ).mp hx _ hb).1)
    have he := congrArg (fun z : PCorner ι => pRepresentation z) hh
    rw [hmul,hmul] at he
    simpa only [StarAlgEquiv.apply_symm_apply,b] using he
  rw [Bicommutant.algebra,StarSubalgebra.mem_centralizer_iff]
  intro B hB
  exact ⟨htest B hB,htest (star B) (star_mem hB)⟩

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem representedBase_le_oldBase (hv : 0<v) (hvu : v<u) : representedBase u v ≤
    Bicommutant.algebra ({oldBaseOp u v (0:ℕ) 1} : Set (PRange ℕ →L[ℂ] PRange ℕ)) := by
  intro T hT
  have hh := filled_corner_mem_diffuseBase u v hv hvu (0:ℕ) 1
    (filledOfCorner ⟨(pRepresentation (ι := ℕ)).symm T,hT⟩)
    ((pRepresentation (ι := ℕ)).symm T).property
  simpa only [StarAlgEquiv.apply_symm_apply] using
    pRepresentation_mem_bicommutant u v (0:ℕ) 1 ((pRepresentation (ι := ℕ)).symm T) hh

theorem oldBaseOp_mem_weightedUniform : oldBaseOp u v (0:ℕ) 1∈
    Bicommutant.algebra (Set.range (weightedUniform u v hv hvu)) := by
  let : NormedRing (PRange ℕ →L[ℂ] PRange ℕ) := ContinuousLinearMap.toNormedRing
  let := oldBaseOp_noAtoms u v hv hvu
  have h := operator_mem_haar_bicommutant (oldBaseOp u v (0:ℕ) 1)
    (oldBaseOp_selfAdjoint u v 0 1) pRoot
    (Bicommutant.algebra ({oldBaseOp u v (0:ℕ) 1} : Set (PRange ℕ →L[ℂ] PRange ℕ)))
    (Set.isClosed_centralizer _)
    (Bicommutant.subset _ (Set.mem_singleton _))
    (oldBaseOp_commutant_total u v (hv.trans hvu).ne' hv.ne' (0:ℕ) 1)
  apply Bicommutant.mono _ (Set.range (weightedUniform u v hv hvu)) ?_ h
  intro T hT
  rcases hT with rfl
  exact ⟨uniformPhase,(uniformHom_phase (oldBaseOp u v (0:ℕ) 1)
    (oldBaseOp_selfAdjoint u v 0 1) pRoot).symm⟩

theorem representedBase_le_weightedUniform : representedBase u v ≤
    Bicommutant.algebra (Set.range (weightedUniform u v hv hvu)) := by
  apply (representedBase_le_oldBase u v hv hvu).trans
  apply Bicommutant.generated_le
  intro T hT
  rcases hT with rfl
  exact oldBaseOp_mem_weightedUniform u v hv hvu
end

section
open FreeFock Amplification WeightedCornerIndex
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem absorbed_kind_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (k : Kind) (hk : k.valid) : kindCreator u v k+star (kindCreator u v k.transpose)∈M := by
  have hh := ((cornerAbsorption u v hv hvu).output_generation M
    (fun i => hbase (kindLeft u v (description i)))
    (fun i => hbase (kindRight u v (description i)))).mpr hout
  have he := hh.1 (indexOf k)
  change kindCreator u v (description (indexOf k))+
    star (kindCreator u v (description (CircularRotation.flip (indexOf k))))∈M at he
  simpa only [description_flip,description_indexOf k hk] using he

theorem absorbed_raw_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (n : ℕ) : pFresh u v 0 (n+2) false false+star (pFresh u v 0 (n+2) false false)∈M := by
  have hh := ((cornerAbsorption u v hv hvu).output_generation M
    (fun i => hbase (kindLeft u v (description i)))
    (fun i => hbase (kindRight u v (description i)))).mpr hout
  obtain ⟨⟨i,m⟩,h⟩ := reservoirCode.surjective n
  simpa only [cornerAbsorption,rawReservoir,h] using hh.2 i m

theorem absorbed_fresh_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (n : ℕ) (r s : Bool) : pFresh u v 0 (n+2) r s+star (pFresh u v 0 (n+2) s r)∈M := by
  by_cases hh : r=false ∧ s=false
  · rcases hh with ⟨rfl,rfl⟩
    exact absorbed_raw_recovery u v hv hvu M hbase hout n
  · exact absorbed_kind_recovery u v hv hvu M hbase hout (.fresh n r s) hh

variable {ι : Type u_4} [DecidableEq ι]

theorem vertex_C_vertex (i : ι) (r : Bool) :
    vertex r*C u v i*vertex r=(weight u v r:ℂ) • edgeCreation i r r := by
  cases r
  · simp only [vertex,Bool.false_eq_true,ite_false,C,sub_mul,one_mul,mul_add,mul_smul_comm,
      P_creation_true,P_creation_false,sub_self,smul_zero,sub_zero,zero_add,
      smul_mul_assoc,weight,edgeCreation]
  · simp only [vertex,ite_true,C,mul_add,mul_smul_comm,P_creation_true,
      P_creation_false,smul_zero (M := ℂ) (A := Operator ι),add_zero,smul_mul_assoc,weight,edgeCreation]

theorem pDiagonal_eq_pFresh (i : ι) (r : Bool) :
    pDiagonal u v i i r=pFresh u v i i r r := by
  apply Subtype.ext
  change ((weight u v (!r):ℂ)/(u:ℂ)) •
    (supportedLeg u v i r*edgeCreation i (!r) (!r)*star (supportedLeg u v i r))=
      (u:ℂ)⁻¹ • (supportedLeg u v i r*C u v i*star (supportedLeg u v i r))
  have hh : supportedLeg u v i r*C u v i*star (supportedLeg u v i r)=
      (weight u v (!r):ℂ) •
        (supportedLeg u v i r*edgeCreation i (!r) (!r)*star (supportedLeg u v i r)) := by
    calc
      _ = supportedLeg u v i r*(vertex (!r)*C u v i*vertex (!r))*star (supportedLeg u v i r) := by
        simp only [← mul_assoc,supportedLeg_vertex]
        rw [mul_assoc _ (vertex (!r)),vertex_star_supportedLeg]
      _ = _ := by rw [vertex_C_vertex];simp only [mul_smul_comm,smul_mul_assoc]
  rw [hh,smul_smul]
  congr 1
  exact div_eq_inv_mul _ _
end

section
open FreeFock Amplification WeightedCornerIndex
variable {ι : Type u_5} [DecidableEq ι]

def blockCorner (u v : ℝ) (i j : ι) (r s : Bool) : PCorner ι :=
  sandwiched P projection_P (supportedLeg u v i r) (supportedLeg u v i s) (S u v j)
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i s)

theorem blockCorner_normalized (u v : ℝ) (hu : u≠0) (i j : ι) (r s : Bool) :
    blockCorner u v i j r s=(u:ℂ) • (pFresh u v i j r s+star (pFresh u v i j s r)) := by
  apply Subtype.ext
  change supportedLeg u v i r*S u v j*star (supportedLeg u v i s)=
    (u:ℂ) • (normalizedCreation u v i j r s+star (normalizedCreation u v i j s r))
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul,supportedCreation_paired]

def residualBlockCorner (u v : ℝ) (i j : ι) (r s : Option Bool) : PCorner ι :=
  sandwiched P projection_P (residualLeg u v i r) (residualLeg u v i s) (S u v j)
    (P_mul_residualLeg u v i r) (P_mul_residualLeg u v i s)

theorem residualBlockCorner_normalized (u v : ℝ) (hu : u≠0) (i j : ι) (r s : Option Bool) :
    residualBlockCorner u v i j r s=(u:ℂ) • (pResidual u v i j r s+star (pResidual u v i j s r)) := by
  apply Subtype.ext
  change residualLeg u v i r*S u v j*star (residualLeg u v i s)=
    (u:ℂ) • (normalizedResidual u v i j r s+star (normalizedResidual u v i j s r))
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul]
  exact (residualPair_eq u v i j r s).symm

theorem blockCorner_zero_off (u v : ℝ) (i : ι) :
    (blockCorner u v i i false true : Operator ι)=leftModulus u v i := by
  change P*S u v i*star (edgePolar u v i)=_
  have h : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [leftModulus,offDiagonal, mul_assoc _ (1-P),h]

theorem blockCorner_star (u v : ℝ) (i j : ι) (r s : Bool) :
    star (blockCorner u v i j r s)=blockCorner u v i j s r := by
  apply Subtype.ext
  change star (supportedLeg u v i r*S u v j*star (supportedLeg u v i s))=_
  simp only [star_mul,star_star,(S_selfAdjoint u v j).star_eq,mul_assoc]
  rfl

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
variable (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)

include hbase in
theorem old_off_block_mem : blockCorner u v (0:ℕ) 0 false true∈M := by
  apply hbase ⟨blockCorner u v 0 0 false true,?_⟩
  change (blockCorner u v 0 0 false true : Operator ℕ)∈filledEdgeAlgebra u v 0 1
  rw [blockCorner_zero_off]
  exact edgeAlgebra_le_filled u v 0 1
    (mul_mem (offDiagonal_mem_edge u v 0) (star_mem (edgePolar_mem_edge u v 0)))

include hout hbase in
theorem absorbed_old_block_recovery (r s : Bool) : blockCorner u v 0 0 r s∈M := by
  have hu : u≠0 := (hv.trans hvu).ne'
  cases r <;> cases s
  · rw [blockCorner_normalized u v hu,← pDiagonal_eq_pFresh]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.diagonal false) trivial) _
  · exact old_off_block_mem u v M hbase
  · rw [← blockCorner_star u v 0 0 false true]
    exact star_mem (old_off_block_mem u v M hbase)
  · rw [blockCorner_normalized u v hu,← pDiagonal_eq_pFresh]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.diagonal true) trivial) _

include hbase hout in
theorem absorbed_residual_block_recovery (a b : Option Bool) :
    residualBlockCorner u v (0:ℕ) 1 a b∈M := by
  have hu : u≠0 := (hv.trans hvu).ne'
  by_cases hab : a=none ∧ b=none
  · rcases hab with ⟨rfl,rfl⟩
    apply hbase ⟨residualBlockCorner u v 0 1 none none,?_⟩
    change residualLeg u v (0:ℕ) none*S u v 1*star (residualLeg u v 0 none)∈filledEdgeAlgebra u v 0 1
    rw [← residualPair_eq,residualPair_none_none]
    exact (filledEdgeAlgebra u v 0 1).smul_mem (defectSemicircle_mem_filled u v hu 0 1) _
  · rw [residualBlockCorner_normalized u v hu]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.residual a b) hab) _

omit hv hvu M hbase hout in
theorem blockCorner_split_false_false : blockCorner u v (0:ℕ) 1 false false=
    residualBlockCorner u v 0 1 none none+residualBlockCorner u v 0 1 (some false) none+
    (residualBlockCorner u v 0 1 none (some false)+residualBlockCorner u v 0 1 (some false) (some false)) := by
  apply Subtype.ext
  change P*S u v 1*star P=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [star_add (R := Operator ℕ),mul_add,add_mul]

omit hv hvu M hbase hout in
theorem blockCorner_split_false_true : blockCorner u v (0:ℕ) 1 false true=
    residualBlockCorner u v 0 1 none (some true)+residualBlockCorner u v 0 1 (some false) (some true) := by
  apply Subtype.ext
  change P*S u v 1*star (residualLeg u v 0 (some true))=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [add_mul]

omit hv hvu M hbase hout in
theorem blockCorner_split_true_false : blockCorner u v (0:ℕ) 1 true false=
    residualBlockCorner u v 0 1 (some true) none+residualBlockCorner u v 0 1 (some true) (some false) := by
  apply Subtype.ext
  change residualLeg u v 0 (some true)*S u v 1*star P=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [star_add (R := Operator ℕ),mul_add]

include hout hbase in
theorem absorbed_filled_block_recovery (r s : Bool) : blockCorner u v 0 1 r s∈M := by
  have hres := absorbed_residual_block_recovery u v hv hvu M hbase hout
  cases r <;> cases s
  · rw [blockCorner_split_false_false]
    exact add_mem (add_mem (hres _ _) (hres _ _)) (add_mem (hres _ _) (hres _ _))
  · rw [blockCorner_split_false_true];exact add_mem (hres _ _) (hres _ _)
  · rw [blockCorner_split_true_false];exact add_mem (hres _ _) (hres _ _)
  · exact hres (some true) (some true)

include hout hbase in
theorem absorbed_block_recovery (j : ℕ) (r s : Bool) : blockCorner u v 0 j r s∈M := by
  rcases j with _|(_|n)
  · exact absorbed_old_block_recovery u v hv hvu M hbase hout r s
  · exact absorbed_filled_block_recovery u v hv hvu M hbase hout r s
  · rw [blockCorner_normalized u v (hv.trans hvu).ne']
    exact M.smul_mem (absorbed_fresh_recovery u v hv hvu M hbase hout n r s) _
end

open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable {ι : Type u_6} [DecidableEq ι]

 theorem full_corner_commutant (u v : ℝ) (hv : 0<v) (hvu : v<u) (i₀ : ι)
    (X T : Operator ι) (hX : X ∈ ambientAlgebra u v)
    (hXs : CornerRerouting.Supported P X) (hT : CornerRerouting.Supported P T)
    (hR : Commute T (edgeRange u v i₀))
    (hA : ∀ i, Commute T (CornerRerouting.diagonal P (S u v i)))
    (hB : ∀ i, Commute T (CornerRerouting.offDiagonal P (edgePolar u v i₀) (S u v i)))
    (hBs : ∀ i, Commute T (star (CornerRerouting.offDiagonal P (edgePolar u v i₀) (S u v i))))
    (hC : ∀ i, Commute T (CornerRerouting.remaining P (edgePolar u v i₀) (S u v i))) :
    Commute T X :=
  CornerRerouting.corner_bicommutant projection_P (edgePolar_left u v i₀)
    (edgePolar_right u v i₀) (edgePolar_initial u v hv.le hvu i₀)
    hX hXs hT (S_selfAdjoint u v) hR hA hB hBs hC

def pAmbient (u v : ℝ) : StarSubalgebra ℂ (PCorner ι) :=
  subalgebraCorner (ambientAlgebra u v) P projection_P (P_mem_ambient u v)

theorem blockCorner_diagonal (u v : ℝ) (i j : ι) :
    (blockCorner u v i j false false : Operator ι)=CornerRerouting.diagonal P (S u v j) := by
  change P*S u v j*star P=P*S u v j*P
  rw [projection_P.isSelfAdjoint.star_eq]

theorem blockCorner_off (u v : ℝ) (i j : ι) :
    (blockCorner u v i j false true : Operator ι)=CornerRerouting.offDiagonal P (edgePolar u v i) (S u v j) := by
  change P*S u v j*star (edgePolar u v i)=P*S u v j*(1-P)*star (edgePolar u v i)
  have hh : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [mul_assoc _ (1-P),hh]

theorem blockCorner_remaining (u v : ℝ) (i j : ι) :
    (blockCorner u v i j true true : Operator ι)=CornerRerouting.remaining P (edgePolar u v i) (S u v j) := by
  change edgePolar u v i*S u v j*star (edgePolar u v i)=
    edgePolar u v i*(1-P)*S u v j*(1-P)*star (edgePolar u v i)
  have hh : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [edgePolar_right,mul_assoc _ (1-P),hh]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem pAmbient_recovered (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M) :
    pAmbient u v ≤ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (M : Set (PCorner ℕ)) : Set (PCorner ℕ)) := by
  intro X hX
  have htest (T : PCorner ℕ) (hT : T∈StarSubalgebra.centralizer ℂ (M : Set (PCorner ℕ))) : T*X=X*T := by
    have hc (a : PCorner ℕ) (ha : a∈M) : Commute (T:Operator ℕ) (a:Operator ℕ) :=
      (congrArg (fun b : PCorner ℕ => (b:Operator ℕ))
        (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT a ha).1)).symm
    have hblocks (j : ℕ) (r s : Bool) := hc (blockCorner u v 0 j r s)
      (absorbed_block_recovery u v hv hvu M hbase hout j r s)
    apply Subtype.ext
    apply full_corner_commutant u v hv hvu (0:ℕ) (X:Operator ℕ) (T:Operator ℕ) hX X.property T.property
    · exact hc (pSupport u v 0 1 true) (hbase (pSupport u v 0 1 true))
    · intro j;rw [← blockCorner_diagonal u v 0 j];exact hblocks j false false
    · intro j;rw [← blockCorner_off u v 0 j];exact hblocks j false true
    · intro j
      rw [← blockCorner_off u v 0 j]
      exact hc (star (blockCorner u v 0 j false true))
        (star_mem (absorbed_block_recovery u v hv hvu M hbase hout j false true))
    · intro j;rw [← blockCorner_remaining u v 0 j];exact hblocks j true true
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  exact ⟨htest T hT,htest (star T) (star_mem hT)⟩
end FreeGroupFactorMain.WeightedFock

end

end OAI
