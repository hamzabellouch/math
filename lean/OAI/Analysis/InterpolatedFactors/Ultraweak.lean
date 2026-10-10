import OAI.Analysis.InterpolatedFactors.GroupBridge

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.HilbertUltraweak
variable (E : Type u_1) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[instance_reducible] def topology : TopologicalSpace (E →L[ℂ] E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : E →L[ℂ] E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

variable {E} {F : Type u_2} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
def sequenceMap (L : E →L[ℂ] F) (ξ : lp (fun _ : ℕ => E) 2) : lp (fun _ : ℕ => F) 2 :=
  ⟨fun k => L (ξ k),((lp.memℓp ξ).norm.const_mul ‖L‖).mono (fun k => L.le_opNorm (ξ k))⟩

omit [CompleteSpace E] in
theorem functional_continuous (ξ η : lp (fun _ : ℕ => E) 2) :
    @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (T (ξ k))) :=
  continuous_iInf_dom (i := ξ) (continuous_iInf_dom (i := η) continuous_induced_dom)

theorem sandwich_continuous (L : E →L[ℂ] F) (R : F →L[ℂ] E) :
    @Continuous _ _ (topology E) (topology F) (fun T : E →L[ℂ] E => L.comp (T.comp R)) := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he : (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))=
      (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (sequenceMap (ContinuousLinearMap.adjoint L) η k)
        (T (sequenceMap R ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    exact (ContinuousLinearMap.adjoint_inner_left L (T (R (ξ k))) (η k)).symm
  change @Continuous _ _ (topology E) _ (fun T : E →L[ℂ] E => ∑' k : ℕ,inner ℂ (η k) (L (T (R (ξ k)))))
  rw [he]
  exact functional_continuous _ _

theorem spatial_continuous (U : E ≃ₗᵢ[ℂ] F) :
    @Continuous _ _ (topology E) (topology F) U.conjStarAlgEquiv :=
  sandwich_continuous U.toContinuousLinearEquiv.toContinuousLinearMap U.symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
theorem add_continuous {X : Type u_3} [TopologicalSpace X] {f g : X → (E →L[ℂ] E)}
    (hf : @Continuous _ _ _ (topology E) f) (hg : @Continuous _ _ _ (topology E) g) :
    @Continuous _ _ _ (topology E) (fun x => f x+g x) := by
  let : TopologicalSpace (E →L[ℂ] E) := topology E
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have he (x : X) :
      (∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))=
        (∑' k : ℕ,inner ℂ (η k) (f x (ξ k)))+(∑' k : ℕ,inner ℂ (η k) (g x (ξ k))) := by
    simp only [add_apply,inner_add_right]
    exact (lp.summable_inner η (sequenceMap (f x) ξ)).tsum_add (lp.summable_inner η (sequenceMap (g x) ξ))
  change Continuous (fun x : X => ∑' k : ℕ,inner ℂ (η k) ((f x+g x) (ξ k)))
  simp_rw [he]
  exact ((functional_continuous ξ η).comp hf).add ((functional_continuous ξ η).comp hg)
end FreeGroupFactorMain.HilbertUltraweak

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_4} [Ring A] [StarRing A]

theorem lift_commute_four {p v t z : A} (hp : IsStarProjection p)
    (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)
    (ht : Supported p t) (htr : Commute t (v*star v))
    (ha : Commute t (p*z*p)) (hb : Commute t (p*z*star v))
    (hc : Commute t (v*z*p)) (hd : Commute t (v*z*star v)) : Commute (lift v t) z := by
  have hvp := right_zero hvr
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hsupport (a b : A) (hal : p*a=a) (hbr : b*p=b) : Supported p (a*z*b) := by
    exact ⟨by rw [← mul_assoc,← mul_assoc,hal],by rw [mul_assoc,hbr]⟩
  have ha' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport p p hp.isIdempotentElem.eq hp.isIdempotentElem.eq) ha
  have hb' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport p (star v) hp.isIdempotentElem.eq hvsp) hb
  have hc' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport v p hpv hp.isIdempotentElem.eq) hc
  have hd' := lift_commute_supported hp.isSelfAdjoint hvp (hsupport v (star v) hpv hvsp) hd
  have hv' := lift_commute_edge hpv hvp hvi hvr ht htr
  have hvs' := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hvi hvr ht htr
  have hz : z=p*z*p+(p*z*star v)*v+star v*(v*z*p)+star v*(v*z*star v)*v := by
    calc
      z = (p+star v*v)*z*(p+star v*v) := by rw [hvi]; noncomm_ring
      _ = _ := by noncomm_ring
  rw [hz]
  exact ((ha'.add_right (hb'.mul_right hv')).add_right (hvs'.mul_right hc')).add_right
    ((hvs'.mul_right hd').mul_right hv')
end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification CornerRerouting
variable {A : Type u_5} [CStarAlgebra A]

def bicomm (s : Set A) : StarSubalgebra ℂ A :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A)

def compress (p : A) (hp : IsStarProjection p) (a : A) : Corner p hp :=
  ⟨p*a*p,by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by rw [mul_assoc,hp.isIdempotentElem.eq]⟩

theorem compress_star (p : A) (hp : IsStarProjection p) (a : A) :
    compress p hp (star a)=star (compress p hp a) := by
  apply Subtype.ext
  change p*star a*p=star (p*a*p)
  simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc]

def compressedSet (p : A) (hp : IsStarProjection p) (s : Set A) : Set (Corner p hp) := compress p hp '' s

variable (p : A) (hp : IsStarProjection p) (s : Set A)
variable (hps : p∈StarSubalgebra.centralizer ℂ s)

theorem supported_commutant (x : Corner p hp) (hx : (x:A)∈StarSubalgebra.centralizer ℂ s) :
    x∈StarSubalgebra.centralizer ℂ (compressedSet p hp s) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  rintro _ ⟨y,hy,rfl⟩
  have hpy : Commute p (x:A) := x.property.1.trans x.property.2.symm
  have hyx : Commute y (x:A) := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx y hy).1
  have he : Commute (compress p hp y) x := by
    apply Subtype.ext
    exact ((hpy.mul_left hyx).mul_left hpy).eq
  have hyx' : Commute (star y) (x:A) :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx y hy).2
  have he' : Commute (compress p hp (star y)) x := by
    apply Subtype.ext
    exact ((hpy.mul_left hyx').mul_left hpy).eq
  rw [compress_star] at he'
  exact ⟨he.eq,he'.eq⟩

include hps in
theorem commutant_of_supported (x : Corner p hp)
    (hx : x∈StarSubalgebra.centralizer ℂ (compressedSet p hp s)) :
    (x:A)∈StarSubalgebra.centralizer ℂ s := by
  have htest (y : A) (hyP : Commute y p) (hh : Commute (compress p hp y) x) : Commute y (x:A) := by
    have hh' := congrArg Subtype.val hh.eq
    change (p*y*p)*(x:A)=(x:A)*(p*y*p) at hh'
    change y*(x:A)=(x:A)*y
    calc
      y*(x:A)= (p*y*p)*(x:A) := by
        calc
          y*(x:A) = (y*p)*(x:A) := by rw [mul_assoc,x.property.1]
          _ = (p*y)*(x:A) := by rw [hyP]
          _ = (p*y*p)*(x:A) := by rw [mul_assoc (p*y),x.property.1]
      _ = (x:A)*(p*y*p) := hh'
      _ = (x:A)*y := by
        calc
          (x:A)*(p*y*p) = (x:A)*(y*p) := by rw [← mul_assoc,← mul_assoc,x.property.2,mul_assoc]
          _ = (x:A)*(p*y) := by rw [hyP]
          _ = (x:A)*y := by rw [← mul_assoc,x.property.2]
  rw [StarSubalgebra.mem_centralizer_iff]
  intro y hy
  have hc := (StarSubalgebra.mem_centralizer_iff ℂ).mp hx _ ⟨y,hy,rfl⟩
  have hpY := (StarSubalgebra.mem_centralizer_iff ℂ).mp hps y hy
  refine ⟨(htest y hpY.1 hc.1).eq,?_⟩
  apply htest (star y) hpY.2
  change compress p hp (star y)*x=x*compress p hp (star y)
  rw [compress_star]
  exact hc.2

include hps in
theorem compress_mem (a : bicomm s) : compress p hp (a:A)∈bicomm (compressedSet p hp s) := by
  rw [bicomm,StarSubalgebra.mem_centralizer_iff]
  intro x hx
  have ht (z : Corner p hp) (hz : z∈StarSubalgebra.centralizer ℂ (compressedSet p hp s)) :
      Commute z (compress p hp (a:A)) := by
    have hzA := commutant_of_supported p hp s hps z hz
    have hza := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property (z:A) hzA).1
    have hzp : Commute (z:A) p := z.property.2.trans z.property.1.symm
    apply Subtype.ext
    exact ((hzp.mul_right hza).mul_right hzp).eq
  exact ⟨(ht x hx).eq,(ht (star x) (star_mem hx)).eq⟩

variable (v : A) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)

include hps hvs hpv hvr hvi in
theorem lift_mem (x : bicomm (compressedSet p hp s)) : lift v (x.val:A)∈bicomm s := by
  have hsupport (a b : A) (hal : p*a=a) (hbr : b*p=b) : Supported p (a*b) :=
    ⟨by rw [← mul_assoc,hal],by rw [mul_assoc,hbr]⟩
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hx (z : A) (hz : z∈StarSubalgebra.centralizer ℂ s) (hzp : Supported p z) :
      Commute (x.val:A) z := by
    let z' : Corner p hp := ⟨z,hzp⟩
    have hm := supported_commutant p hp s z' hz
    have hh := ((StarSubalgebra.mem_centralizer_iff ℂ).mp x.property z' hm).1
    exact (congrArg Subtype.val hh).symm
  have htest (z : A) (hz : z∈StarSubalgebra.centralizer ℂ s) : Commute (lift v (x.val:A)) z := by
    apply lift_commute_four hp hpv hvr hvi x.val.property
    · exact hx _ (mul_mem hvs (star_mem hvs)) (hsupport v (star v) hpv hvsp)
    · exact hx _ (mul_mem (mul_mem hps hz) hps)
        (hsupport (p*z) p (by rw [← mul_assoc,hp.isIdempotentElem.eq]) hp.isIdempotentElem.eq)
    · exact hx _ (mul_mem (mul_mem hps hz) (star_mem hvs))
        (hsupport (p*z) (star v) (by rw [← mul_assoc,hp.isIdempotentElem.eq]) hvsp)
    · exact hx _ (mul_mem (mul_mem hvs hz) hps)
        (hsupport (v*z) p (by rw [← mul_assoc,hpv]) hp.isIdempotentElem.eq)
    · exact hx _ (mul_mem (mul_mem hvs hz) (star_mem hvs))
        (hsupport (v*z) (star v) (by rw [← mul_assoc,hpv]) hvsp)
  rw [bicomm,StarSubalgebra.mem_centralizer_iff]
  intro z hz
  exact ⟨(htest z hz).symm.eq,(htest (star z) (star_mem hz)).symm.eq⟩

include hps hvs hpv hvi in
theorem lift_compress (a : bicomm s) : lift v (compress p hp (a:A):A)=(a:A) := by
  have hap := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property p hps).1
  have havs := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property v hvs).2
  change p*(a:A)*p+star v*(p*(a:A)*p)*v=(a:A)
  rw [hap,mul_assoc,hp.isIdempotentElem.eq,← mul_assoc (star v),havs,mul_assoc,hpv,mul_assoc,hvi]
  noncomm_ring

include hvr in
theorem compress_lift (x : Corner p hp) : compress p hp (lift v (x:A))=x := by
  have hvp := right_zero hvr
  apply Subtype.ext
  change p*lift v (x:A)*p=(x:A)
  rw [mul_assoc,lift_mul_supported hvp ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩,x.property.2,x.property.1]

def iso : bicomm s ≃⋆ₐ[ℂ] bicomm (compressedSet p hp s) where
  toFun a := ⟨compress p hp a,compress_mem p hp s hps a⟩
  invFun x := ⟨lift v (x.val:A),lift_mem p hp s hps v hvs hpv hvr hvi x⟩
  left_inv a := Subtype.ext (lift_compress p hp s hps v hvs hpv hvi a)
  right_inv x := Subtype.ext (compress_lift p hp v hvr x.val)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    have hpA := ((StarSubalgebra.mem_centralizer_iff ℂ).mp a.property p hps).1
    change p*((a:A)*(b:A))*p=(p*(a:A)*p)*(p*(b:A)*p)
    calc
      p*((a:A)*(b:A))*p = (p*(a:A))*((b:A)*p) := by simp only [mul_assoc]
      _ = ((a:A)*p)*((b:A)*p) := by rw [hpA]
      _ = (p*(a:A)*p)*(p*(b:A)*p) := by
        rw [hpA]
        simp only [mul_assoc,← mul_assoc p p,hp.isIdempotentElem.eq]
  map_add' a b := by
    apply Subtype.ext; apply Subtype.ext
    change p*((a:A)+(b:A))*p=p*(a:A)*p+p*(b:A)*p
    simp only [mul_add,add_mul]
  map_smul' c a := by
    apply Subtype.ext; apply Subtype.ext
    change p*(c • (a:A))*p=c • (p*(a:A)*p)
    simp only [mul_smul_comm,smul_mul_assoc]
  map_star' a := Subtype.ext (compress_star p hp (a:A))
end FreeGroupFactorMain.FullReducingCorner

end

namespace FreeGroupFactorMain.ReducingSubspace
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [CompleteSpace K]

def reduce (T : E →L[ℂ] E) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (T.comp K.subtypeL)

theorem reduce_apply (T : E →L[ℂ] E) (hT : ∀ ξ∈K,T ξ∈K) (ξ : K) :
    (reduce K T ξ:E)=T ξ := K.starProjection_eq_self_iff.mpr (hT ξ ξ.property)

theorem reduce_one : reduce K (1:E →L[ℂ] E)=1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto_mem_subspace_eq_self ξ

theorem reduce_add (T U : E →L[ℂ] E) : reduce K (T+U)=reduce K T+reduce K U := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto.map_add _ _

theorem reduce_smul (c : ℂ) (T : E →L[ℂ] E) : reduce K (c • T)=c • reduce K T := by
  apply ContinuousLinearMap.ext
  intro ξ
  exact K.orthogonalProjectionOnto.map_smul c _

theorem inner_reduce (T : E →L[ℂ] E) (ξ η : K) :
    inner ℂ ξ (reduce K T η)=inner ℂ (ξ:E) (T η) :=
  K.inner_orthogonalProjectionOnto_eq_of_mem_left ξ (T η)

variable [CompleteSpace E]

theorem reduce_star (T : E →L[ℂ] E) : reduce K (star T)=star (reduce K T) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [inner_reduce,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (K.inner_orthogonalProjectionOnto_eq_of_mem_right ξ (T η)).symm

omit [CompleteSpace E] in
theorem reduce_mul (T U : E →L[ℂ] E) (hU : ∀ ξ∈K,U ξ∈K) :
    reduce K (T*U)=reduce K T*reduce K U := by
  apply ContinuousLinearMap.ext
  intro ξ
  change K.orthogonalProjectionOnto (T (U ξ))=K.orthogonalProjectionOnto (T (reduce K U ξ:E))
  rw [reduce_apply K U hU]
end FreeGroupFactorMain.ReducingSubspace

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace
variable {A : Type u_7} {E : Type u_8} {I : Type u_9} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

def reducedCoeff : A →⋆ₐ[ℂ] (X.normalHull →L[ℂ] X.normalHull) where
  toFun a := reduce X.normalHull (X.coeff a)
  map_zero' := by simp [reduce]
  map_one' := by rw [map_one,reduce_one]
  map_add' a b := by rw [map_add,reduce_add]
  map_mul' a b := by rw [map_mul,reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_coeff b h)]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,reduce_smul,reduce_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,reduce_star]

def reducedSystem : System A X.normalHull I covariance where
  coeff := X.reducedCoeff
  root := ⟨X.root,X.normalHull_root⟩
  create i := reduce X.normalHull (X.create i)
  contract i j a := by
    change star (reduce X.normalHull (X.create i))*reduce X.normalHull (X.coeff a)*
      reduce X.normalHull (X.create j)=reduce X.normalHull (X.coeff (covariance i j a))
    rw [← reduce_star,← reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_coeff a h),
      ← reduce_mul X.normalHull _ _ (fun _ h => X.normalHull_create j h),X.contract]
  annihilate i a := by
    apply Subtype.ext
    rw [← reduce_star,reduce_apply X.normalHull _ (fun _ h => X.normalHull_annihilate i h)]
    change star (X.create i) ((reduce X.normalHull (X.coeff a) ⟨X.root,X.normalHull_root⟩):E)=0
    rw [reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h),X.annihilate]

theorem reducedSystem_normal (a : A) (w : List (I × A)) :
    (X.reducedSystem.normal a w:E)=X.normal a w := by
  induction w generalizing a with
  | nil => exact reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h) _
  | cons q w ih =>
    rcases q with ⟨i,b⟩
    change (reduce X.normalHull (X.coeff a)
      (reduce X.normalHull (X.create i) (X.reducedSystem.normal b w)):E)=_
    rw [reduce_apply X.normalHull _ (fun _ h => X.normalHull_coeff a h),
      reduce_apply X.normalHull _ (fun _ h => X.normalHull_create i h),ih]
    rfl

theorem reducedSystem_family (w : Word A I) : (X.reducedSystem.family w:E)=X.family w :=
  X.reducedSystem_normal _ _

theorem reducedSystem_state (a : A) :
    inner ℂ X.reducedSystem.root (X.reducedSystem.coeff a X.reducedSystem.root)=
      inner ℂ X.root (X.coeff a X.root) := inner_reduce X.normalHull _ _ _

theorem reducedSystem_total :
    (Submodule.span ℂ (Set.range X.reducedSystem.family)).topologicalClosure=⊤ := by
  have hi : (Subtype.val '' (Submodule.span ℂ (Set.range X.reducedSystem.family) : Set X.normalHull))=
      (X.normalSpan:Set E) := by
    change ((Submodule.span ℂ (Set.range X.reducedSystem.family)).map X.normalHull.subtype : Set E)=_
    rw [Submodule.map_span,← Set.range_comp]
    change (Submodule.span ℂ (Set.range (fun w => (X.reducedSystem.family w:E))) : Set E)=_
    simp only [X.reducedSystem_family,normalSpan]
  apply top_unique
  intro ξ _
  change ξ∈closure (Submodule.span ℂ (Set.range X.reducedSystem.family) : Set X.normalHull)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hi]
  exact ξ.property
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem reduced_weighted_scalar_state (a : UniformAlgebra) :
    inner ℂ (weightedSystem u v hv hvu).reducedSystem.root
      ((weightedSystem u v hv hvu).reducedSystem.coeff a (weightedSystem u v hv hvu).reducedSystem.root)=
      inner ℂ scalarSystem.root (scalarSystem.coeff a scalarSystem.root) := by
  rw [(weightedSystem u v hv hvu).reducedSystem_state]
  exact (scalar_weighted_state u v hv hvu a).symm

def reducedGaussianIso :
    (weightedSystem u v hv hvu).reducedSystem.generated scalarFlip ≃⋆ₐ[ℂ]
      scalarSystem.generated scalarFlip :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem reducedGaussianIso_normal :
    @Continuous _ _ ((weightedSystem u v hv hvu).reducedSystem.generatedTopology scalarFlip)
      (scalarSystem.generatedTopology scalarFlip) (reducedGaussianIso u v hv hvu) :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_normal scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip

theorem reducedGaussianIso_trace (T : (weightedSystem u v hv hvu).reducedSystem.generated scalarFlip) :
    inner ℂ scalarSystem.root ((reducedGaussianIso u v hv hvu T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      inner ℂ (weightedSystem u v hv hvu).reducedSystem.root
        ((T : (weightedSystem u v hv hvu).normalHull →L[ℂ] (weightedSystem u v hv hvu).normalHull)
          (weightedSystem u v hv hvu).reducedSystem.root) :=
  (weightedSystem u v hv hvu).reducedSystem.generatedIso_trace scalarSystem
    (fun a => (reduced_weighted_scalar_state u v hv hvu a).symm)
    (weightedSystem u v hv hvu).reducedSystem_total scalarSystem_total scalarFlip T
end FreeGroupFactorMain.WeightedFock

end

end OAI
