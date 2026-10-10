import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import OAI.Analysis.FactorGeneration.ProjectionLimits

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The orthogonal projection onto an operator's kernel belongs to its
von Neumann algebra. This uses the actual double-commutant definition. -/
theorem kernelProjection_mem (x : M.toStarSubalgebra) :
    (x.val.ker).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro y hy
  rw [Submodule.range_starProjection]
  intro ξ hξ
  change x.val (y ξ)=0
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) hc
  change x.val (y ξ)=y (x.val ξ) at he
  rw [he,show x.val ξ=0 from hξ,map_zero]

def kernelProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨⟨x.val.ker.starProjection,kernelProjection_mem x⟩,by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isSelfAdjoint.star_eq⟩

theorem kernelProjection_apply (x : M.toStarSubalgebra) (ξ : H) :
    ((kernelProjection x).val : H →L[ℂ] H) ξ = x.val.ker.starProjection ξ := rfl

theorem mul_kernelProjection (x : M.toStarSubalgebra) : x*(kernelProjection x).val=0 := by
  apply Subtype.ext
  ext ξ
  exact Submodule.starProjection_apply_mem x.val.ker ξ

theorem kernelProjection_fixes (x : M.toStarSubalgebra) (ξ : H) (hξ : x.val ξ=0) :
    ((kernelProjection x).val : H →L[ℂ] H) ξ=ξ :=
  Submodule.starProjection_eq_self_iff.mpr hξ

/-- This is the largest algebra projection annihilated on the left by x. -/
theorem le_kernelProjection_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    q ≤ kernelProjection x ↔ x*q.val=0 := by
  constructor
  · intro h
    calc x*q.val = x*((kernelProjection x).val*q.val) := by rw [h]
      _ = 0 := by rw [← mul_assoc,mul_kernelProjection,zero_mul]
  · intro h
    apply Subtype.ext
    ext ξ
    apply kernelProjection_fixes
    have he := congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h
    exact he

/-- The projection onto the closed range of x, expressed via ker(x*). -/
def rangeProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨1-(kernelProjection (star x)).val,(kernelProjection (star x)).property.one_sub⟩

theorem rangeProjection_mul (x : M.toStarSubalgebra) : (rangeProjection x).val*x=x := by
  have h := congrArg star (mul_kernelProjection (star x))
  simp only [star_mul,(kernelProjection (star x)).property.isSelfAdjoint.star_eq,
    star_star,star_zero] at h
  change (1-(kernelProjection (star x)).val)*x=x
  rw [sub_mul,one_mul,h,sub_zero]

/-- Minimality retains any prescribed corner supporting x. -/
theorem rangeProjection_le_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    rangeProjection x ≤ q ↔ q.val*x=x := by
  constructor
  · intro h
    calc q.val*x = q.val*((rangeProjection x).val*x) := by rw [rangeProjection_mul]
      _ = x := by rw [← mul_assoc,h,rangeProjection_mul]
  · intro h
    let r : AlgebraProjection M := ⟨1-q.val,q.property.one_sub⟩
    have hz : star x*r.val=0 := by
      have hh := congrArg star h
      simp only [star_mul,q.property.isSelfAdjoint.star_eq] at hh
      change star x*(1-q.val)=0
      rw [mul_sub,mul_one,hh,sub_self]
    have hr := (le_kernelProjection_iff (star x) r).mpr hz
    have hs := projection_mul_of_le hr
    change (1-q.val)*(kernelProjection (star x)).val=1-q.val at hs
    change q.val*(1-(kernelProjection (star x)).val)=1-(kernelProjection (star x)).val
    simp only [sub_mul,one_mul] at hs
    simp only [mul_sub,mul_one]
    apply (sub_eq_sub_iff_add_eq_add).mpr
    have hh := (sub_eq_sub_iff_add_eq_add).mp hs
    simpa only [add_comm,add_left_comm,add_assoc] using hh

/-- Kernel projections fix the range of every operator they annihilate. -/
theorem kernelProjection_mul_of_mul_eq_zero (x y : M.toStarSubalgebra) (h : x*y=0) :
    (kernelProjection x).val*y=y := by
  apply Subtype.ext
  ext ξ
  apply kernelProjection_fixes
  exact congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h

/-- For self-adjoint x, its range projection kills every y killed by x. -/
theorem rangeProjection_mul_eq_zero (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (h : x*y=0) : (rangeProjection x).val*y=0 := by
  change (1-(kernelProjection (star x)).val)*y=0
  rw [hx.star_eq,sub_mul,one_mul,kernelProjection_mul_of_mul_eq_zero x y h,sub_self]

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance positiveSupportCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance positiveSupportOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance positiveSupportPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance positiveSupportLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance positiveSupportStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def positiveSupport (x : M.toStarSubalgebra) : AlgebraProjection M := rangeProjection x⁺

theorem positiveSupport_mul_pos (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁺=x⁺ := rangeProjection_mul _

theorem positiveSupport_mul_neg (x : M.toStarSubalgebra) :
    (positiveSupport x).val*x⁻=0 :=
  rangeProjection_mul_eq_zero x⁺ x⁻ (CFC.posPart_nonneg x).isSelfAdjoint
    (CFC.posPart_mul_negPart x)

theorem positiveSupport_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x=x⁺ := by
  calc (positiveSupport x).val*x = (positiveSupport x).val*(x⁺-x⁻) :=
         congrArg (fun z => (positiveSupport x).val*z) (CFC.posPart_sub_negPart x hx).symm
    _ = x⁺ := by rw [mul_sub,positiveSupport_mul_pos,positiveSupport_mul_neg,sub_zero]

theorem mul_positiveSupport (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    x*(positiveSupport x).val=x⁺ := by
  have h := congrArg star (positiveSupport_mul x hx)
  simpa only [star_mul,hx.star_eq,(positiveSupport x).property.isSelfAdjoint.star_eq,
    (CFC.posPart_nonneg x).isSelfAdjoint.star_eq] using h

theorem positiveSupport_commutes (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    Commute (positiveSupport x).val x := by
  show (positiveSupport x).val*x=x*(positiveSupport x).val
  rw [positiveSupport_mul x hx,mul_positiveSupport x hx]

theorem positiveSupport_compression (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (positiveSupport x).val*x*(positiveSupport x).val=x⁺ := by
  rw [mul_assoc,mul_positiveSupport x hx,positiveSupport_mul_pos]

theorem positiveSupport_complement_mul (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x = -x⁻ := by
  rw [sub_mul,one_mul,positiveSupport_mul x hx]
  calc x-x⁺ = (x⁺-x⁻)-x⁺ := congrArg (fun z => z-x⁺) (CFC.posPart_sub_negPart x hx).symm
    _ = -x⁻ := by abel

theorem positiveSupport_complement_compression (x : M.toStarSubalgebra)
    (hx : IsSelfAdjoint x) :
    (1-(positiveSupport x).val)*x*(1-(positiveSupport x).val) = -x⁻ := by
  have hright : x⁻*(positiveSupport x).val=0 := by
    have h := congrArg star (positiveSupport_mul_neg x)
    simpa only [star_mul,(positiveSupport x).property.isSelfAdjoint.star_eq,
      (CFC.negPart_nonneg x).isSelfAdjoint.star_eq,star_zero] using h
  rw [positiveSupport_complement_mul x hx,mul_sub,mul_one,neg_mul,hright,neg_zero,sub_zero]

def spectralCut (x : M.toStarSubalgebra) (t : ℝ) : AlgebraProjection M :=
  positiveSupport (x-(t : ℂ) • (1 : M.toStarSubalgebra))

theorem spectralShift_selfAdjoint (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    IsSelfAdjoint (x-(t : ℂ) • (1 : M.toStarSubalgebra)) := by
  apply hx.sub
  change star ((t : ℂ) • (1 : M.toStarSubalgebra)) = _
  simp only [star_smul,star_one,Complex.star_def,Complex.conj_ofReal]

/-- The high spectral corner has nonnegative shifted compression. -/
theorem spectralCut_lower (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    0 ≤ (spectralCut x t).val*(x-(t : ℂ) • (1 : M.toStarSubalgebra))*(spectralCut x t).val := by
  rw [spectralCut,positiveSupport_compression _ (spectralShift_selfAdjoint x hx t)]
  exact CFC.posPart_nonneg _

/-- Its complement has nonpositive shifted compression. -/
theorem spectralCut_upper_complement (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℝ) :
    (1-(spectralCut x t).val)*(x-(t : ℂ) • (1 : M.toStarSubalgebra))*
      (1-(spectralCut x t).val) ≤ 0 := by
  rw [spectralCut,positiveSupport_complement_compression _ (spectralShift_selfAdjoint x hx t)]
  exact neg_nonpos.mpr (CFC.negPart_nonneg _)

end

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_isometric_range_factor (a x : H →L[ℂ] H)
    (hnorm : ∀ ξ, ‖x ξ‖ = ‖a ξ‖) :
    ∃ v : H →L[ℂ] H, v * a = x ∧
      star v * v = a.range.topologicalClosure.starProjection ∧
      v * a.range.topologicalClosure.starProjection = v := by
  let K := a.range.topologicalClosure
  let e : a.range →L[ℂ] K :=
    ⟨Submodule.inclusion a.range.le_topologicalClosure,
      continuous_inclusion a.range.le_topologicalClosure⟩
  have hd : DenseRange e :=
    (denseRange_inclusion_iff a.range.le_topologicalClosure).mpr (by rfl)
  have he : IsUniformInducing e :=
    (show Isometry e from fun _ _ => rfl).isUniformInducing
  let f : a.range →L[ℂ] H := x.toLinearMap.compLeftInverse a.toLinearMap
  have hf (ξ : H) : f ⟨a ξ, ⟨ξ, rfl⟩⟩ = x ξ :=
    LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨1, by simp [hnorm]⟩ _ _ rfl
  let g : K →L[ℂ] H := f.extend e
  have hg (ξ : H) : g (e ⟨a ξ, ⟨ξ, rfl⟩⟩) = x ξ :=
    (ContinuousLinearMap.extend_eq f hd he _).trans (hf ξ)
  have hgNorm : ∀ ξ : K, ‖g ξ‖ = ‖ξ‖ := by
    intro ξ
    refine hd.induction_on (p := fun ζ : K => ‖g ζ‖=‖ζ‖) ξ
      (isClosed_eq (g.continuous.norm) continuous_norm) ?_
    rintro ⟨_, ζ, rfl⟩
    exact (congrArg norm (hg ζ)).trans (hnorm ζ)
  let v : H →L[ℂ] H := g.comp K.orthogonalProjectionOnto
  have hva : v * a = x := by
    ext ξ
    change g (K.orthogonalProjectionOnto (a ξ)) = x ξ
    have hh : K.orthogonalProjectionOnto (a ξ) = e ⟨a ξ, ⟨ξ,rfl⟩⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr
        (a.range.le_topologicalClosure ⟨ξ,rfl⟩)
    rw [hh,hg]
  have hvs : v * K.starProjection = v := by
    ext ξ
    change g (K.orthogonalProjectionOnto (K.starProjection ξ)) =
      g (K.orthogonalProjectionOnto ξ)
    congr 1
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self _
  refine ⟨v,hva,?_,hvs⟩
  have heq : (star v * v).toLinearMap = K.starProjection.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro ξ
    change inner ℂ ((star v) (v ξ)) ξ = inner ℂ (K.starProjection ξ) ξ
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K]
    change (‖g (K.orthogonalProjectionOnto ξ)‖ : ℂ)^2 = _
    rw [hgNorm]
    have hh := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (𝕜 := ℂ) (K.orthogonalProjectionOnto ξ) ξ
    rw [inner_self_eq_norm_sq_to_K] at hh
    rw [Submodule.starProjection_apply]
    exact hh
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) heq

end

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem rangeProjection_eq_closure_projection (x : M.toStarSubalgebra) :
    ((rangeProjection x).val : H →L[ℂ] H) = x.val.range.topologicalClosure.starProjection := by
  have he : (star x.val).kerᗮ = x.val.range.topologicalClosure := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
      using (star x.val).orthogonal_ker
  change 1-(star x.val).ker.starProjection = _
  have hh := (Submodule.starProjection_orthogonal (star x.val).ker).symm
  simp only [he] at hh
  exact hh

theorem mul_closure_range_projection_eq_zero (a b : H →L[ℂ] H) (h : b*a=0) :
    b*a.range.topologicalClosure.starProjection=0 := by
  have hr : a.range ≤ b.ker := by
    rintro _ ⟨ξ,rfl⟩
    exact congrArg (fun t : H →L[ℂ] H => t ξ) h
  have hc : a.range.topologicalClosure ≤ b.ker :=
    a.range.topologicalClosure_minimal hr b.isClosed_ker
  ext ξ
  exact hc (Submodule.starProjection_apply_mem _ ξ)

theorem exists_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v * CFC.sqrt (star x*x) = x ∧
      star v*v = (rangeProjection (CFC.sqrt (star x*x))).val ∧
      v*(rangeProjection (CFC.sqrt (star x*x))).val=v := by
  let a := CFC.sqrt (star x*x)
  have ha : IsSelfAdjoint a := (CFC.sqrt_nonneg _).isSelfAdjoint
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have hn (ξ : H) : ‖x.val ξ‖=‖a.val ξ‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have he := congrArg (fun t : M.toStarSubalgebra =>
      inner ℂ ξ ((t : H →L[ℂ] H) ξ)) haa
    have has : star a.val=a.val := congrArg Subtype.val ha.star_eq
    have hs (z : H →L[ℂ] H) : inner ℂ ξ ((star z*z) ξ) = (‖z ξ‖ : ℂ)^2 := by
      rw [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
      rfl
    have he' : (‖a.val ξ‖ : ℂ)^2 = (‖x.val ξ‖ : ℂ)^2 := by
      calc _ = inner ℂ ξ ((star a.val*a.val) ξ) := (hs _).symm
           _ = inner ℂ ξ ((star x.val*x.val) ξ) := by rw [has]; exact he
           _ = _ := hs _
    exact_mod_cast he'.symm
  obtain ⟨v,hva,hvi,hvs⟩ := exists_isometric_range_factor a.val x.val hn
  let s := rangeProjection a
  have hs : (s.val : H →L[ℂ] H)=a.val.range.topologicalClosure.starProjection :=
    rangeProjection_eq_closure_projection a
  rw [← hs] at hvi hvs
  have hmem : v ∈ M := by
    rw [← M.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro y hy
    have hya := (VonNeumannAlgebra.mem_commutant_iff.mp hy) a.val a.property
    have hyx := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
    have hys := (VonNeumannAlgebra.mem_commutant_iff.mp hy) s.val.val s.val.property
    have hz : (y*v-v*y)*a.val=0 := by
      rw [sub_mul,mul_assoc,hva,mul_assoc,← hya,← mul_assoc,hva,hyx,sub_self]
    have hd := mul_closure_range_projection_eq_zero a.val (y*v-v*y) hz
    rw [← hs,sub_mul,mul_assoc,hvs,mul_assoc,← hys,← mul_assoc,hvs] at hd
    exact sub_eq_zero.mp hd
  exact ⟨⟨v,hmem⟩,Subtype.ext hva,Subtype.ext hvi,Subtype.ext hvs⟩

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarSupportsCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarSupportsOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarSupportsStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem sqrt_rangeProjection (x : M.toStarSubalgebra) :
    rangeProjection (CFC.sqrt (star x*x)) = rangeProjection (star x) := by
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have he : star a.val*a.val=star x.val*x.val := by
    change ((star a*a : M.toStarSubalgebra) : H →L[ℂ] H)=_
    rw [ha,CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)]
    rfl
  have hk (z : H →L[ℂ] H) : (star z*z).ker=z.ker := by
    exact z.ker_adjoint_comp_self
  have hker : a.val.ker=x.val.ker := by rw [← hk a.val,he,hk]
  apply Subtype.ext
  apply Subtype.ext
  change 1-(star a.val).ker.starProjection=1-(star (star x.val)).ker.starProjection
  have has : star a.val=a.val := congrArg Subtype.val ha
  simp only [has,star_star,hker]

theorem exists_polar_with_supports (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      v*CFC.sqrt (star x*x)=x ∧
      star v*v=(rangeProjection (star x)).val ∧
      v*star v=(rangeProjection x).val := by
  obtain ⟨v,hvx,hvi,hvs⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let s := rangeProjection a
  have ht : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = (v*(star v*v))*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hvi,hvs]
    · exact IsSelfAdjoint.mul_star_self v
  let t : AlgebraProjection M := ⟨v*star v,ht⟩
  have hxt : rangeProjection x ≤ t := by
    apply (rangeProjection_le_iff x t).mpr
    change (v*star v)*x=x
    calc _ = (v*star v)*(v*a) := by rw [hvx]
         _ = (v*(star v*v))*a := by simp only [mul_assoc]
         _ = x := by rw [hvi,hvs,hvx]
  have htx : t ≤ rangeProjection x := by
    let r := rangeProjection x
    have hz : (r.val*v-v)*a=0 := by
      rw [sub_mul,mul_assoc,hvx,rangeProjection_mul,sub_self]
    have he := mul_closure_range_projection_eq_zero a.val
      ((r.val*v-v : M.toStarSubalgebra) : H →L[ℂ] H)
      (congrArg Subtype.val hz)
    rw [← rangeProjection_eq_closure_projection a] at he
    have he' : (r.val*v-v)*s.val=0 := Subtype.ext he
    rw [sub_mul,mul_assoc,hvs] at he'
    change r.val*(v*star v)=v*star v
    rw [← mul_assoc,sub_eq_zero.mp he']
  refine ⟨v,hvx,?_,?_⟩
  · simpa only [sqrt_rangeProjection] using hvi
  · exact congrArg (fun z : AlgebraProjection M => z.val) (le_antisymm htx hxt)

end Generator.Tracial

end

end OAI
