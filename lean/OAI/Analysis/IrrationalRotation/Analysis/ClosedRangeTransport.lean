import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

noncomputable section
open scoped NNReal

namespace InvariantRotation.ClosedRangeTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (p : Submodule 𝕜 E) [CompleteSpace p]
variable (f : p →L[𝕜] E) (hinj : Function.Injective f)
variable (hclosed : IsClosed (Set.range f))

omit [CompleteSpace p] in

private theorem range_hasOrthogonalProjection (hclosed : IsClosed (Set.range f)) :
    f.range.HasOrthogonalProjection := by
  let : IsClosed (f.range : Set E) := hclosed
  infer_instance

def partialInverse : E →L[𝕜] E := by
  letI := range_hasOrthogonalProjection p f hclosed
  exact p.subtypeL.comp
    ((f.equivRange hinj hclosed).symm.toContinuousLinearMap.comp
      f.range.orthogonalProjectionOnto)

def forward : E →L[𝕜] E :=
  f.comp p.orthogonalProjectionOnto

@[simp]
theorem partialInverse_apply_image (x : p) :
    partialInverse p f hinj hclosed (f x) = (x : E) := by
  let := range_hasOrthogonalProjection p f hclosed
  change (((f.equivRange hinj hclosed).symm
    (f.range.orthogonalProjectionOnto (f x)) : p) : E) = x
  have hproj : f.range.orthogonalProjectionOnto (f x) = ⟨f x, f.mem_range_self x⟩ :=
    f.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f x, f.mem_range_self x⟩
  rw [hproj, f.equivRange_symm_apply hinj hclosed x]

theorem partialInverse_comp_forward :
    (partialInverse p f hinj hclosed).comp (forward p f) = p.starProjection := by
  ext x
  exact partialInverse_apply_image p f hinj hclosed (p.orthogonalProjectionOnto x)

theorem forward_comp_partialInverse :
    letI := range_hasOrthogonalProjection p f hclosed
    (forward p f).comp (partialInverse p f hinj hclosed) = f.range.starProjection := by
  let := range_hasOrthogonalProjection p f hclosed
  ext x
  change f (p.orthogonalProjectionOnto
    (((f.equivRange hinj hclosed).symm (f.range.orthogonalProjectionOnto x) : p) : E)) = _
  rw [p.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h := (f.equivRange hinj hclosed).apply_symm_apply
    (f.range.orthogonalProjectionOnto x)
  exact congrArg (fun z : f.range => (z : E)) h

theorem functional_eq_of_cyclic (τ : (E →L[𝕜] E) → 𝕜)
    (hτ : τ ((partialInverse p f hinj hclosed).comp (forward p f)) =
      τ ((forward p f).comp (partialInverse p f hinj hclosed))) :
    letI := range_hasOrthogonalProjection p f hclosed
    τ p.starProjection = τ f.range.starProjection := by
  let := range_hasOrthogonalProjection p f hclosed
  rw [partialInverse_comp_forward, forward_comp_partialInverse] at hτ
  exact hτ

omit [CompleteSpace E] in

theorem range_forward : (forward p f).range = f.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨p.orthogonalProjectionOnto x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change f (p.orthogonalProjectionOnto x) = f x
    rw [p.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem partialInverse_mem (x : E) : partialInverse p f hinj hclosed x ∈ p := by
  let := range_hasOrthogonalProjection p f hclosed
  exact ((f.equivRange hinj hclosed).symm (f.range.orthogonalProjectionOnto x)).property

theorem projection_comp_partialInverse :
    p.starProjection.comp (partialInverse p f hinj hclosed) =
      partialInverse p f hinj hclosed := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (partialInverse_mem p f hinj hclosed x)

section Algebra

variable {R : Type*} [Monoid R]

theorem commute_partialInverse {a b p q w : R}
    (hba : b * a = p) (hab : a * b = q) (hpb : p * b = b)
    (hwa : Commute w a) (hwp : Commute w p) (hwq : Commute w q) :
    Commute w b := by
  have hbq : b * q = b := by rw [← hab, ← mul_assoc, hba, hpb]
  change w * b = b * w
  calc
    w * b = w * (p * b) := by rw [hpb]
    _ = (w * p) * b := (mul_assoc _ _ _).symm
    _ = (p * w) * b := by rw [hwp.eq]
    _ = ((b * a) * w) * b := by rw [hba]
    _ = (b * (a * w)) * b := by rw [mul_assoc b a w]
    _ = (b * (w * a)) * b := by rw [hwa.eq]
    _ = (b * w) * (a * b) := by simp only [mul_assoc]
    _ = (b * w) * q := by rw [hab]
    _ = b * (w * q) := mul_assoc _ _ _
    _ = b * (q * w) := by rw [hwq.eq]
    _ = (b * q) * w := (mul_assoc _ _ _).symm
    _ = b * w := by rw [hbq]

end Algebra

section VonNeumann

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem range_projection_mem (M : VonNeumannAlgebra F) (a : F →L[ℂ] F)
    (ha : a ∈ M) (hc : IsClosed (Set.range a)) :
    letI : IsClosed (a.range : Set F) := hc
    a.range.starProjection ∈ M := by
  let : IsClosed (a.range : Set F) := hc
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro w hw
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  rintro y ⟨x, rfl⟩
  refine ⟨w x, ?_⟩
  exact congrArg (fun v : F →L[ℂ] F => v x)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) a ha)

theorem partialInverse_mem_algebra
    (M : VonNeumannAlgebra F) (p : Submodule ℂ F) [CompleteSpace p]
    (f : p →L[ℂ] F) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M) (hf : forward p f ∈ M) :
    partialInverse p f hinj hc ∈ M := by
  let := range_hasOrthogonalProjection p f hc
  have hfc : IsClosed (Set.range (forward p f)) := by
    change IsClosed ((forward p f).range : Set F)
    rw [range_forward]
    exact hc
  have hr : f.range.starProjection ∈ M := by
    have hr' := range_projection_mem M (forward p f) hf hfc
    simpa only [range_forward] using hr'
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro w hw
  exact (commute_partialInverse
    (a := forward p f) (b := partialInverse p f hinj hc)
    (p := p.starProjection) (q := f.range.starProjection)
    (partialInverse_comp_forward p f hinj hc)
    (forward_comp_partialInverse p f hinj hc)
    (projection_comp_partialInverse p f hinj hc)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hf).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hp).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hr).symm).eq

theorem trace_range_eq
    (M : VonNeumannAlgebra F) (p : Submodule ℂ F) [CompleteSpace p]
    (f : p →L[ℂ] F) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M) (hf : forward p f ∈ M)
    (τ : (F →L[ℂ] F) → ℂ)
    (hτ : ∀ a ∈ M, ∀ b ∈ M, τ (a * b) = τ (b * a)) :
    letI := range_hasOrthogonalProjection p f hc
    τ p.starProjection = τ f.range.starProjection := by
  apply functional_eq_of_cyclic p f hinj hc τ
  exact hτ _ (partialInverse_mem_algebra M p f hinj hc hp hf) _ hf

end VonNeumann

omit [CompleteSpace E] in

theorem injective_closedRange_of_bound (K : ℝ≥0)
    (hbound : ∀ x : p, ‖x‖ ≤ K * ‖f x‖) :
    Function.Injective f ∧ IsClosed (Set.range f) := by
  have hanti := f.antilipschitz_of_bound hbound
  exact ⟨hanti.injective, hanti.isClosed_range f.uniformContinuous⟩

end InvariantRotation.ClosedRangeTransport

end

end OAI
