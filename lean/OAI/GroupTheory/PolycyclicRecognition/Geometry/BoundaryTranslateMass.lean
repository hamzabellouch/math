import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryImageMass
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarAveraging

namespace OAI

/-! # Uniform translated masses from the nilpotent leaf bound -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

/-- The preimage description of a translate agrees with its multiplication
image, including for nonmeasurable sets. -/
theorem leftTranslate_eq_mul_image
    {S : Type*} [Group S] [MeasurableSpace S] [MeasurableMul₂ S] [MeasurableInv S]
    (E : Set S) (z : S) : leftTranslate E z = (fun x => z * x) '' E := by
  ext y
  constructor
  · intro hy
    exact ⟨z⁻¹ * y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [leftTranslate, mem_ofPred_eq, inv_mul_cancel_left] using hx

/-- Pulling Haar measure back by a boundary homeomorphism measures precisely
its image sets; absolute continuity is unnecessary. -/
theorem boundary_pullback_measure_apply
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    (B : S ≃ₜ T) (μ : Measure T) (E : Set S) :
    Measure.map B.symm μ E = μ (B '' E) := by
  rw [B.symm.measurableEmbedding.map_apply, B.preimage_symm]

/-- Every source quotient translation lifts to a nilpotent element. The leaf
bound then makes all translates of a fixed Cartan image have comparable mass.
The comparison constant is uniform in both the map and the Cartan parameter. -/
theorem boundary_translated_mass_bounds
    {P G N S T D : Type*} [Group G] [Group N] [Group S]
    [TopologicalSpace S] [TopologicalSpace T]
    [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    [MeasurableMul₂ S] [MeasurableInv S]
    (act : G →* Equiv.Perm S) (ι : N →* G) (π : N →* S)
    (hπ : Function.Surjective π) (hact : ∀ n x, act (ι n) x = π n * x)
    (B : P → S ≃ₜ T) (μ : Measure T) (f : P → G → G) (height : G → ℝ)
    (d : D → G) (U : Set S) {K C : ℝ} (hK : 0 < K)
    (hmass : ∀ p x,
      ENNReal.ofReal (Real.exp (height (f p x))) ≤
        ENNReal.ofReal K * μ (B p '' (act x '' U)) ∧
      μ (B p '' (act x '' U)) ≤
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (height (f p x))))
    (hleaf : ∀ p n j, |height (f p (ι n * d j)) - height (f p (d j))| ≤ C) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ p j z,
      ENNReal.ofReal (Real.exp (height (f p (d j)))) ≤
        ENNReal.ofReal K' * (Measure.map (B p).symm μ) (leftTranslate (act (d j) '' U) z) ∧
      (Measure.map (B p).symm μ) (leftTranslate (act (d j) '' U) z) ≤
        ENNReal.ofReal K' * ENNReal.ofReal (Real.exp (height (f p (d j)))) := by
  refine ⟨K * Real.exp C, mul_pos hK (Real.exp_pos _), ?_⟩
  intro p j z
  obtain ⟨n, rfl⟩ := hπ z
  have hset : leftTranslate (act (d j) '' U) (π n) = act (ι n * d j) '' U := by
    rw [leftTranslate_eq_mul_image, image_image]
    congr 1
    funext u
    simp only [map_mul, Equiv.Perm.mul_apply, hact]
  rw [boundary_pullback_measure_apply, hset]
  exact exponential_mass_bounds_of_abs_sub_le hK.le (hleaf p n j)
    (hmass p (ι n * d j)).1 (hmass p (ι n * d j)).2

end PolycyclicRecognition

end

end OAI
