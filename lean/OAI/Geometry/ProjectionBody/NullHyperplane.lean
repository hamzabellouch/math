import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

noncomputable section
open Set MeasureTheory

namespace ProjectionCounterexample

/-- Every level set of a nonzero real linear functional has zero ambient volume. -/
theorem volume_linear_level_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
    [Measure.IsAddHaarMeasure (volume : Measure V)]
    (f : V →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    volume {x : V | f x = c} = 0 := by
  let H : AffineSubspace ℝ V := (affineSpan ℝ ({c} : Set ℝ)).comap f.toAffineMap
  have hmem (x : V) : x ∈ H ↔ f x = c := by
    simp [H]
  have hproper : H ≠ ⊤ := by
    intro htop
    have heq (x : V) : f x = c := (hmem x).mp (by rw [htop]; trivial)
    have hc : c = 0 := by simpa using (heq 0).symm
    apply hf
    ext x
    simpa [hc] using heq x
  have hset : (H : Set V) = {x : V | f x = c} := Set.ext hmem
  rw [← hset]
  exact Measure.addHaar_affineSubspace volume H hproper

end ProjectionCounterexample

end

end OAI
