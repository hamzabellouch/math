import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanThreshold
import OAI.Geometry.Immersion.ClosedSurface.MeanSupport

namespace OAI

/-! Finite local mean families retain polynomial majorants even when the
number of summands grows. The degree depends on the local estimate, not
on the number of charts. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma MeanBounds.mono_majorants {U : Set E} {s r : ℝ} {reference : E → F}
    {L : ℕ} {T : ℝ → (E → F) → E → F} {B K B' K' : ℕ → ℝ → ℝ}
    (h : MeanBounds U s reference r L T B K)
    (hB : ∀ m C, 1 ≤ C → B m C ≤ B' m C)
    (hK : ∀ m C, 1 ≤ C → K m C ≤ K' m C) :
    MeanBounds U s reference r L T B' K' := by
  refine ⟨fun m C hC => (h.B_pos m C hC).trans (hB m C hC),
    fun m C hC => (h.K_pos m C hC).trans (hK m C hC), h.smooth, ?_, ?_⟩
  · intro η hη hη1 m C f hC hf hb hnorm
    exact (h.value η hη hη1 m C f hC hf hb hnorm).mono_const
      (mul_le_mul_of_nonneg_left (hB m C hC) hη.le)
  · intro η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd
    exact (h.difference η hη hη1 m C D f g hC hD hf hg hbf hbg hnf hng hnd).mono_const
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK m C hC) hη.le) hD)

end ClosedSurfaceR4.FiniteMean

namespace ClosedSurfaceR4.PhaseMean
open WeightedEstimates FiniteMean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma polynomialMeanProfile_sum_bound {ι : Type*} (a : Finset ι)
    (p : ℕ → ℕ) (C G : ℕ → ℝ) (m : ℕ) (A : ℝ)
    (hC : 0 ≤ C m) (hG : 1 ≤ G m) (ha : (a.card : ℝ) ≤ G m) :
    1 + ∑ _i ∈ a, polynomialMeanProfile p C G m A ≤
      polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G m A := by
  classical
  let u := G m+max 1 A
  have hu : 1 ≤ u := hG.trans
    (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A)))
  have hau : (a.card : ℝ) ≤ u := ha.trans
    (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 A)))
  have hp : 0 ≤ C m*u^(p m) := mul_nonneg hC (pow_nonneg (zero_le_one.trans hu) _)
  have hone : 1 ≤ u^(p m+1) := one_le_pow₀ hu
  simp only [polynomialMeanProfile, Finset.sum_const, nsmul_eq_mul]
  change 1+(a.card : ℝ)*(C m*u^(p m)) ≤ (1+C m)*u^(p m+1)
  calc
    _ ≤ 1+u*(C m*u^(p m)) := by linarith [mul_le_mul_of_nonneg_right hau hp]
    _ = 1+C m*u^(p m+1) := by rw [pow_succ]; ring
    _ ≤ u^(p m+1)+C m*u^(p m+1) := by linarith
    _ = _ := by ring

/-- A growing finite number of local terms costs one additional polynomial
power when its cardinality is included in the geometric profile. -/
theorem polynomial_finite_mean_family {ι : Type*} {U : Set E}
    (hU : UniqueDiffOn ℝ U) {s : ℝ} (hs : 0 ≤ s)
    {reference : E → F} {r : ℝ} {L : ℕ} (a : Finset ι)
    (T : ι → ℝ → (E → F) → E → F) (p : ℕ → ℕ) (C G : ℕ → ℝ)
    (hC : ∀ m, 0 ≤ C m) (hG : ∀ m, 1 ≤ G m)
    (ha : ∀ m, (a.card : ℝ) ≤ G m)
    (hT : ∀ i ∈ a, MeanBounds U s reference r L (T i)
      (polynomialMeanProfile p C G) (polynomialMeanProfile p C G)) :
    MeanBounds U s reference r L (fun η f x => ∑ i ∈ a, T i η f x)
      (polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G)
      (polynomialMeanProfile (fun m => p m+1) (fun m => 1+C m) G) := by
  apply (MeanBounds.finset_sum hU hs a T (fun _ => polynomialMeanProfile p C G)
    (fun _ => polynomialMeanProfile p C G) hT).mono_majorants
  · intro m A _
    exact polynomialMeanProfile_sum_bound a p C G m A (hC m) (hG m) (ha m)
  · intro m A _
    exact polynomialMeanProfile_sum_bound a p C G m A (hC m) (hG m) (ha m)

end ClosedSurfaceR4.PhaseMean

end

end OAI
