import OAI.NumberTheory.JointDickman.Arithmetic.HarmonicSummation
import OAI.NumberTheory.JointDickman.Arithmetic.RoughAuxiliaryExpansion

namespace OAI

/-!
# The harmonic rough coefficient law

Partial summation of the proved moving-cutoff expansion gives the
weighted interval law needed for the independent prime-product model.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem finiteCountingFunction_rough (E : Finset ℕ) (z t : ℝ) :
    finiteCountingFunction (roughSquarefreeWeight E z) t = roughSquarefreeSummatory E z t := by
  unfold finiteCountingFunction roughSquarefreeSummatory
  rw [← Ioc_insert_left (Nat.zero_le ⌊t⌋₊), sum_insert left_notMem_Ioc]
  simp

theorem roughDensityPolynomial_continuousAt (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (roughDensityPolynomial c E z H) L := by
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply ContinuousAt.add
  · exact continuousAt_id.rpow_const (Or.inl hL.ne')
  · exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hL.ne'))

/-- Uniformity includes arbitrarily short intervals: the error is absolute. -/
theorem rough_harmonic_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t| ≤
          K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound] with B hB
  intro a b ha hab hlog
  have ha0 : 0 < a := by linarith
  let E := Nat.primesLE (auxiliaryCutoff B)
  let F := fun t : ℝ => t * ∑ j ∈ range (H + 1), roughCoefficient c E z j * (Real.log t) ^ (z - 1 - j)
  let M := fun t : ℝ => roughDensityPolynomial c E z H (Real.log t)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (M t) t :=
    hasDerivAt_logarithmic_model c E z H (by linarith [ht.1])
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact ((roughDensityPolynomial_continuousAt c E z H (Real.log_pos ht1)).comp
      (Real.continuousAt_log (by linarith : t ≠ 0))).continuousWithinAt
  have herr : ∀ t ∈ Set.Icc a b,
      |finiteCountingFunction (roughSquarefreeWeight E z) t - F t| ≤
        (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log t :=
      hlog.trans (Real.log_le_log ha0 ht.1)
    simpa only [finiteCountingFunction_rough, F, E, mul_assoc, mul_left_comm, mul_comm] using
      hB t hlogt (ha.trans ht.1)
  have h := harmonic_counting_error_le (roughSquarefreeWeight E z) F ha0 hab hFc herr
  rw [← harmonic_model_integral F M ha0 hab hd hMc] at h
  exact h

end JointDickman

end OAI
