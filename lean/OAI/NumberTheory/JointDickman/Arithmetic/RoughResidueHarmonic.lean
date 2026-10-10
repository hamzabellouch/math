import OAI.NumberTheory.JointDickman.Probability.ResidueSummatory
import OAI.NumberTheory.JointDickman.Arithmetic.RoughHarmonicLaw

namespace OAI

/-! # Partial summation in the unit residue classes -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def roughResidueWeight {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  if (n : ZMod q) = r then roughSquarefreeWeight E z n else 0

theorem finiteCountingFunction_roughResidue {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z t : ℝ) :
    finiteCountingFunction (roughResidueWeight r E z) t = roughResidueSummatory r E z t := by
  unfold finiteCountingFunction roughResidueSummatory progressionSum roughResidueWeight
  rw [← Ioc_insert_left (Nat.zero_le ⌊t⌋₊), sum_insert left_notMem_Ioc]
  simp

theorem rough_residue_harmonic_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
            roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
            (Real.log t) / t) / q.totient| ≤
          K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := roughResidueSummatory_expansion hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound] with B hB
  intro a b ha hab hlog q _ hq r
  have ha0 : 0 < a := by linarith
  let E := Nat.primesLE (auxiliaryCutoff B)
  let F := fun t : ℝ => (t * ∑ j ∈ range (H + 1),
    roughCoefficient c E z j * (Real.log t) ^ (z - 1 - j)) / (q.totient : ℝ)
  let M := fun t : ℝ => roughDensityPolynomial c E z H (Real.log t) / (q.totient : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (M t) t :=
    (hasDerivAt_logarithmic_model c E z H (by linarith [ht.1])).div_const _
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (((roughDensityPolynomial_continuousAt c E z H (Real.log_pos ht1)).comp
      (Real.continuousAt_log (by linarith : t ≠ 0))).div_const _).continuousWithinAt
  have herr : ∀ t ∈ Set.Icc a b,
      |finiteCountingFunction (roughResidueWeight (r : ZMod q) E z) t - F t| ≤
        (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log t :=
      hlog.trans (Real.log_le_log ha0 ht.1)
    simpa only [finiteCountingFunction_roughResidue, F, E, mul_assoc, mul_left_comm, mul_comm] using
      hB t hlogt (ha.trans ht.1) q hq r
  have h := harmonic_counting_error_le (roughResidueWeight (r : ZMod q) E z) F ha0 hab hFc herr
  rw [← harmonic_model_integral F M ha0 hab hd hMc] at h
  have hint : (∫ t in a..b, M t / t) =
      (∫ t in a..b, roughDensityPolynomial c E z H (Real.log t) / t) / q.totient := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [M]
    ring
  rw [hint] at h
  exact h

end JointDickman

end OAI
