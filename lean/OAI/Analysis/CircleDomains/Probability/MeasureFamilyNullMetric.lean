import OAI.Analysis.CircleDomains.Probability.MeasureFamilyNullUnions
import OAI.Analysis.CircleDomains.Probability.MeasureFamilyExceptional

namespace OAI

/-! A zero-modulus family admits a single finite-L² extended Borel density
whose integral is infinite along every member. This provides the exceptional
metric needed to restore pointwise admissibility after an L² limit. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_infinite_integral_metric_of_modulus_zero
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (hz : measureFamilyModulus A Z σ K = 0) :
    ∃ h : Z → ℝ≥0∞, Measurable h ∧ (∫⁻ z, h z ^ 2 ∂σ) < ∞ ∧
      ∀ a, ∫⁻ z, h z ∂(K a : Measure Z) = ∞ := by
  classical
  let c (n : ℕ) : ℝ≥0∞ := n+1
  have heps (n : ℕ) : ∃ b : ℝ≥0, 0 < b ∧ (b : ℝ≥0∞) * c n ^ 2 < (2⁻¹ : ℝ≥0∞)^n := by
    apply ENNReal.exists_nnreal_pos_mul_lt
    · simp [c]
    · simp
  choose b hb hbsmall using heps
  have hex (n : ℕ) := (measureFamilyModulus_zero_iff σ K).mp hz
    (b n) (by exact_mod_cast hb n)
  choose g hgm hga hge using hex
  let f (n : ℕ) (z : Z) : ℝ≥0∞ := c n * g n z
  have hfm (n : ℕ) : Measurable (f n) := measurable_const.mul (hgm n)
  let h (z : Z) : ℝ≥0∞ := (∑' n, f n z ^ 2) ^ (1/2 : ℝ)
  have hh : Measurable h := (Measurable.tsum (fun n => (hfm n).pow_const 2)).pow_const (1/2 : ℝ)
  have hsq (z : Z) : h z ^ 2 = ∑' n, f n z ^ 2 := by
    dsimp only [h]
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hdom (n : ℕ) (z : Z) : f n z ≤ h z := by
    have he : (f n z ^ 2) ^ (1/2 : ℝ) = f n z := by
      rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun j => f j z ^ 2) n) (by norm_num)
  have henergy : (∫⁻ z, h z ^ 2 ∂σ) ≤ 2 := by
    simp_rw [hsq]
    rw [lintegral_tsum (fun n => ((hfm n).pow_const 2).aemeasurable)]
    calc
      ∑' n, ∫⁻ z, f n z ^ 2 ∂σ ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞)^n := by
        apply ENNReal.tsum_le_tsum
        intro n
        have he : (∫⁻ z, f n z ^ 2 ∂σ) = c n ^ 2 * ∫⁻ z, g n z ^ 2 ∂σ := by
          simp only [f,mul_pow]
          exact lintegral_const_mul _ ((hgm n).pow_const 2)
        rw [he]
        exact (mul_le_mul_right (hge n).le _).trans
          (by simpa only [mul_comm] using (hbsmall n).le)
      _ = 2 := ENNReal.tsum_geometric_two
  refine ⟨h,hh,henergy.trans_lt (by norm_num),?_⟩
  intro a
  by_contra hfin
  obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hfin
  have hcn : c n ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    calc
      c n = c n * 1 := (mul_one _).symm
      _ ≤ c n * ∫⁻ z, g n z ∂(K a : Measure Z) := mul_le_mul_right (hga n a) _
      _ = ∫⁻ z, f n z ∂(K a : Measure Z) := (lintegral_const_mul _ (hgm n)).symm
      _ ≤ ∫⁻ z, h z ∂(K a : Measure Z) := lintegral_mono (hdom n)
  have hn' : (n : ℝ≥0∞) ≤ c n := le_self_add
  exact (not_lt_of_ge (hn'.trans hcn)) hn

end CircleDomainRigidity

end

end OAI
