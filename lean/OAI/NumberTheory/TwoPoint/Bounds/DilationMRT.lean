import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeShortSums
import OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums

namespace OAI

/-! MRT at the exact quotient-window lengths needed by a fixed dilation.
The published input is unchanged; only finite reindexing is performed. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma zero_origin_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (Y : ℕ) :
    (∑ v ∈ range Y, F v) ≤ F 0 + ∑ v ∈ range Y, F (v + 1) := by
  have h1 := sum_range_succ F Y
  have h2 := sum_range_succ' F Y
  linarith [hF Y]

lemma shortWindowSum_norm_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) (α : ℝ) : ‖shortWindowSum f D α v‖ ≤ D := by
  apply (norm_shortWindowSum_le f D v α).trans
  calc
    _ ≤ ∑ _m ∈ range D, (1 : ℝ) := sum_le_sum (fun m _ => hf _ (by omega))
    _ = _ := by simp

theorem MRTShortExponentialInput.modified_zero_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
        (∑ v ∈ range Y, ‖shortWindowSum b D α v‖) ≤
          C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
  obtain ⟨C, hC, hbase⟩ := hMRT.modified_fixed_windows hfnp hf
  refine ⟨C + 1, by positivity, ?_⟩
  intro P D hD ε hε
  filter_upwards [hbase P D hD ε hε,
    eventually_ge_atTop (Nat.ceil (1 / ε))] with Y hY hYlarge
  intro b hb hbb heq α
  have hprog : progressionSequence b 1 (0 : ZMod 1) = b := by
    funext n
    simp only [progressionSequence, Subsingleton.elim (n : ZMod 1) 0, ite_true]
  have hw := hY b hb hbb heq 1 (0 : ZMod 1) (α : AddCircle (1 : ℝ))
  simp only [hprog, forwardWindowPolynomial_at_real] at hw
  have hYs : 1 / ε ≤ (Y : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hYlarge)
  have hYe : 1 ≤ (Y : ℝ) * ε := (div_le_iff₀ hε).mp hYs
  have hE : 0 ≤ Real.log (Real.log (D : ℝ)) / Real.log D :=
    loglog_div_log_nonneg D hD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hpiece : (D : ℝ) ≤ (D : ℝ) * Y *
      (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
    have hy : 1 ≤ (Y : ℝ) * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg Y) hE]
    nlinarith
  calc
    _ ≤ ‖shortWindowSum b D α 0‖ + ∑ v ∈ range Y, ‖shortWindowSum b D α (v + 1)‖ :=
      zero_origin_sum_le _ (fun _ => norm_nonneg _) Y
    _ ≤ D + C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) :=
      add_le_add (shortWindowSum_norm_bound b hbb D 0 α) hw
    _ ≤ _ := by nlinarith only [hpiece]

/-- Each quotient length is fixed before taking the long average. Thus
all shorter MRT estimates hold on a common tail, uniformly in the modified
function and in frequency. -/
theorem MRTShortExponentialInput.modified_quotient_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (q D K : ℕ), 0 < q →
      (∀ a ∈ Icc 1 K, 10 ≤ D / a + 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ a ∈ Icc 1 K, ∀ α : ℝ,
        (∑ m ∈ range (Y / a + 1),
          ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) α m‖) ≤
          C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) *
            (Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) + ε) := by
  obtain ⟨C, hC, hw⟩ := hMRT.modified_zero_windows hfnp hf
  refine ⟨C, hC, ?_⟩
  intro P q D K hq hlength ε hε
  have hall : ∀ᶠ Y : ℕ in atTop, ∀ a ∈ Icc 1 K,
      ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) α m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) *
          (Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) + ε) := by
    apply (eventually_all_finset (Icc 1 K)).mpr
    intro a ha
    have hap : 0 < a := (mem_Icc.mp ha).1
    have ht : Tendsto (fun Y : ℕ => Y / a + 1) atTop atTop :=
      (tendsto_add_atTop_nat 1).comp (tendsto_nat_div_atTop a hap)
    filter_upwards [ht.eventually (hw (P ∪ q.primeFactors) (D / a + 1)
      (hlength a ha) ε hε)] with Y hY
    intro b hb hbb heq α
    refine hY (coprimeRestriction q b) (coprimeRestriction_multiplicative q hb)
      (coprimeRestriction_oneBounded q hbb) ?_ α
    intro p hp hnot
    rw [coprimeRestriction_prime q hq b hp (fun h => hnot (mem_union_right _ h))]
    exact heq p hp (fun h => hnot (mem_union_left _ h))
  filter_upwards [hall] with Y hY
  intro b hb hbb heq a ha α
  exact hY a ha b hb hbb heq α

end TwoPointCorrelations

end OAI
