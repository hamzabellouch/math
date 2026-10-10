import OAI.Probability.InvariantIsing.Fields.SpinGroupSlice
import OAI.Probability.InvariantIsing.Fields.SpinFactorization
import OAI.Probability.IsingPerceptron.MonomialGgAtMinimum

namespace OAI

/-! The actual constrained-block terminal payoff. Its prior mass is not
renormalized; the Lipschitz and growth estimates include that fixed mass. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma restrictedSpinLog_le_add {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H K : Spin N → ℝ) (c : ℝ) (h : ∀ σ ∈ S, H σ ≤ K σ + c) :
    restrictedSpinLog S H ≤ restrictedSpinLog S K + c := by
  rw [← restrictedSpinLog_add_const S hS K c]
  exact restrictedSpinLog_mono hS (Finset.Subset.refl _) h

lemma abs_restrictedSpinLog_sub_le {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (H K : Spin N → ℝ) (c : ℝ) (h : ∀ σ ∈ S, |H σ - K σ| ≤ c) :
    |restrictedSpinLog S H - restrictedSpinLog S K| ≤ c := by
  have h₁ := restrictedSpinLog_le_add S hS H K c (fun σ hσ => by
    have hh := (abs_le.mp (h σ hσ)).2
    linarith)
  have h₂ := restrictedSpinLog_le_add S hS K H c (fun σ hσ => by
    have hh := (abs_le.mp (h σ hσ)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def restrictedFieldTerminal {N : ℕ} (S : Finset (Spin N)) (z : Fin N → ℝ) : ℝ :=
  restrictedSpinLog S (fieldEnergy z)

lemma restrictedFieldTerminal_univ {N : ℕ} (z : Fin N → ℝ) :
    restrictedFieldTerminal Finset.univ z = ∑ i, Real.log (Real.cosh (z i)) := by
  rw [restrictedFieldTerminal, restrictedSpinLog_univ, logPartition_fieldEnergy]

lemma restrictedFieldTerminal_zero {N : ℕ} (S : Finset (Spin N)) :
    restrictedFieldTerminal S 0 = Real.log S.card - N * Real.log 2 := by
  simp [restrictedFieldTerminal, restrictedSpinLog, fieldEnergy]

lemma restrictedFieldTerminal_le_univ {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z : Fin N → ℝ) : restrictedFieldTerminal S z ≤ ∑ i, Real.log (Real.cosh (z i)) := by
  rw [restrictedFieldTerminal, ← logPartition_fieldEnergy]
  exact restrictedSpinLog_le_full S hS _

lemma restrictedFieldTerminal_difference {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z y : Fin N → ℝ) :
    |restrictedFieldTerminal S z - restrictedFieldTerminal S y| ≤ ∑ i, |z i - y i| :=
  abs_restrictedSpinLog_sub_le S hS _ _ _ (fun σ _ => abs_fieldEnergy_sub_le z y σ)

lemma restrictedFieldTerminal_norm_difference {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    (z y : Fin N → ℝ) :
    |restrictedFieldTerminal S z - restrictedFieldTerminal S y| ≤ N * ‖z - y‖ := by
  apply (restrictedFieldTerminal_difference S hS z y).trans
  calc
    _ ≤ ∑ _i : Fin N, ‖z - y‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - y) i)
    _ = _ := by simp

lemma continuous_restrictedFieldTerminal {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Continuous (restrictedFieldTerminal S) := by
  apply LipschitzWith.continuous (K := (N : ℝ≥0))
  apply LipschitzWith.of_dist_le_mul
  intro z y
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_natCast] using
    restrictedFieldTerminal_norm_difference S hS z y

lemma restrictedFieldTerminal_linearGrowth {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    HasLinearGrowth (restrictedFieldTerminal S) := by
  refine ⟨|restrictedFieldTerminal S 0|, N, abs_nonneg _, Nat.cast_nonneg _, fun z => ?_⟩
  have hb := restrictedFieldTerminal_norm_difference S hS z 0
  simp only [sub_zero] at hb
  have hh := abs_add_le (restrictedFieldTerminal S z - restrictedFieldTerminal S 0)
    (restrictedFieldTerminal S 0)
  rw [sub_add_cancel] at hh
  linarith

lemma restrictedFieldTerminal_group_bias {N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a)
    (b : A → ℝ) (z : Fin N → ℝ) :
    restrictedFieldTerminal (spinGroupSlice group k) (z + fun i => b (group i)) =
      restrictedFieldTerminal (spinGroupSlice group k) z + spinGroupFieldConstant group k b := by
  have he : fieldEnergy (z + fun i => b (group i)) =
      fun σ => fieldEnergy z σ + fieldEnergy (fun i => b (group i)) σ := by
    funext σ
    simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [restrictedFieldTerminal, he, restrictedSpinLog_group_field group k hk]
  rfl

end InvariantIsing

end

end OAI
