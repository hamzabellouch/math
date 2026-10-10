import OAI.Analysis.LipschitzHilbert.Estimates.DyadicErrorSource
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! The manuscript's annular error indicator and small-angle ratio,
including its logarithmic dyadic-branching source-sum bound. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def errorSourceProfile (c R d v : ℝ) : ℝ :=
  (if c*d ≤ v ∧ v ≤ R*d then 1 else 0) + (if v ≤ c*d then v/d else 0)

theorem errorSourceProfile_measurable {X : Type*} [MeasurableSpace X]
    {v : X → ℝ} (hv : Measurable v) (c R d : ℝ) :
    Measurable (fun x => errorSourceProfile c R d (v x)) := by
  have hA : MeasurableSet {x | c*d ≤ v x ∧ v x ≤ R*d} :=
    (measurableSet_le measurable_const hv).inter (measurableSet_le hv measurable_const)
  have hB : MeasurableSet {x | v x ≤ c*d} := measurableSet_le hv measurable_const
  exact (Measurable.ite hA measurable_const measurable_const).add
    (Measurable.ite hB (hv.div_const d) measurable_const)

theorem errorSourceProfile_le_dyadic (c R d v : ℝ) (K : ℕ)
    (hd : 0 ≤ d) (hR : R ≤ c*(2 : ℝ)^K) :
    errorSourceProfile c R d v ≤ dyadicErrorSource c K d v := by
  apply add_le_add _ le_rfl
  by_cases h : c*d ≤ v ∧ v ≤ R*d
  · have h' : c*d ≤ v ∧ v ≤ (2 : ℝ)^K*(c*d) := by
      refine ⟨h.1, h.2.trans ?_⟩
      have he := mul_le_mul_of_nonneg_right hR hd
      nlinarith [he]
    simp only [ite_eq_left h, ite_eq_left h', le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

theorem errorSourceProfile_nonneg (c R d v : ℝ) (hd : 0 < d) (hv : 0 ≤ v) :
    0 ≤ errorSourceProfile c R d v := by
  unfold errorSourceProfile
  split_ifs <;> positivity

theorem errorSourceProfile_bound (c R d v : ℝ) (hc : 0 < c) (hd : 0 < d) (_hv : 0 ≤ v) :
    errorSourceProfile c R d v ≤ 1+c := by
  have hfirst : (if c*d ≤ v ∧ v ≤ R*d then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have htail : (if v ≤ c*d then v/d else 0) ≤ c := by
    split_ifs with h
    · exact (div_le_iff₀ hd).mpr h
    · exact hc.le
  exact add_le_add hfirst htail

theorem sum_errorSourceProfile (N K : ℕ) (a c R v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) (hR : R ≤ c*(2 : ℝ)^K) :
    (∑ j : Fin N, errorSourceProfile c R (a*(2 : ℝ)^j.val) v) ≤ (K+1 : ℕ)+4*c := by
  exact (Finset.sum_le_sum (fun j _ => errorSourceProfile_le_dyadic c R _ v K (by positivity) hR)).trans
    (sum_dyadicErrorSource N K a c v ha hc hv)

theorem sum_errorSourceProfile_branching (N J E : ℕ) (a c C' v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) (hC : C' ≤ c*(2 : ℝ)^J) :
    (∑ j : Fin N, errorSourceProfile c (C' * ((2 : ℝ)^E)^4) (a*(2 : ℝ)^j.val) v) ≤
      (J+1 : ℕ) + 4*c + (4 / Real.log 2) * Real.log ((2 : ℝ)^E) := by
  have hp : (2 : ℝ)^(4*E) = ((2 : ℝ)^E)^4 := by rw [Nat.mul_comm, pow_mul]
  have hR : C' * ((2 : ℝ)^E)^4 ≤ c*(2 : ℝ)^(J+4*E) := by
    calc
      _ ≤ (c*(2 : ℝ)^J) * ((2 : ℝ)^E)^4 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = _ := by rw [pow_add, hp]; ring
  apply (sum_errorSourceProfile N (J+4*E) a c _ v ha hc hv hR).trans_eq
  rw [Real.log_pow]
  push_cast
  field_simp
  ring

end LipschitzHilbert

end

end OAI
