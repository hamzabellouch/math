import OAI.Probability.MatroidProphet.ProductRestriction
import OAI.Probability.MatroidProphet.Residual.Constants

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

lemma bitsExpectation_contains (q : α → ℝ) (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = ∏ e ∈ R, q e := by
  induction V using Finset.induction_on generalizing R with
  | empty =>
    have h : R = ∅ := Finset.subset_empty.mp hR
    subst R
    simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    by_cases heR : e ∈ R
    · have hRV : R.erase e ⊆ V := by
        intro x hx
        have hm := hR (mem_of_mem_erase hx)
        rcases mem_insert.mp hm with rfl | hm
        · exact (notMem_erase _ _ hx).elim
        · exact hm
      have hzero : bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) = 0 := by
        conv_rhs => rw [← bitsExpectation_const q V 0]
        apply bitsExpectation_congr
        intro S hS
        have hn : ¬ R ⊆ S := fun hh => he (hS (hh heR))
        simp [hn]
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R.erase e ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R.erase e ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
          · intro h x hx
            by_cases hxe : x = e
            · simp [hxe]
            · exact mem_insert_of_mem (h (mem_erase.mpr ⟨hxe, hx⟩))
        simp only [hiff]
      rw [hzero, hyes, ih _ hRV]
      simpa using (mul_prod_erase R q heR)
    · have hRV : R ⊆ V := by
        intro x hx
        exact (mem_insert.mp (hR hx)).resolve_left (fun h => heR (h ▸ hx))
      have hyes : bitsExpectation q V (fun S => if R ⊆ insert e S then 1 else 0) =
          bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) := by
        apply bitsExpectation_congr
        intro S hS
        have hiff : R ⊆ insert e S ↔ R ⊆ S := by
          constructor
          · intro h x hx
            exact (mem_insert.mp (h hx)).resolve_left (fun h => heR (h ▸ hx))
          · exact fun h => h.trans (subset_insert e S)
        simp only [hiff]
      rw [hyes, ih _ hRV]
      ring

lemma bitsExpectation_mul_const (q : α → ℝ) (V : Finset α) (c : ℝ) (f : Finset α → ℝ) :
    bitsExpectation q V (fun S => c * f S) = c * bitsExpectation q V f := by
  simp only [bitsExpectation, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

lemma bitsExpectation_contains_le_half_pow (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V R : Finset α) (hR : R ⊆ V) :
    bitsExpectation q V (fun S => if R ⊆ S then 1 else 0) ≤ (1 / 2 : ℝ) ^ R.card := by
  rw [bitsExpectation_contains q V R hR]
  simpa using prod_le_prod₀ (fun e _ => hq0 e) (fun e _ => hqhalf e)

noncomputable def residualBad (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : Prop :=
  ∃ R ∈ F, t < (R.card : ℝ) ∧ R ⊆ S

noncomputable def residualBadIndicator (F : Finset (Finset α)) (t : ℝ) (S : Finset α) : ℝ := by
  classical
  exact if residualBad F t S then 1 else 0

lemma residualBad_indicator_le (F : Finset (Finset α)) (t : ℝ) (S : Finset α) :
    residualBadIndicator F t S ≤
      ∑ R ∈ F, if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0 := by
  classical
  unfold residualBadIndicator
  split_ifs with hb
  · obtain ⟨R, hRF, hRt, hRS⟩ := hb
    have h := single_le_sum (f := fun R : Finset α =>
      if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0)
      (fun R _ => by split_ifs <;> norm_num) hRF
    simpa [hRt, hRS] using h
  · exact sum_nonneg (fun R _ => by split_ifs <;> norm_num)

lemma bitsExpectation_residualBad_le (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V) (t : ℝ) :
    bitsExpectation q V (fun S => residualBadIndicator F t S) ≤
      (F.card : ℝ) * Real.exp (-t * Real.log 2) := by
  classical
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqhalf e).trans (by norm_num)
  calc
    _ ≤ bitsExpectation q V (fun S => ∑ R ∈ F,
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) :=
      bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBad_indicator_le F t S)
    _ = ∑ R ∈ F, bitsExpectation q V (fun S =>
        if t < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) := bitsExpectation_sum q V F _
    _ ≤ ∑ _R ∈ F, Real.exp (-t * Real.log 2) := by
      apply sum_le_sum
      intro R hRF
      by_cases hRt : t < (R.card : ℝ)
      · simp only [hRt, ite_true]
        apply (bitsExpectation_contains_le_half_pow q hq0 hqhalf V R (hF R hRF)).trans
        have heq : (1 / 2 : ℝ) ^ R.card = Real.exp (-(R.card : ℝ) * Real.log 2) := by
          rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
          simp
        rw [heq]
        apply Real.exp_le_exp.mpr
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        exact mul_le_mul_of_nonneg_right (by linarith) hlog
      · simp only [hRt, ite_false, bitsExpectation_const]
        exact Real.exp_nonneg _
    _ = _ := by simp

end MatroidProphet

end OAI
