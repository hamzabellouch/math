import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Secretary.Model
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

open MeasureTheory Finset

namespace MatroidProphet

variable {n : ℕ} {Q : Type*} [MeasurableSpace Q]

lemma secretaryDecisionAt_congr (A : SecretaryRule n Q) (q : Q)
    (w w' : Weights n) (π π' : ArrivalOrder n) (k : Fin n)
    (hh : history w π k = history w' π' k) :
    secretaryDecisionAt A q w π k = secretaryDecisionAt A q w' π' k := by
  simp only [secretaryDecisionAt, hh]

lemma secretaryAcceptedThrough_mono (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) {t t' : ℕ} (ht : t ≤ t') :
    secretaryAcceptedThrough A q w π t ⊆ secretaryAcceptedThrough A q w π t' := by
  intro e he
  simp only [secretaryAcceptedThrough, mem_filter, mem_univ, true_and] at he ⊢
  exact ⟨lt_of_lt_of_le he.1 ht, he.2⟩

lemma secretaryAcceptedThrough_arrived (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : e ∈ secretaryAcceptedThrough A q w π t) : (π.symm e).val < t :=
  (Finset.mem_filter.mp he).2.1

lemma secretaryAcceptedThrough_not_prefix (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : e ∈ secretaryAcceptedThrough A q w π t) :
    (A.prefixLength q).val ≤ (π.symm e).val := by
  have hd := (Finset.mem_filter.mp he).2.2
  by_contra hn
  have hlt : (π.symm e).val < (A.prefixLength q).val := Nat.lt_of_not_ge hn
  simp [secretaryDecisionAt, hlt] at hd

lemma secretaryAcceptedThrough_prefix_empty (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (ht : t ≤ (A.prefixLength q).val) :
    secretaryAcceptedThrough A q w π t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact (not_lt_of_ge (secretaryAcceptedThrough_not_prefix A q w π t e he))
    (lt_of_lt_of_le (secretaryAcceptedThrough_arrived A q w π t e he) ht)

lemma secretaryReward_nonneg (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ secretaryReward A q w π := by
  exact Finset.sum_nonneg fun e _ => hw e

lemma secretaryReward_le_optimum (M : Matroid (Fin n)) (A : SecretaryRule n Q)
    (hA : SecretaryFeasible M A) (q : Q) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (π : ArrivalOrder n) :
    secretaryReward A q w π ≤ optimum M w :=
  sum_le_optimum M w _ (hA q w hw π n)

lemma measurable_secretaryDecisionAt (A : SecretaryRule n Q)
    (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun x : Q × Weights n => secretaryDecisionAt A x.1 x.2 π k) := by
  classical
  have hp : MeasurableSet {x : Q × Weights n | k.val < (A.prefixLength x.1).val} :=
    (A.measurable_prefixLength.comp measurable_fst)
      (by trivial : MeasurableSet {K : Fin (n + 1) | k.val < K.val})
  exact Measurable.ite hp measurable_const
    ((A.measurable_decide k).comp
      (measurable_fst.prodMk ((measurable_history π k).comp measurable_snd)))

lemma secretaryReward_eq_sum (A : SecretaryRule n Q) (q : Q)
    (w : Weights n) (π : ArrivalOrder n) :
    secretaryReward A q w π =
      ∑ e : Fin n, if secretaryDecisionAt A q w π (π.symm e) = true then w e else 0 := by
  classical
  unfold secretaryReward secretaryAcceptedThrough
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [(π.symm e).isLt, true_and]

lemma measurable_secretaryReward_fixed_order (A : SecretaryRule n Q)
    (π : ArrivalOrder n) :
    Measurable (fun x : Q × Weights n => secretaryReward A x.1 x.2 π) := by
  classical
  simp_rw [secretaryReward_eq_sum]
  apply Finset.measurable_sum
  intro e _
  have hd := measurable_secretaryDecisionAt A π (π.symm e)
  have ht : MeasurableSet {x : Q × Weights n |
      secretaryDecisionAt A x.1 x.2 π (π.symm e) = true} :=
    hd (measurableSet_singleton true)
  exact Measurable.ite ht ((measurable_pi_apply e).comp measurable_snd) measurable_const

/-- No independence from the entire seed is imposed on the measurable arrival order. -/
lemma measurable_secretaryReward (A : SecretaryRule n Q) :
    Measurable (fun x : ArrivalOrder n × (Q × Weights n) =>
      secretaryReward A x.2.1 x.2.2 x.1) :=
  measurable_from_prod_countable_right (measurable_secretaryReward_fixed_order A)

lemma integrable_secretaryReward (M : Matroid (Fin n)) (A : SecretaryRule n Q)
    (hA : SecretaryFeasible M A) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : Ω → Q) (π : Ω → ArrivalOrder n) (hq : Measurable q) (hπ : Measurable π) :
    Integrable (fun ω => secretaryReward A (q ω) w (π ω)) μ := by
  have hm : Measurable (fun ω => secretaryReward A (q ω) w (π ω)) :=
    (measurable_secretaryReward A).comp
    (hπ.prodMk (hq.prodMk measurable_const))
  apply (integrable_const (optimum M w)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (secretaryReward_nonneg A (q ω) w (π ω) hw)]
  exact secretaryReward_le_optimum M A hA (q ω) w hw (π ω)

end MatroidProphet

end OAI
