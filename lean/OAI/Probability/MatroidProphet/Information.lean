import OAI.Probability.MatroidProphet.Model

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MatroidProphet

theorem decisionAt_congr {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v v' : Weights n) (π π' : ArrivalOrder n) (k : Fin n)
    (h : history v π k = history v' π' k) :
    decisionAt A r s v π k = decisionAt A r s v' π' k := by
  simp only [decisionAt, h]

theorem acceptedThrough_mono {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) {t t' : ℕ} (h : t ≤ t') :
    acceptedThrough A r s v π t ⊆ acceptedThrough A r s v π t' := by
  classical
  intro e he
  simp only [acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨lt_of_lt_of_le he.1 h, he.2⟩

theorem acceptedThrough_arrived {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : e ∈ acceptedThrough A r s v π t) : (π.symm e).val < t := by
  classical
  exact ((Finset.mem_filter.mp he).2).1

theorem acceptedThrough_iff_decision {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : (π.symm e).val < t) :
    e ∈ acceptedThrough A r s v π t ↔ decisionAt A r s v π (π.symm e) = true := by
  classical
  simp only [acceptedThrough, Finset.mem_filter, Finset.mem_univ, true_and, he]

theorem sum_le_optimum {n : ℕ} (M : Matroid (Fin n)) (v : Weights n)
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) :
    (∑ e ∈ I, v e) ≤ optimum M v := by
  classical
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    (f := fun J => if M.Indep (J : Set (Fin n)) then ∑ e ∈ J, v e else 0)
    (Finset.mem_univ I)
  change _ ≤ Finset.univ.sup' Finset.univ_nonempty _
  simpa only [ite_eq_left hI] using h

theorem measurable_optimum {n : ℕ} (M : Matroid (Fin n)) : Measurable (optimum M) := by
  classical
  have hm (I : Finset (Fin n)) :
      Measurable (fun v : Weights n =>
        if M.Indep (I : Set (Fin n)) then ∑ e ∈ I, v e else 0) := by
    by_cases hI : M.Indep (I : Set (Fin n))
    · simpa [hI] using I.measurable_sum (fun e _ => measurable_pi_apply e)
    · simp [hI]
  have hsup := Finset.measurable_sup' (s := (Finset.univ : Finset (Finset (Fin n))))
    Finset.univ_nonempty (fun I _ => hm I)
  convert hsup using 1
  ext v
  simp only [optimum, Finset.sup'_apply]

theorem optimum_nonneg {n : ℕ} (M : Matroid (Fin n)) (v : Weights n) :
    0 ≤ optimum M v := by
  simpa using sum_le_optimum M v ∅ (by simp)

theorem reward_nonneg {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (hv : ∀ e, 0 ≤ v e) :
    0 ≤ reward A r s v π := by
  exact Finset.sum_nonneg fun e _ => hv e

theorem reward_le_optimum {n bits : ℕ} (M : Matroid (Fin n)) (A : OnlineRule n bits)
    (hA : Feasible M A) (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n)
    (hs : ∀ e, 0 ≤ s e) (hv : ∀ e, 0 ≤ v e) :
    reward A r s v π ≤ optimum M v :=
  sum_le_optimum M v (accepted A r s v π) (hA r s v π n hs hv)

lemma measurable_history {n : ℕ} (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun v : Weights n => history v π k) := by
  apply Measurable.of_eval
  intro j
  exact measurable_const.prodMk (measurable_pi_apply (π (prefixIndex k j)))

lemma measurable_decisionAt {n bits : ℕ} (A : OnlineRule n bits)
    (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      decisionAt A x.1 x.2.1 x.2.2 π k) :=
  (A.measurable_decide k).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_history π k).comp (measurable_snd.comp measurable_snd))))

lemma reward_eq_sum {n bits : ℕ} (A : OnlineRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) :
    reward A r s v π =
      ∑ e : Fin n, if decisionAt A r s v π (π.symm e) = true then v e else 0 := by
  classical
  unfold reward accepted acceptedThrough
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [(π.symm e).isLt, true_and]

lemma measurable_reward_fixed_order {n bits : ℕ} (A : OnlineRule n bits)
    (π : ArrivalOrder n) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      reward A x.1 x.2.1 x.2.2 π) := by
  classical
  simp_rw [reward_eq_sum]
  apply Finset.measurable_sum
  intro e _
  have hd := measurable_decisionAt A π (π.symm e)
  have ht : MeasurableSet {x : Seed bits × (Weights n × Weights n) |
      decisionAt A x.1 x.2.1 x.2.2 π (π.symm e) = true} :=
    hd (measurableSet_singleton true)
  exact Measurable.ite ht
    ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd)) measurable_const

theorem measurable_reward {n bits : ℕ} (A : OnlineRule n bits) :
    Measurable (fun x : ArrivalOrder n × (Seed bits × (Weights n × Weights n)) =>
      reward A x.2.1 x.2.2.1 x.2.2.2 x.1) :=
  measurable_from_prod_countable_right (measurable_reward_fixed_order A)

end MatroidProphet

end OAI
