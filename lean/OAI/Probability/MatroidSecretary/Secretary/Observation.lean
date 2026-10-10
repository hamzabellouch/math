import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Secretary.PrefixObservationModel

namespace OAI

open MeasureTheory Finset

namespace MatroidProphet

@[simp] lemma mem_orderPrefix {n : ℕ} (π : ArrivalOrder n) (K : ℕ) (e : Fin n) :
    e ∈ orderPrefix π K ↔ (π.symm e).val < K := by
  simp [orderPrefix]

@[simp] lemma prefixLabels_zero {n : ℕ} {k : Fin n} (h : History n k) :
    prefixLabels 0 h = ∅ := by
  simp [prefixLabels]

@[simp] lemma prefixWeights_zero {n : ℕ} {k : Fin n} (h : History n k) :
    prefixWeights 0 h = 0 := by
  funext e
  simp [prefixWeights]

lemma prefixLabels_history {n : ℕ} (w : Weights n) (π : ArrivalOrder n)
    (k : Fin n) (K : ℕ) (hK : K ≤ k.val + 1) :
    prefixLabels K (history w π k) = orderPrefix π K := by
  ext e
  simp only [prefixLabels, mem_image, mem_filter, mem_univ, true_and, mem_orderPrefix]
  constructor
  · rintro ⟨j, hj, hje⟩
    have hj' : prefixIndex k j = π.symm e := by
      apply π.injective
      simpa [history] using hje
    have hv := congrArg Fin.val hj'
    exact hv ▸ hj
  · intro he
    let j : Fin (k.val + 1) := ⟨(π.symm e).val, lt_of_lt_of_le he hK⟩
    refine ⟨j, he, ?_⟩
    have hj : prefixIndex k j = π.symm e := by
      apply Fin.ext
      rfl
    simp [history, hj]

/-- Prefix-label extraction is measurable despite the real-valued history entries. -/
lemma measurable_prefixLabels {n : ℕ} (k : Fin n) (K : ℕ) :
    Measurable (prefixLabels (k := k) K) := by
  classical
  have hl : Measurable (fun h : History n k => fun j => (h j).1) := by
    apply Measurable.of_eval
    intro j
    exact measurable_fst.comp (measurable_pi_apply j)
  exact (measurable_of_countable (fun l : Fin (k.val + 1) → Fin n =>
    (Finset.univ.filter fun j => j.val < K).image l)).comp hl

/-- Changing the suffix entries of an available history does not change prefix data. -/
lemma prefixWeights_congr {n : ℕ} {k : Fin n} (K : ℕ) (h h' : History n k)
    (hh : ∀ j, j.val < K → h j = h' j) :
    prefixWeights K h = prefixWeights K h' := by
  funext e
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < K
  · rw [hh j hj]
  · simp [hj]

lemma prefixLabels_congr {n : ℕ} {k : Fin n} (K : ℕ) (h h' : History n k)
    (hh : ∀ j, j.val < K → (h j).1 = (h' j).1) :
    prefixLabels K h = prefixLabels K h' := by
  apply Finset.image_congr
  intro j hj
  exact hh j (Finset.mem_filter.mp hj).2

lemma measurable_prefixWeights {n : ℕ} (k : Fin n) (K : ℕ) :
    Measurable (prefixWeights (k := k) K) := by
  classical
  apply Measurable.of_eval
  intro e
  apply Finset.measurable_sum
  intro j _
  have hj : Measurable (fun h : History n k => h j) := measurable_pi_apply j
  have he : MeasurableSet {h : History n k | (h j).1 = e} :=
    (measurable_fst.comp hj) (measurableSet_singleton e)
  by_cases hKj : j.val < K
  · have hm : Measurable (fun h : History n k =>
        if (h j).1 = e then (h j).2 else (0 : ℝ)) :=
      Measurable.ite he (measurable_snd.comp hj) measurable_const
    simpa only [hKj, true_and] using hm
  · simp only [hKj, false_and, ite_false]
    exact measurable_const

/-- Seed-dependent cutoff extraction remains measurable jointly with the history. -/
lemma measurable_prefixWeights_seed {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (k : Fin n) (K : Q → Fin (n + 1)) (hK : Measurable K) :
    Measurable (fun x : Q × History n k => prefixWeights (K x.1).val x.2) := by
  have hm : Measurable (fun x : Fin (n + 1) × History n k =>
      prefixWeights x.1.val x.2) :=
    measurable_from_prod_countable_right fun j => measurable_prefixWeights k j.val
  exact hm.comp ((hK.comp measurable_fst).prodMk measurable_snd)

lemma measurable_prefixLabels_seed {n : ℕ} {Q : Type*} [MeasurableSpace Q]
    (k : Fin n) (K : Q → Fin (n + 1)) (hK : Measurable K) :
    Measurable (fun x : Q × History n k => prefixLabels (K x.1).val x.2) := by
  have hm : Measurable (fun x : Fin (n + 1) × History n k =>
      prefixLabels x.1.val x.2) :=
    measurable_from_prod_countable_right fun j => measurable_prefixLabels k j.val
  exact hm.comp ((hK.comp measurable_fst).prodMk measurable_snd)

lemma prefixWeights_history {n : ℕ} (w : Weights n) (π : ArrivalOrder n)
    (k : Fin n) (K : ℕ) (hK : K ≤ k.val + 1) (e : Fin n) :
    prefixWeights K (history w π k) e =
      if (π.symm e).val < K then w e else 0 := by
  classical
  by_cases he : (π.symm e).val < K
  · rw [ite_eq_left he]
    let j : Fin (k.val + 1) := ⟨(π.symm e).val, lt_of_lt_of_le he hK⟩
    have hj : prefixIndex k j = π.symm e := by
      apply Fin.ext
      rfl
    unfold prefixWeights
    rw [Finset.sum_eq_single j]
    · simp [history, hj, j, he]
    · intro b _ hbj
      have hne : π (prefixIndex k b) ≠ e := by
        intro hb
        apply hbj
        apply Fin.ext
        have hbi : prefixIndex k b = π.symm e := by
          apply π.injective
          simpa using hb
        exact congrArg (fun z : Fin n => z.val) hbi
      simp [history, hne]
    · simp
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < K
    · have hne : π (prefixIndex k j) ≠ e := by
        intro hje
        apply he
        have hji : prefixIndex k j = π.symm e := by
          apply π.injective
          simpa using hje
        have hv := congrArg Fin.val hji
        exact hv ▸ hj
      simp [history, hne]
    · simp [hj]

lemma prefixWeights_eq_observed {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (k : Fin n) (K : ℕ)
    (hK : K ≤ k.val + 1) (hmask : A.mask r = orderPrefix π K) :
    prefixWeights K (history w π k) = observed A r w := by
  funext e
  rw [prefixWeights_history w π k K hK e]
  simp [observed, hmask]

lemma hiddenAcceptedThrough_prefix_empty {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (K t : ℕ)
    (hmask : A.mask r = orderPrefix π K) (ht : t ≤ K) :
    hiddenAcceptedThrough A r w π t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, hnot⟩ := Finset.mem_sdiff.mp he
  apply hnot
  rw [hmask, mem_orderPrefix]
  exact lt_of_lt_of_le (acceptedThrough_arrived A.core r (observed A r w) w π t e he) ht

end MatroidProphet

end OAI
