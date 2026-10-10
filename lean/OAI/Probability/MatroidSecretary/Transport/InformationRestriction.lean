import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Explicit information restrictions for hidden-vector rules

These lemmas formalize the no-future-information and irrevocability clauses of
`sections/algorithm.tex`, Lemma `lem:feasibility`. They use only the concrete
history and acceptance definitions; no correctness hypothesis for an algorithm
is introduced.
-/

namespace MatroidProphet

open Finset

lemma observed_eq_of_eq_on_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w w' : Weights n)
    (h : ∀ e ∈ A.mask r, w e = w' e) :
    observed A r w = observed A r w' := by
  classical
  funext e
  by_cases he : e ∈ A.mask r
  · simp only [observed, ite_eq_left he, h e he]
  · simp only [observed, ite_eq_right he]

lemma history_eq_of_agree_before {n : ℕ} (v v' : Weights n)
    (π π' : ArrivalOrder n) (t : ℕ)
    (h : ∀ j : Fin n, j.val < t → (π j, v (π j)) = (π' j, v' (π' j)))
    (k : Fin n) (hk : k.val < t) :
    history v π k = history v' π' k := by
  funext j
  exact h (prefixIndex k j) (by dsimp [prefixIndex]; omega)

/-- Equal available label/value pairs give the same accepted set through a prefix.
The two complete arrival orders and all later values may be different. -/
theorem acceptedThrough_eq_of_agree_before {n bits : ℕ} (A : OnlineRule n bits)
    (r : Seed bits) (s v v' : Weights n) (π π' : ArrivalOrder n) (t : ℕ)
    (h : ∀ j : Fin n, j.val < t → (π j, v (π j)) = (π' j, v' (π' j))) :
    acceptedThrough A r s v π t = acceptedThrough A r s v' π' t := by
  classical
  have subset (v₁ v₂ : Weights n) (ρ₁ ρ₂ : ArrivalOrder n)
      (hρ : ∀ j : Fin n, j.val < t →
        (ρ₁ j, v₁ (ρ₁ j)) = (ρ₂ j, v₂ (ρ₂ j))) :
      acceptedThrough A r s v₁ ρ₁ t ⊆ acceptedThrough A r s v₂ ρ₂ t := by
    intro e he
    have hmem := (Finset.mem_filter.mp he).2
    have hl := congrArg Prod.fst (hρ (ρ₁.symm e) hmem.1)
    have hidx : ρ₂.symm e = ρ₁.symm e := by
      apply ρ₂.injective
      simpa only [Equiv.apply_symm_apply] using hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ e, ?_, ?_⟩
    · simpa only [hidx] using hmem.1
    · rw [hidx]
      rw [← decisionAt_congr A r s v₁ v₂ ρ₁ ρ₂ (ρ₁.symm e)
        (history_eq_of_agree_before v₁ v₂ ρ₁ ρ₂ t hρ _ hmem.1)]
      exact hmem.2
  exact Finset.Subset.antisymm (subset v v' π π' h)
    (subset v' v π' π (fun j hj => (h j hj).symm))

/-- A hidden-vector execution depends only on its revealed coordinates and the
actual arrival history, never on the unobserved future values or future order. -/
theorem hiddenAcceptedThrough_eq_of_same_information {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (w w' : Weights n)
    (π π' : ArrivalOrder n) (t : ℕ)
    (hmask : ∀ e ∈ A.mask r, w e = w' e)
    (hhist : ∀ j : Fin n, j.val < t →
      (π j, w (π j)) = (π' j, w' (π' j))) :
    hiddenAcceptedThrough A r w π t = hiddenAcceptedThrough A r w' π' t := by
  unfold hiddenAcceptedThrough
  rw [observed_eq_of_eq_on_mask A r w w' hmask]
  rw [acceptedThrough_eq_of_agree_before A.core r (observed A r w') w w' π π' t hhist]

/-- Hidden-vector acceptances cannot be revoked. -/
theorem hiddenAcceptedThrough_monotone {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) :
    Monotone (hiddenAcceptedThrough A r w π) := by
  intro t t' htt' e he
  have hm := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr
    ⟨acceptedThrough_mono A.core r (observed A r w) w π htt' hm.1, hm.2⟩

/-- Sacrifice is literal rejection, not merely exclusion from the reward sum. -/
theorem hiddenAcceptedThrough_disjoint_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    Disjoint (hiddenAcceptedThrough A r w π t) (A.mask r) := by
  exact Finset.sdiff_disjoint

/-- Every accepted hidden-vector label has actually arrived. -/
theorem hiddenAcceptedThrough_arrived {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (e : Fin n) (he : e ∈ hiddenAcceptedThrough A r w π t) :
    (π.symm e).val < t :=
  acceptedThrough_arrived A.core r (observed A r w) w π t e
    (Finset.mem_sdiff.mp he).1

/-- The observation operation is jointly measurable in the complete initial seed
and the hidden vector, despite an arbitrary seed-dependent mask. -/
lemma measurable_observed_seed {n bits : ℕ} (A : HiddenRule n bits) :
    Measurable (fun x : Seed bits × Weights n => observed A x.1 x.2) := by
  classical
  apply measurable_from_prod_countable_right
  intro r
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ A.mask r
  · simpa only [observed, ite_eq_left he] using
      (measurable_pi_apply e : Measurable (fun w : Weights n => w e))
  · simpa only [observed, ite_eq_right he] using
      (measurable_const : Measurable (fun _ : Weights n => (0 : ℝ)))

/-- With observations substituted, the actual core decision remains measurable. -/
lemma measurable_hidden_core_decide {n bits : ℕ} (A : HiddenRule n bits)
    (k : Fin n) :
    Measurable (fun x : Seed bits × (Weights n × History n k) =>
      A.core.decide k x.1 (observed A x.1 x.2.1) x.2.2) := by
  apply measurable_from_prod_countable_right
  intro r
  exact (A.core.measurable_decide k).comp
    (measurable_const.prodMk
      (((measurable_observed_seed A).comp
        (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))

end MatroidProphet

end OAI
