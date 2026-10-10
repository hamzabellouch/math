import OAI.Probability.MatroidProphet.Algorithm.Observed

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

noncomputable def selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) : Finset (Fin n) :=
  layerGreedy M (assignedEligible (assign M hE d w) w)
    (fun b => finalPath M hE d w (b-2)) (assignedLayer (assign M hE d w) w)
    (fun e => (π.symm e).val)

lemma selection_not_observed (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n)
    (e : Fin n) (he : e ∈ selection M hE d w π) : e ∉ d.H ∪ d.D ∪ d.C := by
  have hel := layerGreedy_subset M _ _ _ _ he
  have ha := assigned_some_of_eligible (assign M hE d w) w e hel
  obtain ⟨i, _, hei, _⟩ := (assign_spec M hE d w e _ _).mp ha
  exact hei.1

theorem hiddenAccepted_eq_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) :
    hiddenAcceptedThrough (hidden M hE) r w π n =
      selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π := by
  classical
  have hA : accepted (core M hE) r (observed (hidden M hE) r w) w π =
      selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π := by
    unfold core
    rw [layerOnlineRule_accepted]
    obtain ⟨hf, _, ha⟩ := observed_preprocessing M hE r w
    rw [hf, ha]
    rfl
  change accepted (core M hE) r (observed (hidden M hE) r w) w π \ (hidden M hE).mask r = _
  rw [hA]
  ext e
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun he => he.1
  · intro he
    exact ⟨he, selection_not_observed M hE (mainMasks r) _ π e he⟩

theorem hiddenReward_eq_selection (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) :
    hiddenReward (hidden M hE) r w π =
      ∑ e ∈ selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π, w e := by
  unfold hiddenReward
  rw [hiddenAccepted_eq_selection]

theorem rounded_selection_le_hiddenReward (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (r : Seed (mainSeedBits n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e) (π : ArrivalOrder n) :
    (∑ e ∈ selection M hE (mainMasks r) (fun e => roundedLevel weightBase (w e)) π,
      roundedWeight weightBase (w e)) ≤ hiddenReward (hidden M hE) r w π := by
  rw [hiddenReward_eq_selection]
  apply Finset.sum_le_sum
  intro e he
  exact roundedWeight_le (by norm_num [weightBase]) (hw e)

end MatroidProphet.MainAlgorithm

end OAI
