import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem degree_eq_inside_add_outside {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Finset (Fin n)) (w : Fin n) :
    graphDegree G w = (a.filter (G.Adj w)).card +
      ((Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a)).card := by
  have h := (Finset.univ.filter (G.Adj w)).card_filter_add_card_filter_not
    (fun v => v ∈ a)
  have hin : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) =
      a.filter (G.Adj w) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hin] at h
  exact h.symm

theorem inside_count_eq_of_degrees_outside {n : ℕ}
    {G H : SimpleGraph (Fin n)} (a : Finset (Fin n))
    (hdegree : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (w : Fin n) (hw : w ∉ a) :
    (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card := by
  have hs : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ.filter (H.Adj w)).filter (fun v => v ∉ a) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hG, hv⟩
      exact ⟨(hout w hw v hv).mp hG, hv⟩
    · rintro ⟨hH, hv⟩
      exact ⟨(hout w hw v hv).mpr hH, hv⟩
  have h := hdegree w
  rw [degree_eq_inside_add_outside G a w, degree_eq_inside_add_outside H a w,
    hs] at h
  exact Nat.add_right_cancel h

theorem sameFiber_iff_outside_inside {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hout, hin⟩
    refine ⟨hout, hin, ?_⟩
    exact inside_count_eq_of_degrees_outside a
      (fun w => (G.property w).trans (H.property w).symm) hout

end Problem315.PairResampling

end

end OAI
