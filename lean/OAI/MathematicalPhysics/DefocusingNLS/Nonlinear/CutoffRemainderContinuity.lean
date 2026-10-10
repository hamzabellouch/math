import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepRemainder

namespace OAI

/-! # Continuity of the remainder extension on the smaller contraction ball -/

namespace DefocusingNLS

theorem continuous_cutoffRemainderExtension_on_ball
    {P V : Type*} [TopologicalSpace P] [NormedAddCommGroup V]
    (δ r : ℝ) (hrδ : r ≤ δ)
    (h : P → ℕ → {v : V // ‖v‖ ≤ δ} → V)
    (hc : ∀ n, Continuous (fun q : P × {v : V // ‖v‖ ≤ δ} => h q.1 n q.2)) (n : ℕ) :
    Continuous (fun q : P × {v : V // ‖v‖ ≤ r} =>
      cutoffRemainderExtension δ (h q.1) n q.2.1) := by
  have he : (fun q : P × {v : V // ‖v‖ ≤ r} =>
      cutoffRemainderExtension δ (h q.1) n q.2.1) =
      (fun q => h q.1 n ⟨q.2.1, q.2.2.trans hrδ⟩) := by
    funext q
    simp only [cutoffRemainderExtension, dite_eq_left (q.2.2.trans hrδ)]
  rw [he]
  exact (hc n).comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _))

end DefocusingNLS

end OAI
