import OAI.Probability.SwitchChain.PairGeneratorSquare
import OAI.Probability.SwitchChain.ProjectionTools

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem disjoint_sum_nonneg_of_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d → StateSpace n d)
    (hlocal : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b f‖ ^ 2 - ‖R a b f‖ ^ 2 - ‖R b a f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b f‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b f‖ ^ 2 else 0) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  classical
  let s := (pairs n ×ˢ pairs n).filter (fun p => Disjoint p.1 p.2)
  have hmem (a b : Finset (Fin n)) :
      (a,b) ∈ s ↔ a ∈ pairs n ∧ b ∈ pairs n ∧ Disjoint a b := by
    simp only [s, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum (F : Finset (Fin n) → Finset (Fin n) → ℝ) :
      (∑ p ∈ s, F p.1 p.2) =
        ∑ a ∈ pairs n, ∑ b ∈ pairs n, if Disjoint a b then F a b else 0 := by
    rw [show s = (pairs n ×ˢ pairs n).filter
      (fun p => Disjoint p.1 p.2) from rfl, Finset.sum_filter, Finset.sum_product]
  have h := ProjectionTools.sum_disjoint_nonneg s
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (fun a b => ‖g a b f‖ ^ 2) (fun a b => ‖R a b f‖ ^ 2) ?_ ?_ ?_
  · rw [hsum (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)] at h
    exact h
  · rintro ⟨a,b⟩ hab
    have hp := (hmem a b).mp hab
    exact (hmem b a).mpr ⟨hp.2.1, hp.1, hp.2.2.symm⟩
  · intro a b hab
    have hp := (hmem a b).mp hab
    exact hlocal a hp.1 b hp.2.1 hp.2.2
  · rw [hsum (fun a b => ‖R a b f‖ ^ 2), hsum (fun a b => ‖g a b f‖ ^ 2)]
    exact Finset.sum_le_sum hbudget

theorem generator_square_of_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d → StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hlocal : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b f‖ ^ 2 - ‖R a b f‖ ^ 2 - ‖R b a f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b f‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b f‖ ^ 2 else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ :=
  generator_square_of_local hn f htriple
    (disjoint_sum_nonneg_of_interaction_budget f g R hlocal hbudget)

end Problem315.PairResampling

end

end OAI
