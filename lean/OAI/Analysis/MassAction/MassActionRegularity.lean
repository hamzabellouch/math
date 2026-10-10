import OAI.Analysis.MassAction.Model

namespace OAI

noncomputable section

namespace Problem326

/-- Every mass-action monomial is smooth on the whole ambient real space. -/
theorem contDiff_monomial {d : ℕ} (y : Fin d → ℕ) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => monomial x y) := by
  unfold monomial
  fun_prop

/-- The mass-action vector field is polynomial, hence globally smooth. -/
theorem contDiff_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : ContDiff ℝ ⊤ (massAction N κ) := by
  unfold massAction monomial
  fun_prop

theorem contDiff_one_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : ContDiff ℝ 1 (massAction N κ) :=
  (contDiff_massAction N κ).of_le (by simp)

theorem locallyLipschitz_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) : LocallyLipschitz (massAction N κ) :=
  (contDiff_one_massAction N κ).locallyLipschitz

end Problem326

end

end OAI
