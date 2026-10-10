import OAI.Analysis.MassAction.Model

namespace OAI

noncomputable section

namespace Problem326

/-- Pairing the mass-action vector field with a fixed normal commutes with
its finite reaction sum. This is the algebraic bridge to ordered-cut flux. -/
theorem dot_massAction {d : ℕ} (N : ReactionNetwork d)
    (κ : Reaction N → ℝ) (x r : Fin d → ℝ) :
    dot r (massAction N κ x) =
      ∑ e : Reaction N, κ e * monomial x e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) -
          dot r (fun i => (e.val.1 i : ℝ))) := by
  classical
  unfold dot massAction
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The derivative of a fixed linear functional along a differentiable curve. -/
theorem hasDerivAt_dot {d : ℕ} {x : ℝ → (Fin d → ℝ)}
    {v : Fin d → ℝ} {t : ℝ} (hx : HasDerivAt x v t)
    (r : Fin d → ℝ) :
    HasDerivAt (fun s => dot r (x s)) (dot r v) t := by
  unfold dot
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_pi.mp hx i).const_mul (r i)

/-- Affine labels have the expected derivative along solution curves. -/
theorem hasDerivAt_affineLabel {d : ℕ} {x : ℝ → (Fin d → ℝ)}
    {v : Fin d → ℝ} {t : ℝ} (hx : HasDerivAt x v t)
    (r : Fin d → ℝ) (c : ℝ) :
    HasDerivAt (fun s => dot r (x s) + c) (dot r v) t := by
  simpa using (hasDerivAt_dot hx r).add_const c

/-- The derivative of an affine label along a local mass-action solution,
expressed in the scalar form used by the finite graph estimate. -/
theorem IsForwardSolutionOn.hasDerivAt_affineLabel {d : ℕ}
    {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {x0 : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ x0 T x) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) (r : Fin d → ℝ) (c : ℝ) :
    HasDerivAt (fun s => dot r (x s) + c)
      (∑ e : Reaction N, κ e * monomial (x t) e.val.1 *
        (dot r (fun i => (e.val.2 i : ℝ)) -
          dot r (fun i => (e.val.1 i : ℝ)))) t := by
  rw [← dot_massAction]
  exact Problem326.hasDerivAt_affineLabel (hx.2.2 t ht) r c

end Problem326

end

end OAI
