import OAI.Probability.SwitchChain.CrossCellIndependence
import OAI.Probability.SwitchChain.IndependentMomentProjection
import OAI.Probability.SwitchChain.IndependentProjectionInteraction

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments
attribute [local instance] Classical.propDecidable

variable {α β : Type*} [Fintype α] [Fintype β]

theorem projection_covariance_of_product_average (s : ℕ)
    (r : α → Fin 3) (c : β → Fin 3)
    (hprod : ∀ (u : α → ℝ) (v : β → ℝ),
      average s r c (fun x y => u x * v y) =
        average s r c (fun x _ => u x) * average s r c (fun _ y => v y))
    (f g : EuclideanSpace ℝ (Cell s r c)) :
    ⟪PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f,
      PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) g⟫ =
      (∑ z, f z) * (∑ z, g z) / (Fintype.card (Cell s r c) : ℝ) := by
  exact IndependentCell.projection_covariance_of_average_products
    (fun z : Cell s r c => z.val.2.1) (fun z : Cell s r c => z.val.2.2)
    hprod f g

theorem projection_covariance_of_total_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3)
    (f g : EuclideanSpace ℝ (Cell s r c)) :
    ⟪PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f,
      PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) g⟫ =
      (∑ z, f z) * (∑ z, g z) / (Fintype.card (Cell s r c) : ℝ) :=
  projection_covariance_of_product_average s r c
    (average_product_independent_of_ne_two s hs r c) f g

theorem projection_covariance_of_degenerate (r : α → Fin 3) (c : β → Fin 3)
    (hzero : average 2 r c (fun x _ => offCenter r x) = 0 ∨
      average 2 r c (fun _ y => offCenter c y) = 0 ∨
      average 2 r c (fun x y => (1 - offCenter r x) * (1 - offCenter c y)) = 0)
    (f g : EuclideanSpace ℝ (Cell 2 r c)) :
    ⟪PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.1)) f,
      PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.2)) g⟫ =
      (∑ z, f z) * (∑ z, g z) / (Fintype.card (Cell 2 r c) : ℝ) :=
  projection_covariance_of_product_average 2 r c
    (average_product_independent_of_degenerate r c hzero) f g

theorem independent_projection_interaction (s : ℕ)
    (r : α → Fin 3) (c : β → Fin 3) [Nonempty (Cell s r c)]
    (hcase : s ≠ 2 ∨ average s r c (fun x _ => offCenter r x) = 0 ∨
      average s r c (fun _ y => offCenter c y) = 0 ∨
      average s r c (fun x y => (1 - offCenter r x) * (1 - offCenter c y)) = 0)
    (G : EuclideanSpace ℝ (Cell s r c) →ₗ[ℝ] EuclideanSpace ℝ (Cell s r c))
    (hGs : G.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGfirst : ∀ f, G (PairFibers.expectation
      (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f) = 0)
    (hGsecond : ∀ f, G (PairFibers.expectation
      (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f) = 0)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ‖G f‖ ^ 2 ≤
      ⟪f - PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f,
        f - PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f⟫ := by
  apply IndependentCell.independent_interaction_of_covariance
    (Setoid.ker (fun z : Cell s r c => z.val.2.1))
    (Setoid.ker (fun z : Cell s r c => z.val.2.2)) _ G hGs hGi hGfirst hGsecond f
  intro u v
  by_cases hs : s = 2
  · subst s
    exact projection_covariance_of_degenerate r c (hcase.resolve_left (by simp)) u v
  · exact projection_covariance_of_total_ne_two s hs r c u v

theorem independent_projection_interaction_with_errors (s : ℕ)
    (r : α → Fin 3) (c : β → Fin 3) [Nonempty (Cell s r c)]
    (hcase : s ≠ 2 ∨ average s r c (fun x _ => offCenter r x) = 0 ∨
      average s r c (fun _ y => offCenter c y) = 0 ∨
      average s r c (fun x y => (1 - offCenter r x) * (1 - offCenter c y)) = 0)
    (G : EuclideanSpace ℝ (Cell s r c) →ₗ[ℝ] EuclideanSpace ℝ (Cell s r c))
    (hGs : G.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGfirst : ∀ f, G (PairFibers.expectation
      (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f) = 0)
    (hGsecond : ∀ f, G (PairFibers.expectation
      (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f) = 0)
    (f u v : EuclideanSpace ℝ (Cell s r c)) :
    2 * ‖G f‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2 ≤
      2 * ⟪f - PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f,
        f - PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f⟫ := by
  have h := independent_projection_interaction s r c hcase G hGs hGi hGfirst hGsecond f
  nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖]

end Problem315.CrossCellMoments

end

end OAI
