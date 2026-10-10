import Mathlib
import OAI.Computability.VertexCover.Analysis.SelectedIntegralAbs
import OAI.Computability.VertexCover.Analysis.StarMeanContinuous

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Average

theorem finiteMean_finset {α : Type*} (T : Finset α) (f : α → ℝ) :
    VertexCover.finiteMean (fun a : T => f a) = (∑ a ∈ T, f a) / T.card := by
  classical
  unfold VertexCover.finiteMean
  rw [Finset.sum_coe_sort, Fintype.card_coe]

theorem finiteMean_condition_mul {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    VertexCover.finiteMean (fun a => fiberAverage q (fun _ => f) (q a) * g (q a)) =
      VertexCover.finiteMean (fun a => f a * g (q a)) := by
  classical
  have h := sum_fiberAverage q (fun i a => f a * g i)
  have he : ∀ i, fiberAverage q (fun i a => f a * g i) i =
      fiberAverage q (fun _ => f) i * g i := by
    intro i
    unfold fiberAverage
    rw [← Finset.sum_mul]
    ring
  simp_rw [he] at h
  exact congrArg (fun x : ℝ => x / Fintype.card α) h

theorem finiteMean_condition_orthogonal {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    VertexCover.finiteMean (fun a => (f a - fiberAverage q (fun _ => f) (q a)) * g (q a)) = 0 := by
  have he : (fun a => (f a - fiberAverage q (fun _ => f) (q a)) * g (q a)) =
      (fun a => f a * g (q a) - fiberAverage q (fun _ => f) (q a) * g (q a)) := by
    funext a
    ring
  rw [he, VertexCover.finiteMean_sub, finiteMean_condition_mul, sub_self]

theorem finiteMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    VertexCover.finiteMean (fun a => c * f a) = c * VertexCover.finiteMean f := by
  classical
  simp only [VertexCover.finiteMean, ← Finset.mul_sum]
  ring

theorem finiteMean_sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ VertexCover.finiteMean (fun a => (f a)^2) :=
  div_nonneg (Finset.sum_nonneg (fun a _ => sq_nonneg (f a))) (Nat.cast_nonneg _)

theorem finiteMean_condition_pythagoras {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    VertexCover.finiteMean (fun a => (f a - g (q a))^2) =
      VertexCover.finiteMean (fun a => (f a - fiberAverage q (fun _ => f) (q a))^2) +
      VertexCover.finiteMean (fun a => (fiberAverage q (fun _ => f) (q a) - g (q a))^2) := by
  have he : (fun a => (f a - g (q a))^2) =
      (fun a => (f a - fiberAverage q (fun _ => f) (q a))^2 +
        (fiberAverage q (fun _ => f) (q a) - g (q a))^2 +
        2 * ((f a - fiberAverage q (fun _ => f) (q a)) *
          (fiberAverage q (fun _ => f) (q a) - g (q a)))) := by
    funext a
    ring
  rw [he, VertexCover.finiteMean_add, VertexCover.finiteMean_add,
    finiteMean_const_mul,
    finiteMean_condition_orthogonal q f (fun i => fiberAverage q (fun _ => f) i - g i)]
  ring

theorem finiteMean_condition_best {α β : Type*} [Fintype α] [Fintype β]
    (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    VertexCover.finiteMean (fun a => (f a - fiberAverage q (fun _ => f) (q a))^2) ≤
      VertexCover.finiteMean (fun a => (f a - g (q a))^2) := by
  rw [finiteMean_condition_pythagoras q f g]
  exact le_add_of_nonneg_right (finiteMean_sq_nonneg
    (fun a : α => fiberAverage q (fun _ => f) (q a) - g (q a)))

end VertexCover.Average


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
