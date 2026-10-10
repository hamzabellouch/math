import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [TopologicalSpace.SeparableSpace H]

theorem countable_orthogonal_family {I : Type*} (v : I → H)
    (hne : ∀ i,v i≠0) (hortho : ∀ i j,i≠j → inner ℂ (v i) (v j)=0) : Countable I := by
  let B : I → Set H := fun i => Metric.ball (v i) (‖v i‖/2)
  have hdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi : dist x (v i)<‖v i‖/2 := hxi
    have hj : dist x (v j)<‖v j‖/2 := hxj
    have hd := dist_triangle (v i) x (v j)
    rw [dist_comm (v i) x] at hd
    have hd' : ‖v i-v j‖ < (‖v i‖+‖v j‖)/2 := by
      rw [←dist_eq_norm]
      linarith
    have hs : ‖v i-v j‖^2=‖v i‖^2+‖v j‖^2 := by
      rw [@norm_sub_sq ℂ,hortho i j hij]
      simp
    have hs' := sq_nonneg (‖v i‖-‖v j‖)
    have hn := norm_pos_iff.mpr (hne i)
    have hn' := norm_pos_iff.mpr (hne j)
    nlinarith [norm_nonneg (v i-v j)]
  exact hdis.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by exact div_pos (norm_pos_iff.mpr (hne i)) (by norm_num))⟩)

end Kadison

end

end
end

end OAI
