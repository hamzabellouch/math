import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonFiniteNormalization
open Set Metric

variable {X Y : Type*} [MetricSpace X]

lemma three_marks_avoid_two_points (v : Fin 3 → X) {sep : ℝ}
    (hv : ∀ i j,i≠j → sep≤dist (v i) (v j)) (x y : X) :
    ∃ i,sep/2≤dist x (v i) ∧ sep/2≤dist y (v i) := by
  classical
  by_contra hn
  have hc (i : Fin 3) : dist x (v i)<sep/2 ∨ dist y (v i)<sep/2 := by
    by_cases hi : sep/2≤dist x (v i)
    · exact Or.inr (lt_of_not_ge (fun hh=>hn ⟨i,hi,hh⟩))
    · exact Or.inl (lt_of_not_ge hi)
  let b : Fin 3 → Bool:=fun i=>decide (dist x (v i)<sep/2)
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    have hsv:=hv i j hne
    have hd (z : X) (hi : dist z (v i)<sep/2) (hj : dist z (v j)<sep/2) : False := by
      have ht:=dist_triangle (v i) z (v j)
      rw [dist_comm (v i) z] at ht
      linarith
    have heq : (dist x (v i)<sep/2)↔(dist x (v j)<sep/2) := by
      simpa only [b,decide_eq_decide] using hij
    by_cases hi : dist x (v i)<sep/2
    · exact hd x hi (heq.mp hi)
    · exact hd y ((hc i).resolve_left hi) ((hc j).resolve_left (fun hj=>hi (heq.mpr hj)))
  have hh:=Fintype.card_le_of_injective b hb
  norm_num at hh

lemma chart_mark_avoiding_images (f : X → Y) (v : Fin 3 → X) (w : Fin 3 → Y)
    {sep eps : ℝ} (hv : ∀ i j,i≠j → sep≤dist (v i) (v j))
    (heps : eps<sep/2) (hfiber : ∀ x y,f x=f y → dist x y≤eps)
    (hmark : ∀ i,f (v i)=w i) (x y : X) :
    ∃ i,sep/2≤dist x (v i) ∧ sep/2≤dist y (v i) ∧ f x≠w i ∧ f y≠w i := by
  obtain ⟨i,hix,hiy⟩:=three_marks_avoid_two_points v hv x y
  refine ⟨i,hix,hiy,?_,?_⟩
  · intro h
    have hh:=hfiber x (v i) (h.trans (hmark i).symm)
    linarith
  · intro h
    have hh:=hfiber y (v i) (h.trans (hmark i).symm)
    linarith
end CannonFiniteNormalization

end
end
end
end

end OAI
