import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonFiniteNormalization
open Set Metric

lemma three_marks_two_metrics {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (v : Fin 3 → X) (w : Fin 3 → Y) {s t : ℝ}
    (hv : ∀ i j,i ≠ j → s ≤ dist (v i) (v j))
    (hw : ∀ i j,i ≠ j → t ≤ dist (w i) (w j)) (x : X) (y : Y) :
    ∃ i,s/2 ≤ dist x (v i) ∧ t/2 ≤ dist y (w i) := by
  classical
  by_contra hn
  have hc (i : Fin 3) : dist x (v i) < s/2 ∨ dist y (w i) < t/2 := by
    by_cases hi : s/2 ≤ dist x (v i)
    · exact Or.inr (lt_of_not_ge (fun hh=>hn ⟨i,hi,hh⟩))
    · exact Or.inl (lt_of_not_ge hi)
  let b : Fin 3 → Bool:=fun i=>decide (dist x (v i) < s/2)
  have hb : Function.Injective b := by
    intro i j hij
    by_contra hne
    have heq : (dist x (v i) < s/2)↔(dist x (v j) < s/2) := by
      simpa only [b,decide_eq_decide] using hij
    by_cases hi : dist x (v i) < s/2
    · have hj:=heq.mp hi
      have ht:=dist_triangle (v i) x (v j)
      rw [dist_comm (v i) x] at ht
      have hs:=hv i j hne
      linarith
    · have hi':=(hc i).resolve_left hi
      have hj':=(hc j).resolve_left (fun hj=>hi (heq.mpr hj))
      have ht:=dist_triangle (w i) y (w j)
      rw [dist_comm (w i) y] at ht
      have hs:=hw i j hne
      linarith
  have hh:=Fintype.card_le_of_injective b hb
  norm_num at hh

lemma normalized_outer_endpoint {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (v : Fin 3 → X) (w : Fin 3 → Y)
    {s t R B : ℝ} (hv : ∀ i j,i ≠ j → s ≤ dist (v i) (v j))
    (hw : ∀ i j,i ≠ j → t ≤ dist (w i) (w j))
    (hmark : ∀ i,f (v i)=w i) (hR : R ≤ s/2) (hB : B ≤ t/2) (o : X) :
    ∃ z : X,R ≤ dist o z ∧ B ≤ dist (f z) (f o) := by
  obtain ⟨i,hi,hwi⟩:=three_marks_two_metrics v w hv hw o (f o)
  refine ⟨v i,hR.trans hi,?_⟩
  rw [hmark i,dist_comm]
  exact hB.trans hwi

lemma nearby_marks_separated {X : Type*} [PseudoMetricSpace X]
    (a v : Fin 3 → X) {s e : ℝ}
    (ha : ∀ i j,i ≠ j → s ≤ dist (a i) (a j))
    (hv : ∀ i,dist (a i) (v i) ≤ e) :
    ∀ i j,i ≠ j → s-2*e ≤ dist (v i) (v j) := by
  intro i j hij
  have h:=dist_triangle (a i) (v i) (a j)
  have h':=dist_triangle (v i) (v j) (a j)
  rw [dist_comm (v j) (a j)] at h'
  have hi:=hv i
  have hj:=hv j
  have hs:=ha i j hij
  linarith

lemma moving_normalized_outer_endpoint {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (a v : Fin 3 → X) (w : Fin 3 → Y)
    {s t e R B : ℝ} (ha : ∀ i j,i ≠ j → s ≤ dist (a i) (a j))
    (hv : ∀ i,dist (a i) (v i) ≤ e)
    (hw : ∀ i j,i ≠ j → t ≤ dist (w i) (w j))
    (hmark : ∀ i,f (v i)=w i) (hR : R ≤ (s-2*e)/2)
    (hB : B ≤ t/2) (o : X) :
    ∃ z : X,R ≤ dist o z ∧ B ≤ dist (f z) (f o) :=
  normalized_outer_endpoint f v w (nearby_marks_separated a v ha hv)
    hw hmark hR hB o
end CannonFiniteNormalization

end
end
end
end

end OAI
