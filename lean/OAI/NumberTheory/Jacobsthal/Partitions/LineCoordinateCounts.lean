import OAI.NumberTheory.Jacobsthal.Estimates.LatticeSpacing

namespace OAI

namespace Erdos970

section

namespace ErdosRichLine
open ErdosConvexGraph

theorem coordinate_card_le_div (X : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℤ)
    (hinj : Set.InjOn f (X : Set (ℤ × ℤ))) (S : ℝ) (hS : 0 ≤ S)
    (d : ℕ) (hd : 0 < d) (hbox : ∀ p ∈ X, 0 ≤ (f p : ℝ) ∧ (f p : ℝ) ≤ S)
    (hdiv : ∀ p ∈ X, ∀ q ∈ X, (d : ℤ) ∣ f p-f q) :
    (X.card : ℝ) ≤ S/(d : ℝ)+1 := by
  classical
  have hh := congruent_integer_set_card (X.image f) S hS d hd
    (by rintro x hx;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx;exact hbox p hp)
    (by
      intro x hx y hy
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
      exact hdiv p hp q hq)
  rwa [Finset.card_image_of_injOn hinj] at hh

theorem PrimitiveIntegerLine.slope_dvd_y_difference (l : PrimitiveIntegerLine)
    (p q : ℤ × ℤ) (hp : l.Contains p) (hq : l.Contains q) :
    (l.slope.natAbs : ℤ) ∣ p.2-q.2 := by
  have he : (l.denominator : ℤ)*(p.2-q.2) = l.slope*(p.1-q.1) := by
    unfold Contains at hp hq
    linear_combination hp-hq
  have hg : Int.gcd l.slope (l.denominator : ℤ) = 1 := by
    simpa [Int.gcd_def] using l.reduced.gcd_eq_one
  have hh : l.slope ∣ p.2-q.2 := Int.dvd_of_dvd_mul_right_of_gcd_one
    (by rw [he];exact dvd_mul_right _ _) hg
  simpa only [Int.natCast_natAbs,abs_dvd] using hh

theorem PrimitiveIntegerLine.y_injective (l : PrimitiveIntegerLine) (ha : l.slope ≠ 0)
    (X : Finset (ℤ × ℤ)) (hline : ∀ p ∈ X, l.Contains p) :
    Set.InjOn Prod.snd (X : Set (ℤ × ℤ)) := by
  intro p hp q hq he
  have hp' := hline p hp
  have hq' := hline q hq
  unfold Contains at hp' hq'
  have hm : l.slope*p.1 = l.slope*q.1 := by rw [he] at hp';omega
  exact Prod.ext (mul_left_cancel₀ ha hm) he

theorem PrimitiveIntegerLine.denominator_point_count (l : PrimitiveIntegerLine)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (X.card : ℝ) ≤ S/(l.denominator : ℝ)+1 :=
  coordinate_card_le_div X Prod.fst hinj S hS l.denominator l.denominator_pos
    (fun p hp => (hbox p hp).1)
    (fun p hp q hq => l.denominator_dvd_x_difference p q (hline p hp) (hline q hq))

theorem PrimitiveIntegerLine.slope_point_count (l : PrimitiveIntegerLine) (ha : l.slope ≠ 0)
    (X : Finset (ℤ × ℤ)) (S : ℝ) (hS : 0 ≤ S)
    (hbox : ∀ p ∈ X, InSquare S p) (hline : ∀ p ∈ X, l.Contains p) :
    (X.card : ℝ) ≤ S/(l.slope.natAbs : ℝ)+1 :=
  coordinate_card_le_div X Prod.snd (l.y_injective ha X hline) S hS l.slope.natAbs
    (Int.natAbs_pos.mpr ha) (fun p hp => (hbox p hp).2)
    (fun p hp q hq => l.slope_dvd_y_difference p q (hline p hp) (hline q hq))

end ErdosRichLine

end

end Erdos970

end OAI
