import OAI.MeasureTheory.Falconer.Estimates.FiniteTripleCounting

namespace OAI

/-! # Three-dimensional finite Loomis--Whitney counting -/

namespace Falconer
open scoped BigOperators
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem finite_loomis_whitney_three (S : Finset (X × Y × Z)) :
    (S.card : ℝ)^2 ≤
      ((S.image (fun p => (p.1,p.2.1))).card : ℝ)*
      ((S.image (fun p => (p.2.1,p.2.2))).card : ℝ)*
      ((S.image (fun p => (p.2.2,p.1))).card : ℝ) := by
  classical
  let A := S.image (fun p => (p.1,p.2.1))
  let B := S.image (fun p => (p.2.1,p.2.2))
  let C := S.image (fun p => (p.2.2,p.1))
  let f : X → Y → ℝ := fun x y => if (x,y) ∈ A then 1 else 0
  let g : Y → Z → ℝ := fun y z => if (y,z) ∈ B then 1 else 0
  let h : Z → X → ℝ := fun z x => if (z,x) ∈ C then 1 else 0
  have hpoint (p : X × Y × Z) :
      (if p ∈ S then (1:ℝ) else 0) ≤ f p.1 p.2.1*g p.2.1 p.2.2*h p.2.2 p.1 := by
    by_cases hp : p ∈ S
    · have ha : (p.1,p.2.1) ∈ A := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      have hb : (p.2.1,p.2.2) ∈ B := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      have hc : (p.2.2,p.1) ∈ C := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      simp only [hp,ite_true,f,g,h,ha,hb,hc,one_mul,le_refl]
    · simp only [hp,ite_false]
      dsimp [f,g,h]
      positivity
  have hcount : (S.card:ℝ) ≤ ∑ x, ∑ y, ∑ z, f x y*g y z*h z x := by
    calc
      _ = ∑ p : X × Y × Z, if p ∈ S then (1:ℝ) else 0 := by simp
      _ ≤ ∑ p : X × Y × Z, f p.1 p.2.1*g p.2.1 p.2.2*h p.2.2 p.1 :=
        Finset.sum_le_sum (fun p _ => hpoint p)
      _ = _ := by simp only [Fintype.sum_prod_type]
  have ha : (∑ x, ∑ y, (f x y)^2) = (A.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : X × Y => (f p.1 p.2)^2)]
    simp [f]
  have hb : (∑ y, ∑ z, (g y z)^2) = (B.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : Y × Z => (g p.1 p.2)^2)]
    simp [g]
  have hc : (∑ z, ∑ x, (h z x)^2) = (C.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : Z × X => (h p.1 p.2)^2)]
    simp [h]
  have ht := finite_triangle_square_bound f g h
  rw [ha,hb,hc] at ht
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2).trans ht

end Falconer

end OAI
