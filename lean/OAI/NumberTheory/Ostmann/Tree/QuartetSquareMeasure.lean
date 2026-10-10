import OAI.NumberTheory.Ostmann.Tree.DensityDomination

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open scoped BigOperators
open Density
variable {F : Type*} [Field F] [Fintype F]
local instance : DecidableEq F := Classical.decEq F

theorem square_coset_fiber_card (K y : Fˣ) :
    (Finset.univ.filter (fun z : Fˣ => K*z^2=y)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun z : Fˣ => K*z^2=y)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hx' : K*x^2=y := (Finset.mem_filter.mp hx).2
    apply le_trans (Finset.card_le_card (t := {x,-x}) ?_) Finset.card_le_two
    intro z hz
    have hz' : K*z^2=y := (Finset.mem_filter.mp hz).2
    have he : z^2=x^2 := mul_left_cancel (hz'.trans hx'.symm)
    rcases Units.sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h <;> simp [h]
  · exact (show S.card ≤ 2 by simp [Finset.not_nonempty_iff_eq_empty.mp hs])

theorem square_average_domination (K : Fˣ) (H : Fˣ → ℝ) (hH : ∀ y, 0 ≤ H y) :
    average (fun z : Fˣ => H (K*z^2)) ≤ 2*average H := by
  have hf : ∀ y, (Finset.univ.filter (fun z : Fˣ => some (K*z^2)=some y)).card ≤ 2 := by
    intro y
    simpa only [Option.some.injEq] using square_coset_fiber_card K y
  have hsum := sum_integrate_le (fun z : Fˣ => some (K*z^2)) 2 hf H hH
  simp only [integrate, Nat.cast_ofNat] at hsum
  unfold average
  calc
    _ ≤ (Fintype.card Fˣ:ℝ)⁻¹*(2*∑ y,H y) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by ring

theorem average_mono {A : Type*} [Fintype A] (f g : A → ℝ)
    (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => h x))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem average_nonneg {A : Type*} [Fintype A] (f : A → ℝ) (h : ∀ x, 0 ≤ f x) :
    0 ≤ average f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun x _ => h x))

theorem average_const_mul {A : Type*} [Fintype A] (c : ℝ) (f : A → ℝ) :
    average (fun x => c*f x) = c*average f := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem independent_square_domination (K L : Fˣ) (H : Fˣ → Fˣ → ℝ)
    (hH : ∀ x y, 0 ≤ H x y) :
    average (fun x : Fˣ => average (fun y : Fˣ => H (K*x^2) (L*y^2))) ≤
      4*average (fun x : Fˣ => average (fun y : Fˣ => H x y)) := by
  calc
    _ ≤ average (fun x : Fˣ => 2*average (fun y : Fˣ => H (K*x^2) y)) := by
      apply average_mono
      intro x
      exact square_average_domination L (H (K*x^2)) (hH (K*x^2))
    _ = 2*average (fun x : Fˣ => average (fun y : Fˣ => H (K*x^2) y)) :=
      average_const_mul _ _
    _ ≤ 2*(2*average (fun x : Fˣ => average (fun y : Fˣ => H x y))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact square_average_domination K (fun x => average (H x))
        (fun x => average_nonneg (H x) (hH x))
    _ = _ := by ring

end
end Ostmann.Tree.Quartet

end OAI
