import OAI.Probability.ClassicalON.EdgeOperators

namespace OAI

universe uI uP uX

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {X : Type uX} {P : Type uP} {I : Type uI} [Fintype X] [Fintype P] [Fintype I]

theorem norm_sum_sq_le_card (f : I → ℂ) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card I:ℝ)*∑ i, ‖f i‖^2 := by
  calc _ ≤ (∑ i, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
       _ ≤ _ := by
          have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
            (s := Finset.univ) (r := fun i => ‖f i‖) (f := fun _ => 1)
            (g := fun i => ‖f i‖^2) (fun _ _ => by norm_num) (fun i _ => sq_nonneg _)
            (fun i _ => le_of_eq (one_mul _).symm)
          simpa using h

theorem SquareBound.mono {U : X → P → ℂ} {a b : ℝ}
    (ha : SquareBound U a) (hab : a^2 ≤ b^2) : SquareBound U b := by
  intro v
  exact (ha v).trans (mul_le_mul_of_nonneg_right hab (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem sum_by_fibers [DecidableEq I] (d : X → I) (f : X → ℝ) :
    (∑ x, f x) = ∑ i, ∑ x : {x // d x=i}, f x := by
  classical
  simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
    (Equiv.sum_comp (Equiv.sigmaFiberEquiv d) f).symm

theorem SquareBound.combine_directions (U : X → P → ℂ) (d : X → Bool) (a : ℝ)
    (h : ∀ m : Bool, SquareBound (fun (x : {x // d x=m}) p => U x p) a) :
    SquareBound U (2*a) := by
  intro v
  rw [sum_by_fibers d]
  calc _ ≤ ∑ _m : Bool, a^2*∑ p, ‖v p‖^2 :=
          Finset.sum_le_sum fun m _ => h m v
       _ ≤ (2*a)^2*∑ p, ‖v p‖^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
          have hs : 0 ≤ ∑ p : P, ‖v p‖^2 := Finset.sum_nonneg fun p _ => sq_nonneg ‖v p‖
          nlinarith [mul_nonneg (sq_nonneg a) hs]

theorem gram_groups_bound (T : I → X → X → ℂ) (C : ℝ)
    (h : ∀ i, (∑ x, ∑ y, ‖T i x y‖^2) ≤ C) :
    (∑ x, ∑ y, ‖∑ i, T i x y‖^2) ≤ (Fintype.card I:ℝ)^2*C := by
  calc _ ≤ ∑ x, ∑ y, (Fintype.card I:ℝ)*∑ i, ‖T i x y‖^2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => norm_sum_sq_le_card _
       _ = (Fintype.card I:ℝ)*∑ i, ∑ x, ∑ y, ‖T i x y‖^2 := by
          simp only [← Finset.mul_sum]
          congr 1
          calc (∑ x, ∑ y, ∑ i, ‖T i x y‖^2) = ∑ x, ∑ i, ∑ y, ‖T i x y‖^2 :=
                Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
               _ = _ := Finset.sum_comm
       _ ≤ (Fintype.card I:ℝ)*∑ _i : I, C := by gcongr with i; exact h i
       _ = _ := by simp; ring

end ClassicalON

end

end OAI
