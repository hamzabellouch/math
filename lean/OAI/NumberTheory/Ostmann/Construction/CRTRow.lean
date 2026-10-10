import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def unitMultiplyEquiv {n : ℕ} (u : (ZMod n)ˣ) : ZMod n ≃ ZMod n where
  toFun x := x * (u : ZMod n)
  invFun x := x * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]

def crtUnitEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcoprime : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (u : ∀ i, (ZMod (a i))ˣ) :
    ZMod (∏ i, a i) ≃ (∀ i, ZMod (a i)) :=
  (ZMod.prodEquivPi a hcoprime).toEquiv.trans
    (Equiv.piCongrRight fun i => unitMultiplyEquiv (u i))

def crtRow {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcoprime : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (u : ∀ i, (ZMod (a i))ˣ) (g : ∀ i, ZMod (a i) → ℂ)
    (t : ZMod (∏ i, a i)) : ℂ :=
  ∏ i, g i (crtUnitEquiv a hcoprime u t i)

theorem crtRow_sq_norm {ι : Type*} [Fintype ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (u : ∀ i, (ZMod (a i))ˣ) (g : ∀ i, ZMod (a i) → ℂ) :
    (∑ t, ‖crtRow a hcoprime u g t‖^2) =
      ∏ i, ∑ b, ‖g i b‖^2 := by
  classical
  simp only [crtRow, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∑ v : ∀ i, ZMod (a i), ∏ i, ‖g i (v i)‖^2 :=
      (crtUnitEquiv a hcoprime u).sum_comp (fun v => ∏ i, ‖g i (v i)‖^2)
    _ = _ := (Fintype.prod_sum (fun i b => ‖g i b‖^2)).symm

theorem crtRow_sq_norm_le {ι : Type*} [Fintype ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (u : ∀ i, (ZMod (a i))ˣ) (g : ∀ i, ZMod (a i) → ℂ)
    (hg : ∀ i, (∑ b, ‖g i b‖^2) ≤ (a i : ℝ)) :
    (∑ t, ‖crtRow a hcoprime u g t‖^2) ≤ (∏ i, a i : ℕ) := by
  rw [crtRow_sq_norm, Nat.cast_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · intro i hi
    exact hg i

end Ostmann.Construction

end

end OAI
