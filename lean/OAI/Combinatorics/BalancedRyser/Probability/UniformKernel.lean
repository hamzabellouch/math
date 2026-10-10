import Mathlib

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace UniformKernel

open Finset

variable {U V W : Type*} [Fintype U] [Fintype V]

noncomputable def fiberMass (κ : U → V → W → ℝ) (v : V) (w : W) : ℝ :=
  (∑ u, κ u v w) / ((Fintype.card U : ℝ) * Fintype.card V)

theorem fiberMass_le [Nonempty U] [Nonempty V]
    (κ : U → V → W → ℝ) (b : ℝ)
    (hκ : ∀ u v w, κ u v w ≤ b) (v : V) (w : W) :
    fiberMass κ v w ≤ b / Fintype.card V := by
  have hU : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  unfold fiberMass
  apply (div_le_iff₀ (mul_pos hU hV)).2
  have hs : (∑ u, κ u v w) ≤ (Fintype.card U : ℝ) * b := by
    calc
      (∑ u, κ u v w) ≤ ∑ _u : U, b := sum_le_sum (fun u _ => hκ u v w)
      _ = (Fintype.card U : ℝ) * b := by simp
  calc
    (∑ u, κ u v w) ≤ (Fintype.card U : ℝ) * b := hs
    _ = b / (Fintype.card V : ℝ) *
        ((Fintype.card U : ℝ) * Fintype.card V) := by field_simp

theorem fiberMass_nonneg (κ : U → V → W → ℝ)
    (hκ : ∀ u v w, 0 ≤ κ u v w) (v : V) (w : W) :
    0 ≤ fiberMass κ v w := by
  unfold fiberMass
  exact div_nonneg (sum_nonneg (fun u _ => hκ u v w)) (by positivity)

theorem assignmentMass_le [Nonempty U] [Nonempty V]
    (κ : U → V → W → ℝ) (b : ℝ)
    (hκ : ∀ u v w, κ u v w ≤ b) (A : Finset (V × W)) :
    ∑ a ∈ A, fiberMass κ a.1 a.2 ≤
      (A.card : ℝ) * b / Fintype.card V := by
  calc
    (∑ a ∈ A, fiberMass κ a.1 a.2) ≤
        ∑ _a ∈ A, b / (Fintype.card V : ℝ) :=
      sum_le_sum (fun a _ => fiberMass_le κ b hκ a.1 a.2)
    _ = (A.card : ℝ) * b / Fintype.card V := by simp; ring

theorem conditional_assignmentMass_le [Nonempty U] [Nonempty V]
    (κ : U → V → W → ℝ) (b a₀ success : ℝ)
    (hκ₀ : ∀ u v w, 0 ≤ κ u v w)
    (hκ : ∀ u v w, κ u v w ≤ b)
    (ha₀ : 0 < a₀) (hsuccess : a₀ ≤ success) (A : Finset (V × W)) :
    (∑ a ∈ A, fiberMass κ a.1 a.2) / success ≤
      (A.card : ℝ) * b / ((Fintype.card V : ℝ) * a₀) := by
  have hmass : 0 ≤ ∑ a ∈ A, fiberMass κ a.1 a.2 :=
    sum_nonneg (fun a _ => fiberMass_nonneg κ hκ₀ a.1 a.2)
  calc
    (∑ a ∈ A, fiberMass κ a.1 a.2) / success ≤
        (∑ a ∈ A, fiberMass κ a.1 a.2) / a₀ :=
      div_le_div_of_nonneg_left hmass ha₀ hsuccess
    _ ≤ ((A.card : ℝ) * b / Fintype.card V) / a₀ :=
      div_le_div_of_nonneg_right (assignmentMass_le κ b hκ A) ha₀.le
    _ = (A.card : ℝ) * b / ((Fintype.card V : ℝ) * a₀) := by ring

end UniformKernel
end Balanced

namespace Balanced.UniformKernel
open scoped _root_.Balanced

theorem offsetAverage_le {q n : ℕ} (hq : 0 < q)
    {W : Type*} (κ : (Fin n → Fin q) → (Fin n → Fin q) → W → ℝ)
    (b : ℝ) (hκ : ∀ u v w, κ u v w ≤ b)
    (v : Fin n → Fin q) (w : W) :
    (∑ u, κ u v w) / (q : ℝ) ^ (2 * n) ≤ b / (q : ℝ) ^ n := by
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have h := fiberMass_le κ b hκ v w
  simpa only [fiberMass, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    two_mul, pow_add] using h

theorem totalMass_le_one {U V W : Type*}
    [Fintype U] [Fintype V] [Fintype W] [Nonempty U] [Nonempty V]
    (κ : U → V → W → ℝ) (hκ : ∀ u v, ∑ w, κ u v w ≤ 1) :
    ∑ v, ∑ w, fiberMass κ v w ≤ 1 := by
  have hU : (0 : ℝ) < Fintype.card U := by
    exact_mod_cast Fintype.card_pos
  have hV : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  simp only [fiberMass, ← Finset.sum_div]
  apply (div_le_iff₀ (mul_pos hU hV)).2
  calc
    (∑ v, ∑ w, ∑ u, κ u v w) = ∑ v, ∑ u, ∑ w, κ u v w := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_comm
    _ ≤ ∑ _v : V, ∑ _u : U, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun u _ => hκ u v))
    _ = 1 * ((Fintype.card U : ℝ) * Fintype.card V) := by simp; ring

end Balanced.UniformKernel

end OAI
