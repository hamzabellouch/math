import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeVertices
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ : ℕ}

lemma offset_abs_le (w : ClosedLine h ℓ) (K : ℝ)
    (hK : ∀ i, (w.label i : ℝ) ≤ K) (j : Fin (ℓ+1)) :
    |(w.offset j : ℝ)| ≤ (j.val : ℝ) * (h : ℝ) * K := by
  induction j using Fin.induction with
  | zero => simp [w.start_zero]
  | succ i ih =>
    have hs : (w.offset i.succ : ℝ) = (w.offset i.castSucc : ℝ) +
        (w.sign i : ℝ) * (h : ℝ) * (w.label i : ℝ) := by
      have hs := w.step i
      have hi : w.offset i.succ = w.offset i.castSucc + w.sign i * h * w.label i := by omega
      exact_mod_cast hi
    have ha : |(w.sign i : ℝ) * (h : ℝ) * (w.label i : ℝ)| = (h : ℝ) * (w.label i : ℝ) := by
      rcases w.sign_mem i with hsign | hsign <;> rw [hsign] <;>
        simp [abs_mul]
    calc
      _ ≤ |(w.offset i.castSucc : ℝ)| + |(w.sign i : ℝ) * (h : ℝ) * (w.label i : ℝ)| := by
        rw [hs]
        exact abs_add_le _ _
      _ ≤ (i.val : ℝ) * (h : ℝ) * K + (h : ℝ) * K := by
        rw [ha]
        exact add_le_add ih (mul_le_mul_of_nonneg_left (hK i) (Nat.cast_nonneg _))
      _ = _ := by simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; ring

lemma vertex_abs_le (w : ClosedLine h ℓ) (K : ℝ) (hK₀ : 0 ≤ K)
    (hK : ∀ i, (w.label i : ℝ) ≤ K) (v : ℤ) (hv : v ∈ treeVertices w) :
    |(v : ℝ)| ≤ (ℓ : ℝ) * (h : ℝ) * K := by
  obtain ⟨j,_,rfl⟩ := mem_image.mp hv
  apply (offset_abs_le w K hK j).trans
  have hj : (j.val : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg _)) hK₀

lemma line_difference_bound (w : ClosedLine h ℓ) (K : ℝ) (hK₀ : 0 ≤ K)
    (hK : ∀ i, (w.label i : ℝ) ≤ K) (v : ℤ) (hv : v ∈ treeVertices w)
    (u : ℤ) (hu : u ∈ treeVertices w) :
    ((u-v).natAbs : ℝ) ≤ 2 * (ℓ : ℝ) * (h : ℝ) * K := by
  have heq : ((u-v).natAbs : ℝ) = |(u : ℝ) - (v : ℝ)| := by
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  rw [heq]
  calc
    _ ≤ |(u : ℝ)| + |(v : ℝ)| := abs_sub _ _
    _ ≤ (ℓ : ℝ) * (h : ℝ) * K + (ℓ : ℝ) * (h : ℝ) * K :=
      add_le_add (vertex_abs_le w K hK₀ hK u hu) (vertex_abs_le w K hK₀ hK v hv)
    _ = _ := by ring

theorem source_line_difference_bound (w : ClosedLine h ℓ)
    (hlabels : ∀ i, w.label i ∈ D.members) (hτ : 0 ≤ τ)
    (hℓ : (ℓ : ℝ) ≤ 2 * B) (v : ℤ) (hv : v ∈ treeVertices w)
    (u : ℤ) (hu : u ∈ treeVertices w) :
    ((u-v).natAbs : ℝ) ≤ Real.exp ((C₀ + 4 * (h : ℝ) * τ) * B) := by
  have hk₀ : 0 ≤ τ * Real.exp (C₀*B) := mul_nonneg hτ (Real.exp_pos _).le
  have hk : ∀ i, (w.label i : ℝ) ≤ τ * Real.exp (C₀*B) := fun i =>
    (D.upper _ (hlabels i)).trans (mul_le_mul_of_nonneg_left D.H_upper hτ)
  apply (line_difference_bound w _ hk₀ hk v hv u hu).trans
  calc
    _ ≤ 4 * (h : ℝ) * τ * B * Real.exp (C₀*B) := by
      have ha := mul_le_mul_of_nonneg_right hℓ
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg h)) hk₀)
      nlinarith only [ha]
    _ ≤ Real.exp (4 * (h : ℝ) * τ * B) * Real.exp (C₀*B) := by
      have hx : 4 * (h : ℝ) * τ * B ≤ Real.exp (4 * (h : ℝ) * τ * B) := by
        have hh := Real.add_one_le_exp (4 * (h : ℝ) * τ * B)
        linarith
      exact mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
