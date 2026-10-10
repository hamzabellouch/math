import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeProgression
open scoped BigOperators

def logPrimeSupport (N : ℕ) (lo hi : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (N+1)).filter fun p =>
    p.Prime ∧ lo ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ hi

@[simp] theorem mem_logPrimeSupport (N p : ℕ) (lo hi : ℝ) :
    p ∈ logPrimeSupport N lo hi ↔
      p ≤ N ∧ p.Prime ∧ lo ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ hi := by
  classical
  simp [logPrimeSupport]

def harmonicProgression (N M : ℕ) (a : ZMod M) (lo hi : ℝ) : ℝ :=
  ∑ p ∈ (logPrimeSupport N lo hi).filter (fun p : ℕ => (p:ZMod M)=a), (p:ℝ)⁻¹

def harmonicIntegral (M : ℕ) (lo hi : ℝ) : ℝ :=
  (Nat.totient M:ℝ)⁻¹ * ∫ t in lo..hi, (t:ℝ)⁻¹

def correctedIntegral (M : ℕ) (χa β lo hi : ℝ) : ℝ :=
  (Nat.totient M:ℝ)⁻¹ * ∫ t in lo..hi,
    (1-χa*Real.exp ((β-1)*t))/t

theorem sum_harmonicProgression (N M : ℕ) [NeZero M] (lo hi : ℝ) :
    (∑ a : ZMod M, harmonicProgression N M a lo hi) =
      ∑ p ∈ logPrimeSupport N lo hi, (p:ℝ)⁻¹ := by
  classical
  exact Finset.sum_fiberwise (logPrimeSupport N lo hi) (fun p => (p:ZMod M)) (fun p => (p:ℝ)⁻¹)

theorem harmonicProgression_nonneg (N M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    0 ≤ harmonicProgression N M a lo hi :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem deletion_error (S E : Finset ℕ) (w : ℕ → ℝ) {α : ℝ}
    (hα : 0 ≤ α) (hw : ∀ p ∈ S, 0 ≤ w p ∧ w p ≤ α) :
    0 ≤ (∑ p ∈ S, w p) - (∑ p ∈ S \ E, w p) ∧
      (∑ p ∈ S, w p) - (∑ p ∈ S \ E, w p) ≤ E.card*α := by
  classical
  have hsplit : (∑ p ∈ S, w p) = (∑ p ∈ S \ E, w p)+(∑ p ∈ S ∩ E, w p) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S E), Finset.sdiff_union_inter]
  rw [hsplit,add_sub_cancel_left]
  constructor
  · exact Finset.sum_nonneg fun p hp => (hw p (Finset.mem_inter.mp hp).1).1
  · calc
      _ ≤ ∑ _p ∈ S ∩ E, α := Finset.sum_le_sum fun p hp =>
        (hw p (Finset.mem_inter.mp hp).1).2
      _ = (S ∩ E).card*α := by simp
      _ ≤ E.card*α := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=S) (s₂:=E))) hα

end Ostmann.Arithmetic.PrimeProgression

end

end OAI
