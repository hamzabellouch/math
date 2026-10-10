import OAI.NumberTheory.TwoPoint.Bounds.AffineTransfer
import OAI.NumberTheory.TwoPoint.Statements

namespace OAI

/-!
# Transfer from a positive gap to two arbitrary shifts

Cancellation for a positive gap gives cancellation for any two
distinct nonnegative shifts.
-/

open Filter

namespace TwoPointCorrelations

def UnshiftedCorrectedElliott : Prop :=
  ∀ f g : ℕ → ℂ, Multiplicative f → Multiplicative g →
    OneBounded f → OneBounded g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ h : ℕ, 0 < h →
      Tendsto (fun N : ℕ => correlationSum f g 0 h N / (N : ℂ)) atTop (nhds 0)

lemma residuePrefix_one (u : ℕ → ℂ) (b N : ℕ) :
    residuePrefix u 1 b N = ∑ n ∈ Finset.Icc 1 N, u n := by
  have hs : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [residuePrefix, hs, Nat.mod_one, ite_true]

theorem correlation_shift_zero (f g : ℕ → ℂ) (h b : ℕ)
    (hzero : Tendsto (fun N : ℕ => correlationSum f g 0 h N / (N : ℂ))
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => correlationSum f g b (b + h) N / (N : ℂ))
      atTop (nhds 0) := by
  have hp : Tendsto (fun N : ℕ =>
      residuePrefix (fun n => f n * g (n + h)) 1 b N / (N : ℂ)) atTop (nhds 0) := by
    simpa only [residuePrefix_one, correlationSum, Nat.add_zero] using hzero
  have ht := affine_mean_tendsto_zero (fun n => f n * g (n + h)) 1 b (by decide) hp
  simpa only [correlationSum, one_mul, Nat.add_assoc] using ht

theorem UnshiftedCorrectedElliott.binary (hcore : UnshiftedCorrectedElliott) :
    BinaryCorrectedElliott := by
  intro f g hf hg hfb hgb hnp h₁ h₂ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := correlation_shift_zero f g (h₂ - h₁) h₁
      (hcore f g hf hg hfb hgb hnp _ (Nat.sub_pos_of_lt hlt))
    simpa only [Nat.add_sub_of_le hlt.le] using h
  · have h := correlation_shift_zero g f (h₁ - h₂) h₂
      (hcore g f hg hf hgb hfb hnp.symm _ (Nat.sub_pos_of_lt hgt))
    simpa only [Nat.add_sub_of_le hgt.le, correlationSum, mul_comm] using h

end TwoPointCorrelations

end OAI
