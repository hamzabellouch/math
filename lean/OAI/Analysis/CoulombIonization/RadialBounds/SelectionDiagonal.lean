import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FiniteBarrier

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma diagonal_of_eventually {P : ℕ → ℕ → Prop} (hP : ∀ k, ∀ᶠ n in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, P (φ k) k := by
  classical
  choose t ht using fun k => eventually_atTop.mp (hP k)
  let φ : ℕ → ℕ := Nat.rec (t 0) (fun k prev => max (prev+1) (t (k+1)))
  have hφstep (k) : φ k < φ (k+1) := by
    change φ k < max (φ k+1) (t (k+1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  refine ⟨φ,strictMono_nat_of_lt_succ hφstep,fun k => ht k (φ k) ?_⟩
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

lemma SelectedQuantumData.rough_lower {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hl : 1 ≤ l) (hτ : τ ≤ 1) (hB : 0 ≤ B) (hRl : R ≤ l) :
    -(2+64*volume.real (closedBall (0:TFSpace) R)) ≤ s^3*(Z-(N:ℝ)) := by
  have hh := d.opposite_charge hs (zero_lt_one.trans_le hl) hB hRl
  have hs3 : s^3 ≤ 1 := pow_le_one₀ hs.le hs1
  have hl2 : l⁻¹^2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (zero_lt_one.trans_le hl).le)
    ((inv_le_one₀ (zero_lt_one.trans_le hl)).mpr hl)
  have hv : 0 ≤ volume.real (closedBall (0:TFSpace) R) := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hl2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hv)
  nlinarith only [hh,hs3,hmul,hτ]

end CoulombBarrier

end

end OAI
