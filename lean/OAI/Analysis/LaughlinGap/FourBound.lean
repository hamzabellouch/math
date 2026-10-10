import Mathlib
import OAI.Analysis.LaughlinGap.FourBoundCore

namespace OAI

/-! Four Bound. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

lemma four_comparison_summed {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (ε : ℝ) (ρ : Fin 23 → ℝ)
    (hQb : ∀ d : Fin 23,
      -(ρ d) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy (d.val+1) => fourAnnihilator Q (d.val+1) (d.val+1) r.val.val)
          (fourComparison rows ε Q (d.val+1))) :
    -(24*∑ d, ρ d) • physicalHamiltonian Q ≤
      retainedFourTarget Q - ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowFour (by omega) (rows r)) +
      ε • (((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1)) := by
  have hb := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Fin 23))) =>
    fourAverage_lower hQ (fourComparison rows ε Q (d.val+1)) (ρ d) (hQb d))
  simpa only [← Finset.smul_sum,← Finset.sum_smul,Finset.sum_neg_distrib,
    ← Finset.mul_sum,fourComparison_difference hQ] using hb

lemma rearrange_comparison {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
    {x y e r : A} (h : -r ≤ y-x+e) : x ≤ y+e+r := by
  calc
    x = -r+(x+r) := by abel
    _ ≤ (y-x+e)+(x+r) := add_le_add h (le_refl _)
    _ = y+e+r := by abel

lemma four_comparison_pointwise {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε) (ρ : Fin 23 → ℝ)
    (hQb : ∀ d : Fin 23,
      -(ρ d) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy (d.val+1) => fourAnnihilator Q (d.val+1) (d.val+1) r.val.val)
          (fourComparison rows ε Q (d.val+1))) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
      (∑ r, rowFour (by omega) (rows r)) ≤
        fourTarget Q + (1222*ε+24*∑ d, ρ d) • physicalHamiltonian Q := by
  have hb := four_comparison_summed hQ rows ε ρ hQb
  rw [neg_smul] at hb
  have hh := rearrange_comparison hb
  have he := smul_le_smul_of_nonneg_left (fourAllowance_le hQ) hε
  have ht := add_le_add (retainedFourTarget_le hQ) he
  have h := add_le_add ht (le_refl ((24*∑ d, ρ d) • physicalHamiltonian Q))
  apply hh.trans
  convert h using 1
  rw [smul_smul,add_assoc,← add_smul,mul_comm ε]

theorem four_comparison_of_certificates (rows : ι → RowData) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ∀ d : Fin 23, FourCertificate rows ε (d.val+1) (by omega)) :
    ∃ R : ℕ → ℝ, (∀ Q, 0 ≤ R Q) ∧ Tendsto R atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, ∀ hQ : 24 ≤ Q,
        ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
          (∑ r, rowFour (by omega) (rows r)) ≤
            fourTarget Q + (1222*ε+R Q) • physicalHamiltonian Q := by
  classical
  choose ρ hpos hlim hbound using (fun d : Fin 23 => four_local_transfer rows ε (by omega) (hc d))
  refine ⟨fun Q => 24*∑ d, ρ d Q,fun Q => mul_nonneg (by norm_num) (Finset.sum_nonneg (fun d _ => hpos d Q)),?_,?_⟩
  · simpa using (tendsto_finsetSum Finset.univ (fun d _ => hlim d)).const_mul 24
  · filter_upwards [eventually_all.mpr hbound] with Q hQb
    intro hQ
    exact four_comparison_pointwise hQ rows ε hε (fun d => ρ d Q) (fun d => hQb d hQ)

end LaughlinGap.RealOccupation

end

end OAI
