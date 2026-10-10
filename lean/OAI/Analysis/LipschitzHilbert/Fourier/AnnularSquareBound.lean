import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPartitionIdentities
import Mathlib.Data.Int.Interval

namespace OAI

/-! The geometric annular cutoffs have a uniform finite square sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyLow_norm (s : ℝ) : ‖reassemblyLow s‖≤1 := by
  rw [reassemblyLow_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyLowBump.nonneg]
  exact reassemblyLowBump.le_one

theorem reassemblyOuter_norm (s : ℝ) : ‖reassemblyOuter s‖≤1 := by
  rw [reassemblyOuter_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg reassemblyOuterBump.nonneg]
  exact reassemblyOuterBump.le_one

theorem reassemblyDifference_norm (s : ℝ) : ‖reassemblyDifference s‖≤2 :=
  (norm_sub_le _ _).trans (by linarith only [reassemblyLow_norm ((16/27)*s),reassemblyLow_norm ((8/9)*s)])

theorem reassemblyPositive_norm_le (s : ℝ) : ‖reassemblyPositive s‖≤‖reassemblyDifference s‖ := by
  rw [reassemblyPositive_apply,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (reassemblyOuter_norm s)

theorem geometric_annuli_separated (j k : ℤ) (x : ℝ) (hjk : j+2≤k) :
    reassemblyDifference ((3/2:ℝ)^j*x)=0 ∨ reassemblyDifference ((3/2:ℝ)^k*x)=0 := by
  by_contra hn
  have hj : reassemblyDifference ((3/2:ℝ)^j*x)≠0 := fun h => hn (Or.inl h)
  have hk : reassemblyDifference ((3/2:ℝ)^k*x)≠0 := fun h => hn (Or.inr h)
  have hjlo : 9/8 < |(3/2:ℝ)^j*x| := lt_of_not_ge (fun h => hj (reassemblyDifference_small _ h))
  have hkhi : |(3/2:ℝ)^k*x|<117/64 := lt_of_not_ge (fun h => hk (reassemblyDifference_large _ h))
  have hpow : (3/2:ℝ)^j*(9/4)≤(3/2:ℝ)^k := by
    calc
      _ = (3/2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
  have hscale := mul_le_mul_of_nonneg_right hpow (abs_nonneg x)
  have habs (n : ℤ) : |(3/2:ℝ)^n*x|=(3/2:ℝ)^n*|x| := by
    rw [abs_mul,abs_of_pos (zpow_pos (by norm_num) _)]
  rw [habs j] at hjlo
  rw [habs k] at hkhi
  nlinarith only [hscale,hjlo,hkhi]

theorem reassemblyDifference_square_sum (I : Finset ℤ) (x : ℝ) :
    (∑ j∈I, ‖reassemblyDifference ((3/2:ℝ)^j*x)‖^2)≤12 := by
  classical
  let A := I.filter (fun j => reassemblyDifference ((3/2:ℝ)^j*x)≠0)
  have hAI : A⊆I := Finset.filter_subset _ _
  have heq : (∑ j∈I, ‖reassemblyDifference ((3/2:ℝ)^j*x)‖^2)=
      ∑ j∈A, ‖reassemblyDifference ((3/2:ℝ)^j*x)‖^2 := by
    symm
    apply Finset.sum_subset hAI
    intro j hj hjA
    have hz : reassemblyDifference ((3/2:ℝ)^j*x)=0 := by
      by_contra hn
      exact hjA (Finset.mem_filter.mpr ⟨hj,hn⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  rw [heq]
  have hcard : A.card≤3 := by
    by_cases hne : A.Nonempty
    · obtain ⟨j,hj⟩ := hne
      have hjnz := (Finset.mem_filter.mp hj).2
      have hsub : A⊆Finset.Icc (j-1) (j+1) := by
        intro k hk
        have hknz := (Finset.mem_filter.mp hk).2
        apply Finset.mem_Icc.mpr
        constructor
        · by_contra hn
          have hkj : k+2≤j := by omega
          exact (geometric_annuli_separated k j x hkj).elim hknz hjnz
        · by_contra hn
          have hjk : j+2≤k := by omega
          exact (geometric_annuli_separated j k x hjk).elim hjnz hknz
      apply (Finset.card_le_card hsub).trans
      rw [Int.card_Icc]
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
      omega
  calc
    _ ≤ ∑ j∈A, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [show (2:ℝ)^2=4 by norm_num] using
        pow_le_pow_left₀ (norm_nonneg _) (reassemblyDifference_norm ((3/2:ℝ)^j*x)) 2
    _ = (A.card:ℝ)*4 := by simp
    _ ≤ 12 := by exact_mod_cast (Nat.mul_le_mul_right 4 hcard)

theorem reassemblyPositive_square_sum (I : Finset ℤ) (x : ℝ) :
    (∑ j∈I, ‖reassemblyPositive ((3/2:ℝ)^j*x)‖^2)≤12 := by
  apply (Finset.sum_le_sum (fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (reassemblyPositive_norm_le ((3/2:ℝ)^j*x)) 2)).trans
  exact reassemblyDifference_square_sum I x

end LipschitzHilbert.PacketRepresentation

end

end OAI
