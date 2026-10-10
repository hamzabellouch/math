import OAI.NumberTheory.Ostmann.Construction.GiantEmpirical
import OAI.NumberTheory.Ostmann.Construction.LogCellPrior
import OAI.NumberTheory.Ostmann.Construction.LogCellReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem logCellWeight_zero_not_mem (c : ℝ) {p : ℕ} (hp : Nat.Prime p)
    (hn : p∉logCellPrimes c) : logCellWeight c p=0 := by
  have hbound : ⌈Real.exp (c+1)⌉₊<p := by
    by_contra h
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,by omega⟩,hp⟩
  apply logCellWeight_zero_above
  exact (Nat.floor_le_ceil _).trans_lt hbound

theorem logCellPrior_mass_weight (c : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass c E)
    (q : LogCellSample c E) :
    (logCellPrior c E hZ).mass q=logCellWeight c q/logCellMass c E := by
  change logCellWeight c q/(∑r : LogCellSample c E,logCellWeight c r)=_
  rw [logCell_sample_sum]

theorem logCellPrior_mean_indicator (c : ℝ) (hZ : 0<logCellMass c ∅)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (f : ℕ → ℝ) :
    (logCellPrior c ∅ hZ).mean (fun q => if (q:ℕ)∈P then f q else 0) =
      (∑p∈P,logCellWeight c p*f p)/logCellMass c ∅ := by
  classical
  unfold FinitePrior.mean
  simp_rw [logCellPrior_mass_weight]
  calc
    _ = (∑q : LogCellSample c ∅,if (q:ℕ)∈P then logCellWeight c q*f q else 0)/logCellMass c ∅ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqP : (q:ℕ)∈P <;> simp only [hqP,ite_true,ite_false,mul_zero,zero_div]
      ring
    _ = (∑q∈logCellPrimes c,if q∈P then logCellWeight c q*f q else 0)/logCellMass c ∅ := by
      congr 1
      simpa only [Finset.sdiff_empty] using Finset.sum_coe_sort (logCellPrimes c\∅)
        (fun q => if q∈P then logCellWeight c q*f q else 0)
    _ = _ := by
      congr 1
      rw [Finset.sum_ite_mem]
      apply Finset.sum_subset Finset.inter_subset_right
      intro p hp hnot
      have hn : p∉logCellPrimes c := fun h => hnot (Finset.mem_inter.mpr ⟨h,hp⟩)
      rw [logCellWeight_zero_not_mem c (hP p hp) hn,zero_mul]

theorem giant_cell_prior_mean (d : Decomposition) (X : ℕ) (c : ℝ)
    (hZ : 0<logCellMass c ∅) (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) :
    (logCellPrior c ∅ hZ).mean
      (fun q => if (q:ℕ)∈P then giantEmpiricalMean d X q else 0) =
      (∑p∈P,logCellWeight c p*giantEmpiricalMean d X p)/logCellMass c ∅ :=
  logCellPrior_mean_indicator c hZ P hP _

end Ostmann.Construction

end

end OAI
