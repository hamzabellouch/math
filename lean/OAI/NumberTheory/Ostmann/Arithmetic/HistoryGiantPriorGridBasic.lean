import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothFreezing
import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletion

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion PrimeProgression PrimeCellReplacement
open scoped BigOperators

def giantPrimeCutoff (G : ℝ) : ℕ := ⌈Real.exp (G+1)⌉₊

def giantPrimeSupport (G : ℝ) : Finset ℕ :=
  logPrimeSupport (giantPrimeCutoff G) (G-1) (G+1)

theorem giantPrimeSupport_subset (G : ℝ) : giantPrimeSupport G ⊆ logCellPrimes G := by
  classical
  intro p hp
  obtain ⟨hn,hp,_,_⟩ := (mem_logPrimeSupport _ _ _ _).mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,hn⟩,hp⟩

theorem gridMean_eq_closedPrime_weight_sum (G : ℝ) (E : Finset ℕ) (F : ℕ → ℂ) :
    gridMean G E F = ∑ p ∈ giantPrimeSupport G,
      ((logCellWeight G p / logCellMass G E : ℝ) : ℂ) * F p := by
  classical
  unfold gridMean
  symm
  apply Finset.sum_subset (giantPrimeSupport_subset G)
  intro p hp hnot
  have hdata := Finset.mem_filter.mp hp
  have hn := (Finset.mem_Ioc.mp hdata.1).2
  have hz : smoothPartition (Real.log p-G)=0 := by
    by_contra hz
    have hs := smoothPartition_support_subset hz
    apply hnot
    exact (mem_logPrimeSupport _ _ _ _).mpr ⟨hn,hdata.2,by linarith [hs.1],by linarith [hs.2]⟩
  simp only [logCellWeight,hz,zero_div,Complex.ofReal_zero,zero_mul]

theorem gridMean_eq_closedPrime_sum (G : ℝ) (E : Finset ℕ) (F : ℕ → ℂ) :
    gridMean G E F = ∑ p ∈ giantPrimeSupport G,
      (((logCellMass G E*(p:ℝ))⁻¹ : ℝ) : ℂ) *
        ((smoothPartition (Real.log p-G) : ℂ) * F p) := by
  rw [gridMean_eq_closedPrime_weight_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : logCellWeight G p / logCellMass G E =
      (logCellMass G E*(p:ℝ))⁻¹*smoothPartition (Real.log p-G) := by
    simp only [logCellWeight,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,Complex.ofReal_mul,mul_assoc]

theorem gridMean_eq_closedPrime_subtype (G : ℝ) (E : Finset ℕ) (F : ℕ → ℂ) :
    gridMean G E F = ∑ p : {p : ℕ // p ∈ giantPrimeSupport G},
      (((logCellMass G E*(p.val:ℝ))⁻¹ : ℝ) : ℂ) *
        ((smoothPartition (Real.log p.val-G) : ℂ) * F p.val) := by
  rw [gridMean_eq_closedPrime_sum]
  exact (Finset.sum_coe_sort _ _).symm

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
