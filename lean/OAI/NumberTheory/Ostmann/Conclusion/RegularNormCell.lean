import OAI.NumberTheory.Ostmann.Conclusion.RegularNormTestAP
import OAI.NumberTheory.Ostmann.Construction.GiantCellPriorIdentity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Arithmetic.PrimeCellReplacement Ostmann.Arithmetic.PrimeProgression
open Ostmann.Construction

theorem logCellPrior_nonnegative_test_le (c : ℝ) (hZ : 0 < logCellMass c ∅)
    (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (logCellPrior c ∅ hZ).mean (fun p => f p) ≤
      (∑ p ∈ logPrimeSupport ⌈Real.exp (c+1)⌉₊ (c-1) c,
        (logCellMass c ∅*(p : ℝ))⁻¹*f p)+
      (∑ p ∈ logPrimeSupport ⌈Real.exp (c+1)⌉₊ c (c+1),
        (logCellMass c ∅*(p : ℝ))⁻¹*f p) := by
  classical
  let N := ⌈Real.exp (c+1)⌉₊
  let P := logCellPrimes c
  let A := logPrimeSupport N (c-1) c
  let B := logPrimeSupport N c (c+1)
  have hA : A ⊆ P := by
    intro p hp
    obtain ⟨hpN,hp,_,_⟩ := (mem_logPrimeSupport _ _ _ _).mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,hpN⟩,hp⟩
  have hB : B ⊆ P := by
    intro p hp
    obtain ⟨hpN,hp,_,_⟩ := (mem_logPrimeSupport _ _ _ _).mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,hpN⟩,hp⟩
  have hpoint (p : ℕ) (hpP : p ∈ P) :
      logCellWeight c p/logCellMass c ∅*f p ≤
        (if p ∈ A then (logCellMass c ∅*(p : ℝ))⁻¹*f p else 0)+
        (if p ∈ B then (logCellMass c ∅*(p : ℝ))⁻¹*f p else 0) := by
    have hfp := hf p
    have hnonneg : 0 ≤ (logCellMass c ∅*(p : ℝ))⁻¹*f p := by positivity
    by_cases hw : logCellWeight c p=0
    · simp only [hw,zero_div,zero_mul]
      positivity
    obtain ⟨hpI,hp⟩ := Finset.mem_filter.mp hpP
    have hpN := (Finset.mem_Ioc.mp hpI).2
    have hφ : Ostmann.smoothPartition (Real.log (p : ℝ)-c) ≠ 0 := by
      intro he
      apply hw
      simp only [logCellWeight,he,zero_div]
    have hsupport := Ostmann.smoothPartition_support_subset hφ
    have hweight : logCellWeight c p ≤ 1/(p : ℝ) :=
      div_le_div_of_nonneg_right (Ostmann.smoothPartition_le_one _) (Nat.cast_nonneg p)
    have hcore := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hweight hZ.le) (hf p)
    have he : (1/(p : ℝ))/logCellMass c ∅ = (logCellMass c ∅*(p : ℝ))⁻¹ := by
      simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
    rw [he] at hcore
    by_cases hpc : Real.log (p : ℝ) ≤ c
    · have hpA : p ∈ A := (mem_logPrimeSupport _ _ _ _).mpr ⟨hpN,hp,by linarith [hsupport.1],hpc⟩
      rw [ite_eq_left hpA]
      exact hcore.trans (le_add_of_nonneg_right (by positivity))
    · have hpB : p ∈ B := (mem_logPrimeSupport _ _ _ _).mpr ⟨hpN,hp,by linarith,by linarith [hsupport.2]⟩
      rw [ite_eq_left hpB]
      exact hcore.trans (le_add_of_nonneg_left (by positivity))
  unfold FinitePrior.mean
  simp_rw [logCellPrior_mass_weight]
  have hs : (∑ p : LogCellSample c ∅, logCellWeight c p/logCellMass c ∅*f p) =
      ∑ p ∈ P, logCellWeight c p/logCellMass c ∅*f p := by
    simpa only [Finset.sdiff_empty] using Finset.sum_coe_sort (logCellPrimes c \ ∅)
      (fun p => logCellWeight c p/logCellMass c ∅*f p)
  rw [hs]
  have hh := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hA,Finset.inter_eq_right.mpr hB] at hh
  exact hh

end Ostmann.Conclusion

end

end OAI
