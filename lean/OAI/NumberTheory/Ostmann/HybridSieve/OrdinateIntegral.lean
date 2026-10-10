import OAI.NumberTheory.Ostmann.HybridSieve.OrdinateDefs

namespace OAI

open MeasureTheory
open scoped Classical
namespace Ostmann.HybridSieve

lemma physicalDyadicSum_integral_scale (N : ℕ) (a : ℕ → ℂ) {Q : ℕ}
    (i : PrimitiveFamily Q) (T : ℝ) :
    (∫ t in -T..T, ‖physicalDyadicSum N a i t‖^2) =
      T*(∫ t in Set.Icc (-1:ℝ) 1, ‖dyadicPhaseSum N a i (T/(2*Real.pi)) t‖^2) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  simpa only [smul_eq_mul, mul_neg, mul_one, physicalDyadicSum_scaled] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun t => ‖physicalDyadicSum N a i t‖^2) (a := (-1:ℝ)) (b := 1) T).symm

theorem exists_physical_hybrid_integral_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (a : ℕ → ℂ) (T : ℝ), 0 < N → 0 < T →
      (∑ i : PrimitiveFamily Q, familyWeight i *
        (∫ t in -T..T, ‖physicalDyadicSum N a i t‖^2)) ≤
      C * ((N:ℝ)+T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ)) *
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_hybrid_integral_constant
  refine ⟨C*(2*Real.pi+1), mul_pos hC (by positivity), ?_⟩
  intro N Q a T hN hT
  have hraw := mul_le_mul_of_nonneg_left
    (hbound N Q a (T/(2*Real.pi)) hN (by positivity)) hT.le
  have hsum : (∑ i : PrimitiveFamily Q, familyWeight i *
      (∫ t in -T..T, ‖physicalDyadicSum N a i t‖^2)) =
      T*(∑ i : PrimitiveFamily Q, familyWeight i *
        (∫ t in Set.Icc (-1:ℝ) 1, ‖dyadicPhaseSum N a i (T/(2*Real.pi)) t‖^2)) := by
    simp_rw [physicalDyadicSum_integral_scale]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hHarm : 0 ≤ (harmonic (Q^2):ℝ) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · exact_mod_cast (harmonic_pos (pow_ne_zero 2 hQ)).le
  have hcoeff : 0 ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbase : 2*Real.pi*(N:ℝ)+T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ) ≤
      (2*Real.pi+1)*((N:ℝ)+T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ)) := by
    nlinarith [mul_nonneg (show 0 ≤ 2*Real.pi by positivity)
      (show 0 ≤ T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ) by positivity)]
  calc
    _ ≤ T*(C*((N:ℝ)/(T/(2*Real.pi))+1+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*
        ∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) := hraw
    _ = C*(2*Real.pi*(N:ℝ)+T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ))*
        (∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) := by
      field_simp
    _ ≤ C*((2*Real.pi+1)*((N:ℝ)+T+(Q:ℝ)^2*T*(harmonic (Q^2):ℝ)))*
        (∑ n ∈ Finset.Ioc N (2*N), ‖a n‖^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hC.le) hcoeff
    _ = _ := by ring

end Ostmann.HybridSieve

end OAI
