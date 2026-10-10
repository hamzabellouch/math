import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileTemperature

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem atomicScalarValue_hasDerivAt_temperature {k : ℕ} (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q ∈ admissibleQuantiles k) :
    HasDerivAt (fun b => atomicScalarValue k b Q)
      (β*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*quantileOverlapMean k β Q j)) β := by
  let I := ∫ s in Set.Icc (0:ℝ) 1, s*quantileCDF k Q s
  have he (b : ℝ) : atomicScalarValue k b Q = atomicParisi k b Q+(b^2/2)*I := by
    dsimp only [atomicParisi,I]
    ring
  simp_rw [he]
  have hP := atomicParisi_hasDerivAt_temperature β Q hQ
  have hI := (((hasDerivAt_id β).pow 2).div_const 2).mul_const I
  apply (hP.add hI).congr_deriv
  dsimp only [I,id_eq]
  rw [quantileCDF_integral k Q hQ.2]
  ring

theorem atomicScalarValue_hasDerivAt_squaredTemperature {k : ℕ} {b : ℝ} (hb : 0 < b)
    (Q : Fin (k+1) → ℝ) (hQ : Q ∈ admissibleQuantiles k) :
    HasDerivAt (fun c => atomicScalarValue k (Real.sqrt c) Q)
      ((1/2:ℝ)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*
        quantileOverlapMean k (Real.sqrt b) Q j)) b := by
  have H := (atomicScalarValue_hasDerivAt_temperature (Real.sqrt b) Q hQ).comp b
    ((hasDerivAt_id b).sqrt hb.ne')
  apply H.congr_deriv
  dsimp only [id_eq]
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  field_simp

theorem atomicScalarValue_lipschitz_squaredTemperature {k : ℕ}
    (Q : Fin (k+1) → ℝ) (hQ : Q ∈ admissibleQuantiles k) :
    LipschitzOnWith (1/2) (fun b : ℝ => atomicScalarValue k (Real.sqrt b) Q)
      (Set.Ioi 0) := by
  apply (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun b hb => (atomicScalarValue_hasDerivAt_squaredTemperature hb Q hQ).hasDerivWithinAt)
  intro b hb
  let S := ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*quantileOverlapMean k (Real.sqrt b) Q j
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (by positivity) (hQ.2 j).1)
      (quantileOverlapMean_bounds k (Real.sqrt b) Q j).1
  have hS1 : S ≤ 1 := by
    calc
      S ≤ ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        have hq := hQ.2 j
        have hr := quantileOverlapMean_bounds k (Real.sqrt b) Q j
        calc
          _ ≤ ((k+1:ℕ):ℝ)⁻¹*Q j :=
            mul_le_of_le_one_right (mul_nonneg (by positivity) hq.1) hr.2
          _ ≤ ((k+1:ℕ):ℝ)⁻¹ := mul_le_of_le_one_right (by positivity) hq.2
      _ = 1 := uniformAtom_sum k
  change ‖(1/2:ℝ)*(1-S)‖ ≤ (1/2:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  linarith

end SK.Analytic

end
end

end

end OAI
