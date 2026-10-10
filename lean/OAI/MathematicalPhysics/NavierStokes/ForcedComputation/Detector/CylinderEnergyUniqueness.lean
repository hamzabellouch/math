import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyEstimates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneEnergyLimit

namespace OAI

/-! The localized identity implies zero difference energy in the full
strong cylinder class. Every cutoff error is estimated here. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows MeasureTheory Set Filter
open scoped Topology

theorem localized_energy_derivative_upper (hI : CylinderLocalEnergyIdentity)
    {ν C BU BV BE BP : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (_hBU : 0 ≤ BU) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (_hBP : 0 ≤ BP)
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hcut : ∀ x, ‖fderiv ℝ (cylinderWeight n) x‖ ≤ C * ((n : ℝ)+1)⁻¹ ∧
      |scalarLaplacian (cylinderWeight n) x| ≤ C * ((n : ℝ)+1)⁻¹ ^ 2)
    (huB : ∀ x, ‖fderiv ℝ (fun y => u (t,y)) x‖ ≤ BU)
    (hvB : ∀ x, ‖v (t,x)‖ ≤ BV)
    (hE : differenceEnergy u v t ≤ BE) (hP : pressureDifferenceEnergy p q t ≤ BP) :
    ∃ e, HasDerivAt (localizedDifferenceEnergy u v n) e t ∧
      e ≤ (6 * BU) * localizedDifferenceEnergy u v n t +
        (ν * C * BE + C * BV * BE + 2 * C * (BP + BE)) * ((n : ℝ)+1)⁻¹ := by
  let μ := ((n : ℝ)+1)⁻¹
  have hμ : 0 ≤ μ := by dsimp [μ]; positivity
  have hμ1 : μ ≤ 1 := by
    change ((n : ℝ) + 1)⁻¹ ≤ 1
    apply (inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hμ2 : μ ^ 2 ≤ μ := by nlinarith
  have hInt := localizedDifferenceInteraction_bound hu hv ht.le n huB
  have hDiff := localizedDiffusionError_bound hu hv ht.le n (fun x => (hcut x).2)
  have hTr := localizedTransportError_bound (mul_nonneg hC hμ) hu hv ht.le n
    (fun x => (hcut x).1) hvB
  have hPr := localizedPressureError_bound (mul_nonneg hC hμ) hu hv ht.le n
    (fun x => (hcut x).1)
  have hDiff' : localizedDiffusionError u v n t ≤ C * μ * BE := by
    calc
      _ ≤ |localizedDiffusionError u v n t| := le_abs_self _
      _ ≤ (C * μ ^ 2) * differenceEnergy u v t := hDiff
      _ ≤ (C * μ ^ 2) * BE := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ C * μ * BE := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hμ2 hC) hBE
  have hTr' : localizedTransportError u v n t ≤ C * μ * BV * BE := by
    exact (le_abs_self _).trans (hTr.trans (mul_le_mul_of_nonneg_left hE (by positivity)))
  have hPr' : localizedPressureError u v p q n t ≤ C * μ * (BP + BE) :=
    (le_abs_self _).trans (hPr.trans
      (mul_le_mul_of_nonneg_left (add_le_add hP hE) (mul_nonneg hC hμ)))
  have hInt' : -localizedDifferenceInteraction u v n t ≤
      (3 * BU) * localizedDifferenceEnergy u v n t :=
    (neg_le_abs _).trans hInt
  refine ⟨_, hI ν hν f u v p q hu hv n t ht, ?_⟩
  have hD := localizedDifferenceDissipation_nonneg u v n t
  have hDis := mul_nonneg hν.le hD
  have hd := mul_le_mul_of_nonneg_left hDiff' hν.le
  nlinarith

theorem IsCylinderClassicalSolution.difference_energy_zero
    (hI : CylinderLocalEnergyIdentity) {ν : ℝ} (hν : 0 < ν)
    {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    {T : ℝ} (hT : 0 ≤ T) : differenceEnergy u v T = 0 := by
  obtain ⟨C, hC, hcut⟩ := cylinderWeight_derivative_bounds
  obtain ⟨AU, hAU⟩ := hu.bounded T hT
  obtain ⟨AV, hAV⟩ := hv.bounded T hT
  let BU := max 0 AU
  let BV := max 0 AV
  have hBU : 0 ≤ BU := le_max_left _ _
  have hBV : 0 ≤ BV := le_max_left _ _
  have huB (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) :
      ‖fderiv ℝ (fun y => u (t,y)) x‖ ≤ BU := by
    have hb := hAU t ht x
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hb.trans (le_max_right _ _))
  have hvB (t : ℝ) (ht : t ∈ Icc 0 T) (x : Space) : ‖v (t,x)‖ ≤ BV := by
    have hb := hAV t ht x
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hb.trans (le_max_right _ _))
  obtain ⟨BE, hBE, hE⟩ := hu.difference_energy_uniform hv hT
  obtain ⟨BP, hBP, hP⟩ := hu.pressure_difference_uniform hv hT
  let A := ν * C * BE + C * BV * BE + 2 * C * (BP + BE)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply zero_of_localized_energy_limit (C := 6 * BU)
    (E := localizedDifferenceEnergy u v) (ε := fun n => A * ((n : ℝ)+1)⁻¹) hT
  · intro n
    positivity
  · simpa only [one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A
  · exact fun n => localizedDifferenceEnergy_continuous hI hν hu hv hT n
  · exact localizedDifferenceEnergy_initial hu hv
  · exact fun n t _ => localizedDifferenceEnergy_nonneg u v n t
  · intro n t ht
    exact localized_energy_derivative_upper hI hν hC hBU hBV hBE hBP hu hv ht.1 n
      (hcut n) (huB t ⟨ht.1.le, ht.2.le⟩) (hvB t ⟨ht.1.le, ht.2.le⟩)
      (hE t ⟨ht.1.le, ht.2.le⟩) (hP t ⟨ht.1.le, ht.2.le⟩)
  · exact localizedDifferenceEnergy_limit hu hv hT

end ForcedComputation.VelocityDetector

end

end OAI
