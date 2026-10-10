import OAI.Geometry.RCD.Sobolev.LocalEnergyMeasure

namespace OAI

/-! # Integrating a uniform rescaled gradient bound -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem rescaled_local_energy_bound (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (w : SobolevSpace μ hQ) {A U : Set X} (hAU : A⊆U) (hfin : μ U≠⊤)
    (hpos : 0<μ.real U) {r M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐ x ∂μ.restrict A, r^2*localGamma μ hQ w w x≤M) :
    (r^2/μ.real U)*(∫ x in A, localGamma μ hQ w w x ∂μ)≤M := by
  let : IsFiniteMeasure (μ.restrict A) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (lt_of_le_of_lt (measure_mono hAU) hfin.lt_top)⟩
  have hi := integral_mono_ae ((localGamma_memL1 μ hQ w w).restrict.const_mul (r^2))
    (integrable_const M) hb
  rw [integral_const_mul,integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hi
  have hm : μ.real A≤μ.real U := measureReal_mono hAU hfin
  have hu : r^2*(∫ x in A, localGamma μ hQ w w x ∂μ)≤μ.real U*M :=
    hi.trans (mul_le_mul_of_nonneg_right hm hM)
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hu)

end RegularPointCoordinates

end

end OAI
