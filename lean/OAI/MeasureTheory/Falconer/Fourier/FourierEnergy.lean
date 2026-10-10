import OAI.MeasureTheory.Falconer.Fourier.FourierLebesgue
import OAI.MeasureTheory.Falconer.Fourier.MellinGaussian

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def rieszEnergyOn (μ : Measure V) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : V × V, (edist z.1 z.2)^(-u) ∂μ.prod μ

noncomputable def gaussianQuadraticOn (μ : Measure V) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : V × V, ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2))) ∂μ.prod μ

noncomputable def sourceEnergyConstant (n u : ℝ) : ℝ :=
  (Real.pi^(u/2)/Real.Gamma (u/2)) *
    ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2))

theorem sourceEnergyConstant_pos {n u : ℝ} (hu : 0 < u) (hun : u < n) :
    0 < sourceEnergyConstant n u := by
  unfold sourceEnergyConstant
  apply mul_pos
  · exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos (by linarith))

theorem rieszEnergyOn_gaussian_mixture (μ : Measure V) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    rieszEnergyOn μ u = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a := by
  let F : ℝ → V × V → ℝ≥0∞ := fun a z => ENNReal.ofReal (a^(u/2-1)) *
    ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
  calc
    rieszEnergyOn μ u = ∫⁻ z : V × V,
        ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
          (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ := by
      apply lintegral_congr
      intro z
      rw [edist_dist, dist_eq_norm]
      exact source_kernel_gaussian_mixture_all (norm_nonneg _) hu
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ z : V × V, (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ∫⁻ z : V × V, F a z ∂μ.prod μ := by
      congr 1
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (V × V) × ℝ => F z.2 z.1) := by
        dsimp [F]
        fun_prop
      exact hm.aemeasurable
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro a
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem source_fourier_energy_identity
    (μ : Measure V) [IsFiniteMeasure μ] {u : ℝ}
    (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn μ u = ENNReal.ofReal (sourceEnergyConstant (Module.finrank ℝ V) u) *
      ∫⁻ ξ : V, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-Module.finrank ℝ V)) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by exact_mod_cast hu.trans hun)
  let n : ℝ := Module.finrank ℝ V
  let A : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (a^(u/2-1)) * ENNReal.ofReal (a^(-n/2))
  let G : ℝ → V → ℝ≥0∞ := fun a ξ =>
    ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))
  let H : V → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖sourceFourier μ ξ‖^2)
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2))
  have hscale : (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a) =
      ∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    rw [gaussianQuadraticOn, source_scaled_gaussian_lintegral μ ha, ← mul_assoc]
    exact (lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm.trans
        (lintegral_congr (fun ξ => by simp only [A,G,H,n,mul_assoc]))
  have hswap : (∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ) =
      ∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ := by
    apply lintegral_lintegral_swap
    have hm : Measurable (fun z : ℝ × V => A z.1 * G z.1 z.2 * H z.2) := by
      dsimp [A,G,H,sourceFourier]
      fun_prop
    exact hm.aemeasurable
  have hweight : (∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ) =
      D * ∫⁻ ξ : V, H ξ * ENNReal.ofReal (‖ξ‖^(u-n)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    have hne : ∀ᵐ ξ : V ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with ξ hξ
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    change (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))) * H ξ = _
    rw [source_weight_gaussian_mixture (norm_pos_iff.mpr hξ) hun]
    dsimp [D,n]
    ac_rfl
  rw [rieszEnergyOn_gaussian_mixture μ hu,hscale,hswap,hweight,← mul_assoc]
  rw [sourceEnergyConstant,ENNReal.ofReal_mul (by positivity)]

theorem rieszEnergyOn_plane (μ : Measure Plane) [IsFiniteMeasure μ] (u : ℝ) :
    rieszEnergyOn μ u = rieszEnergy μ u := (rieszEnergy_eq_prod μ u).symm

theorem planar_fourier_energy_identity (μ : Measure Plane) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hu2 : u < 2) :
    rieszEnergy μ u = ENNReal.ofReal (sourceEnergyConstant 2 u) *
      ∫⁻ ξ : Plane, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-2)) := by
  have hn : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have h := source_fourier_energy_identity μ hu (by simpa [hn] using hu2)
  simpa only [hn, Nat.cast_ofNat, rieszEnergyOn_plane] using h

theorem line_fourier_energy_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    rieszEnergyOn μ u = ENNReal.ofReal (sourceEnergyConstant 1 u) *
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (|ξ|^(u-1)) := by
  simpa using source_fourier_energy_identity μ hu (by simpa using hu1)

theorem finite_fourier_energy_of_ball_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hu2 : u < 2) (hus : u < s) (hb : BallBound μ s C) :
    (∫⁻ ξ : Plane, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
      ENNReal.ofReal (‖ξ‖^(u-2))) < ∞ := by
  have he := rieszEnergy_lt_top_of_ball_bound μ hu hus hb
  rw [planar_fourier_energy_identity μ hu hu2] at he
  by_contra hn
  rw [top_le_iff.mp (not_lt.mp hn), ENNReal.mul_top
    (ENNReal.ofReal_pos.mpr (sourceEnergyConstant_pos hu hu2)).ne'] at he
  exact lt_irrefl _ he

end PlanarFalconer

end OAI
