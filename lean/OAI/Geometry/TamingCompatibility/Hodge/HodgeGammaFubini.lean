import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaSplit

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] [PseudoMetricSpace X] in
lemma gammaKernel_measurable (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2)) (T r : ℝ) :
    StronglyMeasurable (fun p : X × X => gammaKernel K T r p.1 p.2) := by
  have hm : StronglyMeasurable (fun p : (X × X) × ℝ =>
      hodgeGammaWeight p.2 • K (r^2*p.2) p.1.1 p.1.2) :=
    ((hodgeGammaWeight_continuous.stronglyMeasurable.comp_measurable measurable_snd).smul
      (hKm.comp_measurable (show Measurable (fun p : (X × X) × ℝ => (r^2*p.2,p.1.1,p.1.2)) by fun_prop)))
  exact (hm.integral_prod_right (ν := volume.restrict (Ioc 0 (T/r^2)))).const_smul (1/120 : ℝ)

variable (μ : Measure (X × X)) [IsFiniteMeasure μ]

lemma gammaKernel_pairing (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (Θ : X × X → B →L[ℝ] ℝ) (hΘm : StronglyMeasurable Θ)
    {M : ℝ} (hM : 0 ≤ M) (hΘ : ∀ p, ‖Θ p‖ ≤ M) :
    (∫ p, Θ p (gammaKernel K T r p.1 p.2) ∂μ) =
      (1/120 : ℝ) * ∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
        (∫ p, Θ p (K (r^2*s) p.1 p.2) ∂μ) := by
  let ν := volume.restrict (Ioc 0 (T/r^2))
  let G := fun s (p : X × X) => hodgeGammaWeight s • K (r^2*s) p.1 p.2
  let m := fun s : ℝ => A/r^(2*k)*(Real.exp (-s)*s^q)
  have hm : Integrable m ν := by
    have h := polynomialMoment_integrable q 0
    simp only [pow_zero,mul_one] at h
    exact (h.mono_set (fun _ h => h.1)).const_mul _
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    ((hodgeGammaWeight_continuous.stronglyMeasurable.comp_measurable measurable_fst).smul
      (hKm.comp_measurable (show Measurable (fun p : ℝ × X × X => (r^2*p.1,p.2.1,p.2.2)) by fun_prop)))
  have hGb (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) (p : X × X) : ‖G s p‖ ≤ m s := by
    have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
    have hb : VolterraBounds.weight 0 (r^2*s) p.1 p.2 * ‖K (r^2*s) p.1 p.2‖ ≤ A/(r^2*s)^k := by
      simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK _ hst p.1 p.2
    simpa only [VolterraBounds.weight,pow_zero,one_mul,mul_one] using
      weighted_gamma_integrand q k 0 hqk hr hs.1 K p.1 p.2 hb
  have hGi (p : X × X) : Integrable (fun s => G s p) ν := by
    apply hm.mono' ((hGm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hGb s hs p
  have hFm : StronglyMeasurable (fun p : ℝ × X × X => Θ p.2 (G p.1 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hΘm.comp_measurable measurable_snd).prodMk hGm)
  have hFi : Integrable (fun p : ℝ × X × X => Θ p.2 (G p.1 p.2)) (ν.prod μ) := by
    apply ((hm.const_mul M).comp_fst μ).mono' hFm.aestronglyMeasurable
    have hp : ∀ᵐ p : ℝ × X × X ∂ν.prod μ, p.1 ∈ Ioc 0 (T/r^2) := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact Eventually.of_forall fun _ => hs
    filter_upwards [hp] with p hp
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hΘ p.2) (hGb p.1 hp p.2) (norm_nonneg _) hM)
  calc
    _ = (1/120 : ℝ) * ∫ p, ∫ s, Θ p (G s p) ∂ν ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      unfold gammaKernel
      rw [map_smul,smul_eq_mul,(Θ p).integral_comp_comm (hGi p)]
    _ = (1/120 : ℝ) * ∫ s, ∫ p, Θ p (G s p) ∂μ ∂ν := by
      exact congrArg (fun a : ℝ => (1/120 : ℝ)*a) (integral_integral_swap hFi).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      simp only [G,map_smul,smul_eq_mul,integral_const_mul]

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
