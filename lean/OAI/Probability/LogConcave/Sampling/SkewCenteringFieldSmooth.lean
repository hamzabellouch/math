import Mathlib
import OAI.Probability.LogConcave.Sampling.SkewCenteringField
import OAI.Probability.LogConcave.Dynamics.Truncated

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

lemma skewCenteringField_smooth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) (s : ℝ) :
    ContDiff ℝ 1 (skewCenteringField K m s) := by
  have hA : ContDiff ℝ 1 (fun y : Point d => (K y).adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Point d) (F:=Point d)).contDiff.comp hK
  have hAp : ContDiff ℝ 1 (fun p : Point d × Point d => (K p.1).adjoint p.2) :=
    (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hmp : ContDiff ℝ 1 (fun p : Point d × Point d => m p.1) := hm.comp contDiff_fst
  exact (hAp.const_smul (-s⁻¹)).prodMk (hmp.const_smul s⁻¹)

lemma skewCenteringField_growth {d : ℕ} {K : Point d → Point d →L[ℝ] Point d}
    {m : Point d → Point d} {C : ℝ} {L : ℝ≥0} (hC : 0≤C) (hK : ∀y,‖K y‖≤C)
    (hm : LipschitzWith L m) {s : ℝ} (hs : 0<s) (p : Point d × Point d) :
    ‖skewCenteringField K m s p‖≤ s⁻¹*(C+L)*‖p‖+s⁻¹*‖m 0‖ := by
  have hmn : ‖m p.1‖≤L*‖p.1‖+‖m 0‖ := by
    have h1 := hm.norm_sub_le p.1 0
    simpa only [sub_zero] using (norm_le_norm_sub_add (m p.1) (m 0)).trans (add_le_add h1 le_rfl)
  have hkn : ‖(K p.1).adjoint p.2‖≤C*‖p.2‖ := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [ContinuousLinearMap.adjoint.norm_map]; gcongr; exact hK _)
  change max ‖-s⁻¹ • (K p.1).adjoint p.2‖ ‖s⁻¹ • m p.1‖≤_
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hs)]
  apply max_le
  · calc
      _≤ s⁻¹*(C*‖p.2‖) := mul_le_mul_of_nonneg_left hkn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖)+s⁻¹*‖m 0‖ := by
        have hp : ‖p.2‖≤‖p‖ := norm_snd_le p
        have hL : C≤C+L := le_add_of_nonneg_right L.coe_nonneg
        have hh : C*‖p.2‖≤(C+L)*‖p‖ := mul_le_mul hL hp (norm_nonneg _) (by positivity)
        exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)).trans (le_add_of_nonneg_right (by positivity))
      _=_ := by ring
  · calc
      _≤ s⁻¹*(L*‖p.1‖+‖m 0‖) := mul_le_mul_of_nonneg_left hmn (inv_nonneg.mpr hs.le)
      _≤ s⁻¹*((C+L)*‖p‖+‖m 0‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
        apply add_le_add_left
        exact mul_le_mul (le_add_of_nonneg_left hC) (norm_fst_le p) (norm_nonneg _) (by positivity)
      _=_ := by ring

lemma integrable_product_norm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x => ‖x‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    Integrable (fun p : E × F => ‖p‖) (μ.prod ν) := by
  apply ((hμ.comp_fst ν).add (hν.comp_snd μ)).mono' continuous_norm.aestronglyMeasurable
  filter_upwards [] with p
  rw [norm_norm]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

theorem skewCentering_stationary {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : ContDiff ℝ 1 K) (hm : ContDiff ℝ 1 m) {C : ℝ} {L : ℝ≥0}
    (hC : 0≤C) (hKb : ∀y,‖K y‖≤C) (hmL : LipschitzWith L m)
    (hμ : Integrable (fun y => ‖y‖) μ)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    {s a b : ℝ} (hs : 0<s) (hab : a<b) :
    (μ.prod (stdGaussian (Point d))).map
      (fun p => LinearGrowthODE.flow (skewCenteringField_smooth hK hm s)
        (by positivity : 0≤ s⁻¹*(C+L)) (by positivity : 0≤ s⁻¹*‖m 0‖)
        (skewCenteringField_growth hC hKb hmL hs) hab.le p b)=μ.prod (stdGaussian (Point d)) := by
  have hi : Integrable (fun g : Point d => ‖g‖) (stdGaussian (Point d)) := IsGaussian.integrable_id.norm
  have hprod := integrable_product_norm hμ hi
  apply LinearGrowthODE.stationary_law
  · exact hab
  · apply ((hprod.const_mul (s⁻¹*(C+L))).add (integrable_const (s⁻¹*‖m 0‖))).mono'
      (skewCenteringField_smooth hK hm s).continuous.norm.aestronglyMeasurable
    filter_upwards [] with p
    rw [norm_norm]
    exact skewCenteringField_growth hC hKb hmL hs p
  · intro φ hφ hφc
    exact product_stein_flux hK.continuous hm.continuous hstein s hφ hφc
end LogConcaveSampling

end

end

end

end OAI
