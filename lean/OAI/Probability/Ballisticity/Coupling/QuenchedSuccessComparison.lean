import Mathlib
import OAI.Probability.Ballisticity.Estimates.SuccessfulAverage
import OAI.Probability.Ballisticity.Coupling.QuenchedMoments

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def successQuenchedKernel {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    Kernel (Environment d) (Path d) where
  toFun ω := (crossingQuenched ℓ x H ω)⁻¹ • (quenchedKernel (ω,x)).restrict (Cross ℓ x H)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply,Measure.restrict_apply hA,smul_eq_mul]
    exact (measurable_crossingQuenched ℓ x H).inv.mul
      ((fixedQuenchedKernel x).measurable_coe (hA.inter (measurableSet_cross ℓ x H)))

lemma successQuenchedKernel_apply {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (A : Set (Path d)) (hA : MeasurableSet A) :
    successQuenchedKernel ℓ x H ω A = (crossingQuenched ℓ x H ω)⁻¹ *
      quenchedKernel (ω,x) (A ∩ Cross ℓ x H) := by
  exact (Measure.smul_apply _ _ _).trans (by rw [Measure.restrict_apply hA]; rfl)

instance successQuenchedKernel_finite {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    IsFiniteKernel (successQuenchedKernel ℓ x H) where
  exists_univ_le := by
    refine ⟨1,by simp,fun ω => ?_⟩
    rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
    exact ENNReal.inv_mul_le_one _

lemma successQuenchedKernel_probability {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (hq : crossingQuenched ℓ x H ω ≠ 0) :
    IsProbabilityMeasure (successQuenchedKernel ℓ x H ω) := by
  constructor
  rw [successQuenchedKernel_apply _ _ _ _ _ MeasurableSet.univ,Set.univ_inter]
  exact ENNReal.inv_mul_cancel hq (measure_ne_top _ _)

lemma quenched_success_event_comparison {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) (hq : noDropQuenched ℓ x ω ≠ 0)
    (hsub : NoDrop ℓ x ≤ᵐ[quenchedKernel (ω,x)] Cross ℓ x H)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    |(noDropQuenchedKernel ℓ x ω).real A-(successQuenchedKernel ℓ x H ω).real A| ≤
      1-(noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω).toReal := by
  have hpq : noDropQuenched ℓ x ω ≤ crossingQuenched ℓ x H ω := measure_mono_ae hsub
  have ha : crossingQuenched ℓ x H ω ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hq).trans_le hpq)
  let B := noDropQuenchedKernel ℓ x ω
  let C := successQuenchedKernel ℓ x H ω
  let η := (crossingQuenched ℓ x H ω)⁻¹ • (quenchedKernel (ω,x)).restrict (NoDrop ℓ x)
  let : IsProbabilityMeasure B := noDropQuenchedKernel_probability ℓ x ω hq
  let : IsProbabilityMeasure C := successQuenchedKernel_probability ℓ x H ω ha
  have hηB : η ≤ B := by
    apply Measure.le_iff.mpr
    intro E hE
    rw [noDropQuenchedKernel_apply _ _ _ _ hE]
    change (crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) E ≤ _
    rw [Measure.restrict_apply hE]
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr hpq) le_rfl
  have hηC : η ≤ C := by
    apply Measure.le_iff.mpr
    intro E hE
    rw [successQuenchedKernel_apply _ _ _ _ _ hE]
    change (crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) E ≤ _
    rw [Measure.restrict_apply hE]
    apply mul_le_mul' le_rfl
    apply measure_mono_ae
    filter_upwards [hsub] with X hX
    exact fun h => ⟨h.1,hX h.2⟩
  let : IsFiniteMeasure η := ⟨lt_of_le_of_lt (hηB Set.univ) (measure_lt_top _ _)⟩
  have hm : η.real Set.univ=(noDropQuenched ℓ x ω / crossingQuenched ℓ x H ω).toReal := by
    change ((crossingQuenched ℓ x H ω)⁻¹ * (quenchedKernel (ω,x)).restrict (NoDrop ℓ x) Set.univ).toReal=_
    rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
    congr 1
    exact (ENNReal.div_eq_inv_mul).symm
  have hB := measureReal_le_add_mass_defect B η hηB A hA
  have hC := measureReal_le_add_mass_defect C η hηC A hA
  have hB' : η.real A ≤ B.real A := ENNReal.toReal_mono (measure_ne_top _ _) (hηB A)
  have hC' : η.real A ≤ C.real A := ENNReal.toReal_mono (measure_ne_top _ _) (hηC A)
  rw [hm] at hB hC
  change |B.real A-C.real A| ≤ _
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma noDrop_success_cost_ae_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ=1)
    (htrans : DirectionallyTransient ν ℓ) (x : Lattice d)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    ∀ᵐ ω ∂environmentLaw ν,
      Tendsto (fun i => 1-(noDropQuenched ℓ x ω / crossingQuenched ℓ x (H i) ω).toReal)
        atTop (𝓝 0) := by
  filter_upwards [crossingQuenched_tendsto_ae ν ℓ htrans,
    quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans] with ω hc hq
  have hh := ENNReal.Tendsto.const_mul (tendsto_inv_iff.mpr ((hc x).comp hH))
    (Or.inr (show noDropQuenched ℓ x ω ≠ ⊤ from measure_ne_top _ _))
  rw [ENNReal.mul_inv_cancel (ne_of_gt (hq x)) (measure_ne_top _ _)] at hh
  have hr := (ENNReal.continuousAt_toReal (by simp : (1:ℝ≥0∞)≠⊤)).tendsto.comp hh
  simpa only [div_eq_mul_inv,ENNReal.toReal_one,sub_self] using
    (tendsto_const_nhds.sub hr : Tendsto (fun i => 1-(noDropQuenched ℓ x ω *
      (crossingQuenched ℓ x (H i) ω)⁻¹).toReal) atTop (𝓝 (1-(1:ℝ≥0∞).toReal)))

end DirectionalTransience

end

end

end OAI
