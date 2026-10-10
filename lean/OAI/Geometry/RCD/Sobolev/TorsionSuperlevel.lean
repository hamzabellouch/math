import OAI.Geometry.RCD.Sobolev.TorsionMoment

namespace OAI

/-!
# Nonlinear superlevel inequality for the Dirichlet torsion solution

Bounded two-level tests, rather than a prior integrability assertion for an
unbounded power of the solution, justify each use of Sobolev and Hölder.
-/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

/-- The bounded level moment controls the measure of the upper superlevel. -/
theorem level_superlevel_measure_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {u : X → ℝ} (hu : Measurable u)
    {k l p B : ℝ} (hkl : k < l) (hp : 0 < p)
    (hbound : (∫ x, levelClip k l (u x) ^ p ∂ν) ≤ B) :
    ν.real {x | l ≤ u x} ≤ B / (l - k) ^ p := by
  let v := fun x => levelClip k l (u x)
  have hv0 (x) : 0 ≤ v x := le_min (le_max_right _ _) (sub_nonneg.mpr hkl.le)
  have hvm : Measurable v := (levelClip_lipschitz k l).continuous.measurable.comp hu
  have hvi : Integrable (fun x => v x ^ p) ν := by
    apply Integrable.of_bound (hvm.pow_const p).aestronglyMeasurable ((l - k) ^ p)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hv0 x) p)]
      exact Real.rpow_le_rpow (hv0 x) (min_le_right _ _) hp.le
  let S := {x | l ≤ u x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hu
  have hlo : (l - k) ^ p * ν.real S ≤ ∫ x, v x ^ p ∂ν := by
    have hb := integral_mono_ae ((integrable_const ((l - k) ^ p)).indicator hS) hvi
      (Eventually.of_forall fun x => by
        by_cases hx : x ∈ S
        · rw [indicator_of_mem hx]
          have hh : l ≤ u x := hx
          simp only [v, levelClip, positiveClip,
            max_eq_left (sub_nonneg.mpr (hkl.le.trans hh)),
            min_eq_right (sub_le_sub_right hh k)]
          exact le_rfl
        · rw [indicator_of_notMem hx]
          exact Real.rpow_nonneg (hv0 x) p)
    simpa only [integral_indicator_const _ hS, smul_eq_mul, mul_comm] using hb
  exact (le_div_iff₀ (Real.rpow_pos_of_pos (sub_pos.mpr hkl) p)).mpr
    (by simpa only [mul_comm] using hlo.trans hbound)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The superlinear measure recurrence underlying the torsion height bound. -/
theorem torsion_superlevel_le (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (u : SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ u.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    {d C : ℝ} (hd : 1 < d) (hC : 0 ≤ C)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) :
    (μ.restrict Ω).real {x | l ≤ SobolevSpace.toLp μ hQ u.val x} ≤
      C ^ (2 * d) *
        ((μ.restrict Ω).real {x | k < SobolevSpace.toLp μ hQ u.val x}) ^ (2 * d - 1) /
          (l - k) ^ (2 * d) := by
  let ν := μ.restrict Ω
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hΩfin.lt_top⟩
  let U := fun x => SobolevSpace.toLp μ hQ u.val x
  let v := fun x => levelClip k l (U x)
  let S := {x | k < U x}
  let T := levelTruncation μ hQ u.val hk hkl.le
  let φ : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨T, levelTruncation_mem_dirichlet μ hQ Ω u hk hkl.le⟩
  have hU : Measurable U := (Lp.stronglyMeasurable _).measurable
  have hS : MeasurableSet S := measurableSet_lt measurable_const hU
  have hv : Measurable v := (levelClip_lipschitz k l).continuous.measurable.comp hU
  have hv0 (x) : 0 ≤ v x := le_min (le_max_right _ _) (sub_nonneg.mpr hkl.le)
  have hvb : ∀ᵐ x ∂ν, 0 ≤ v x ∧ v x ≤ l - k :=
    Eventually.of_forall fun x => ⟨hv0 x, min_le_right _ _⟩
  have hvz : ∀ᵐ x ∂ν, x ∉ S → v x = 0 := by
    apply Eventually.of_forall
    intro x hx
    have hh : U x ≤ k := le_of_not_gt hx
    simp only [v, levelClip, positiveClip, max_eq_right (sub_nonpos.mpr hh),
      min_eq_left (sub_nonneg.mpr hkl.le)]
  have hp : 1 < 2 * d := by linarith
  have hpq : (2 * d).HolderConjugate (2 * d / (2 * d - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hholder := bounded_support_integral_le ν hv.aemeasurable hpq hvb S hS hvz
  have hmoment : (∫ x, v x ^ (2 * d) ∂ν) ^ (2 / (2 * d)) ≤
      C * ((∫ x, v x ^ (2 * d) ∂ν) ^ (1 / (2 * d)) * (ν.real S) ^ ((2 * d - 1) / (2 * d))) := by
    have he := torsion_level_energy μ hQ Ω u hsolve hk hkl.le
    have hsob' := hsob φ
    have hvrep := ae_restrict_of_ae (s := Ω) (levelTruncation_coe μ hQ u.val hk hkl.le)
    have heq : (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) =
        ∫ x, v x ^ (2 * d) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hvrep] with x hx
      change |SobolevSpace.toLp μ hQ T x| ^ (2 * d) = v x ^ (2 * d)
      rw [hx, abs_of_nonneg (hv0 x)]
    rw [heq] at hsob'
    change (∫ x, v x ^ (2 * d) ∂ν) ^ (1 / d) ≤ C * energyForm μ hQ T T at hsob'
    rw [he] at hsob'
    have hexp : 1 / (2 * d / (2 * d - 1)) = (2 * d - 1) / (2 * d) := by field_simp
    rw [hexp] at hholder
    have hexp' : 2 / (2 * d) = 1 / d := by field_simp
    rw [hexp']
    exact hsob'.trans (mul_le_mul_of_nonneg_left hholder hC)
  have hI0 : 0 ≤ ∫ x, v x ^ (2 * d) ∂ν :=
    integral_nonneg fun x => Real.rpow_nonneg (hv0 x) _
  have hmoment' := moment_le_of_sobolev_holder hI0 hC measureReal_nonneg hp hmoment
  exact level_superlevel_measure_le ν hU hkl (by linarith) hmoment'

end RegularPointCoordinates

end

end OAI
