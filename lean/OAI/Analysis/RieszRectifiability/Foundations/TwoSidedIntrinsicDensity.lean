import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BoundedPlanarDensity

namespace OAI

/-!
# Two-sided intrinsic densities

Lower ball-growth bounds give a positive multiple of Euclidean volume dominated
by the measure. Together with the upper-growth domination, this produces a
measurable density with pointwise lower and upper bounds by clipping its
Radon–Nikodym derivative without changing the represented measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def intrinsicLowerDensityBound (n : ℕ) (C : ℝ) : ℝ≥0 :=
  Real.toNNReal ((C * (volume : Measure (Ambient n)).real (ball 0 1))⁻¹)

theorem intrinsicLowerDensityBound_pos (n : ℕ) (C : ℝ) (hC : 0 < C) :
    0 < intrinsicLowerDensityBound n C := by
  apply Real.toNNReal_pos.mpr
  apply inv_pos.mpr
  exact mul_pos hC (ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne)

theorem intrinsic_volume_le_of_lower_growth (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient n)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x : Ambient n, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) :
    intrinsicLowerDensityBound n C • (volume : Measure (Ambient n)) ≤ μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hc : (intrinsicLowerDensityBound n C : ℝ) = (C * V)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr (mul_nonneg hC.le hV.le))
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicLowerDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n / C := by
    rw [hc, hvol]
    field_simp [hV.ne', hC.ne']
  calc
    (intrinsicLowerDensityBound n C • (volume : Measure (Ambient n))) (closedBall x r) =
        ENNReal.ofReal ((intrinsicLowerDensityBound n C : ℝ) *
          (volume : Measure (Ambient n)).real (closedBall x r)) := by
      rw [ENNReal.ofReal_mul (intrinsicLowerDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]
    _ = ENNReal.ofReal (r ^ n / C) := congrArg ENNReal.ofReal hid
    _ ≤ μ (ball x r) := hlower x r hr
    _ ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall

theorem nnreal_le_rnDeriv_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (c : ℝ≥0) (hac : μ ≪ ν) (hdom : c • ν ≤ μ) :
    ∀ᵐ x ∂ν, (c : ℝ≥0∞) ≤ μ.rnDeriv ν x := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
  intro s hs _hfin
  rw [Measure.setLIntegral_rnDeriv' hac hs]
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply] using! hdom s

theorem exists_two_sided_density_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hν : ν ≠ 0)
    (c D : ℝ≥0) (hlower : c • ν ≤ μ) (hupper : μ ≤ D • ν) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, c ≤ f x ∧ f x ≤ D) ∧
      ν.withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  have hac : μ ≪ ν := hupper.absolutelyContinuous.trans Measure.smul_absolutelyContinuous
  have hlo := nnreal_le_rnDeriv_of_domination μ ν c hac hlower
  have hup := rnDeriv_le_of_nnreal_domination μ ν D hupper
  have : NeBot (ae ν) := ae_neBot.mpr hν
  have hcd : c ≤ D := by
    obtain ⟨x, hxlo, hxup⟩ := (hlo.and hup).exists
    exact ENNReal.coe_le_coe.mp (hxlo.trans hxup)
  let f : α → ℝ := fun x => min (D : ℝ) (max (c : ℝ) (μ.rnDeriv ν x).toReal)
  have hm : Measurable f := measurable_const.min
    (measurable_const.max (μ.measurable_rnDeriv ν).ennreal_toReal)
  have heq : (fun x => ENNReal.ofReal (f x)) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [hlo, hup] with x hxlo hxup
    have hne : μ.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hxup
    have hreal_lo : (c : ℝ) ≤ (μ.rnDeriv ν x).toReal := by
      simpa only [ENNReal.coe_toReal] using!
        (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hne).mpr hxlo
    have hreal_up : (μ.rnDeriv ν x).toReal ≤ (D : ℝ) := by
      simpa only [ENNReal.coe_toReal] using!
        (ENNReal.toReal_le_toReal hne ENNReal.coe_ne_top).mpr hxup
    change ENNReal.ofReal (min (D : ℝ) (max (c : ℝ) (μ.rnDeriv ν x).toReal)) = _
    rw [max_eq_right hreal_lo, min_eq_right hreal_up, ENNReal.ofReal_toReal hne]
  refine ⟨f, hm, ?_, ?_⟩
  · intro x
    exact ⟨le_min (NNReal.coe_le_coe.mpr hcd) (le_max_left _ _), min_le_left _ _⟩
  · rw [withDensity_congr_ae heq]
    exact Measure.withDensity_rnDeriv_eq μ ν hac

theorem exists_two_sided_intrinsic_density (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient n)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x : Ambient n, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, intrinsicLowerDensityBound n C ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n G) ∧
      (volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact exists_two_sided_density_of_domination μ volume (by exact NeZero.ne volume)
    (intrinsicLowerDensityBound n C) (intrinsicGrowthDensityBound n G)
    (intrinsic_volume_le_of_lower_growth n C G μ hC hg hlower)
    (intrinsic_growth_le_volume n G μ hg)

end

end RieszRectifiability

end OAI
