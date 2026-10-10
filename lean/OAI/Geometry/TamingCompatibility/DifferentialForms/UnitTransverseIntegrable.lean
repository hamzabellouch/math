import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.UnitTransverseLocal
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransverseCut
import OAI.Geometry.TamingCompatibility.Concentration.RadialDefectCombination

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma unitTransverse_quotient_integrable (p : X) (b : Space) {R : ℝ} (hR : 0 < R)
    (hBT : Metric.closedBall b R ⊆ (extChartAt Model p).target)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (hdef : Integrable (smoothUnitDefect J α hs ht p b R 0) μ) :
    Integrable (fun u => ‖unitTransverseCut J α hs ht p b K u‖^2 /
      (unitDistanceCut J α hs ht p b K u)^4) μ := by
  obtain ⟨C,B,hC,hB,hlocal⟩ := unitTransverse_local_bound J α hs ht p b hR hBT
  have hb := hBT (Metric.mem_closedBall_self hR.le)
  let G := hermitianGraph (coordinateJ J p b)
  have hmeas := ((unitTransverseCut_measurable J α hs ht p b hK hKT).norm.pow_const 2).div
    ((unitDistanceCut_measurable J α hs ht p b hK hKT).pow_const 4)
  apply ((hdef.const_mul (C*‖G‖^4)).add (integrable_const (B+1/R^2))).mono' hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  simp only [Pi.div_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hzero : 0 ≤ smoothUnitDefect J α hs ht p b R 0 u := smoothUnitDefect_nonneg J α hs ht p hb R 0 u
  by_cases hu : u ∈ unitChartDomain J α hs ht p K
  · simp only [unitTransverseCut,unitDistanceCut,indicator_of_mem hu]
    have husrc := (unitChart_mem J α hs ht p hKT hu).1
    let t := ‖unitChartBase J α hs ht p u-b‖
    let d := unitRadialDefect J α hs ht p b u
    let g := unitRadialRadius J α hs ht p b u
    have ht0 : 0 ≤ t := norm_nonneg _
    have hd0 : 0 ≤ d := unitRadialDefect_nonneg J α hs ht p hb u
    have hg0 : 0 ≤ g := norm_nonneg _
    by_cases hball : u ∈ unitChartDomain J α hs ht p (Metric.closedBall b R)
    · have hfrac := defect_quotient_radius_compare hd0 ht0 hg0
        (hermitianGraph_norm_ge (coordinateJ J p b) (unitChartBase J α hs ht p u-b))
        (G.le_opNorm (unitChartBase J α hs ht p u-b)) (by
          intro hz
          have hz' : unitChartBase J α hs ht p u-b = 0 := norm_eq_zero.mp hz
          simp [d,unitRadialDefect,hz',hermitianDefect])
      have he : smoothUnitDefect J α hs ht p b R 0 u = 2*d/g^4 := by
        rw [smoothUnitDefect,indicator_of_mem hball]
        change 2*d/((0:ℝ)^2+g^2)^2 = 2*d/g^4
        ring
      have hsq := div_le_div_of_nonneg_right (hlocal u hball) (pow_nonneg ht0 4)
      have hnorm : ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*(d/t^4)+B*(t^4/t^4) := by
        calc
          _ ≤ (C*d+B*t^4)/t^4 := hsq
          _ = _ := by ring
      have htfrac : t^4/t^4 ≤ 1 := div_self_le_one _
      have hh := hnorm.trans (add_le_add (mul_le_mul_of_nonneg_left hfrac hC)
        (mul_le_of_le_one_right hB htfrac))
      rw [he]
      have hp : 0 ≤ C*‖G‖^4*(d/g^4) := by positivity
      have hRinv : 0 ≤ (1:ℝ)/R^2 := by positivity
      change ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*‖G‖^4*(2*d/g^4)+(B+1/R^2)
      rw [show 2*d/g^4 = 2*(d/g^4) by ring]
      nlinarith
    · have hRt : R ≤ t := by
        by_contra h
        have hmem : unitChartBase J α hs ht p u ∈ Metric.closedBall b R := by
          rw [Metric.mem_closedBall,dist_eq_norm]
          exact (lt_of_not_ge h).le
        exact hball ⟨unitChartBase J α hs ht p u,hmem,(extChartAt Model p).left_inv husrc⟩
      have htpos := lt_of_lt_of_le hR hRt
      obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p u husrc
      have hnorm := norm_transverse_le _ _ (unitChartBase J α hs ht p u-b) h₁ h₂ h₃
      have hsq := div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (pow_nonneg ht0 4)
      have he : t^2/t^4 = 1/t^2 := by field_simp
      have hh : ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ 1/R^2 := by
        apply (hsq.trans_eq he).trans
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hR) (pow_le_pow_left₀ hR.le hRt 2)
      have hp : 0 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u := by positivity
      change ‖unitTransverse J α hs ht p b u‖^2/t^4 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u+(B+1/R^2)
      linarith
  · simp only [unitTransverseCut,unitDistanceCut,indicator_of_notMem hu,norm_zero]
    have hp : 0 ≤ C*‖G‖^4*smoothUnitDefect J α hs ht p b R 0 u := by positivity
    simp only [zero_pow (by decide : 2 ≠ 0),zero_div]
    positivity
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace MeasureTheory
open scoped _root_.MeasureTheory
open Filter
open scoped Topology ENNReal

lemma integrable_nonneg_limit_of_uniform_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} {G : ℕ → Ω → ℝ} {f : Ω → ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ n, _root_.MeasureTheory.Integrable (G n) μ) (hpos : ∀ n x, 0 ≤ G n x)
    (hbound : ∀ n, ∫ x, G n x ∂μ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (f x))) :
    _root_.MeasureTheory.Integrable f μ ∧ ∫ x, f x ∂μ ≤ C := by
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae _
    (fun n => (hG n).aestronglyMeasurable) (Eventually.of_forall hlim)
  have hfpos : ∀ x, 0 ≤ f x := fun x => ge_of_tendsto (hlim x) (Eventually.of_forall (fun n => hpos n x))
  have hlinear (n : ℕ) : ∫⁻ x, ‖G n x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    rw [show (fun x => ‖G n x‖ₑ) = fun x => ENNReal.ofReal (G n x) by
      funext x; rw [Real.enorm_eq_ofReal (hpos n x)]]
    rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG n) (Eventually.of_forall (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hnorm : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
    calc
      ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖G n x‖ₑ) atTop ∂μ :=
        _root_.MeasureTheory.lintegral_congr (fun x => (hlim x).enorm.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
        _root_.MeasureTheory.lintegral_liminf_le' (fun n => (hG n).aestronglyMeasurable.aemeasurable.enorm)
      _ ≤ ENNReal.ofReal C := liminf_le_of_le (by isBoundedDefault) (by
          intro b hb
          obtain ⟨n,hn⟩ := hb.exists
          exact hn.trans (hlinear n))
  have hfi : _root_.MeasureTheory.Integrable f μ := ⟨hmeas,hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hfi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hfpos)]
  simpa only [Real.enorm_eq_ofReal (hfpos _)] using hnorm

end MeasureTheory

end
end

end OAI
