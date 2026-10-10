import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularTightness

namespace OAI

section

/-! # A single physical damping rate for all starts in a short time window -/

noncomputable section
open Set
open scoped NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem window_damping_range {κ d b W s : ℝ}
    (hκ : 0 < κ) (hκsmall : κ ≤ 1) (hb : 0 < b) (hW : W ≤ κ*b/200)
    (hs : s ∈ Icc b (b+W)) (hd : d ≤ 1/2) {p : V × V} (hp : p ∈ lateBox κ d s) :
    (referenceClock:ℝ) ≤ 192*Real.pi*‖transverse p.1‖/(κ*b) ∧
      192*Real.pi*‖transverse p.1‖/(κ*b) ≤ 12*(referenceClock:ℝ) := by
  have hspos := hb.trans_le hs.1
  obtain ⟨hlo,hhi,_⟩ := lateBox_radius_bounds hκ hspos hp
  have hd' := mul_le_mul_of_nonneg_right hd (mul_pos hκ hspos).le
  have hkb : κ*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hκsmall hb.le]
  have hst : s ≤ 2*b := by linarith [hs.2]
  have hrlo : κ*b/2 ≤ ‖transverse p.1‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hκ.le]
  have hrhi : ‖transverse p.1‖ ≤ 3*(κ*b) := by
    nlinarith [mul_le_mul_of_nonneg_left hst hκ.le]
  constructor
  · apply (le_div_iff₀ (mul_pos hκ hb)).mpr
    change 48*Real.pi*(κ*b) ≤ 192*Real.pi*‖transverse p.1‖
    nlinarith [mul_le_mul_of_nonneg_left hrlo (show 0 ≤ 192*Real.pi by positivity),
      mul_pos Real.pi_pos (mul_pos hκ hb)]
  · apply (div_le_iff₀ (mul_pos hκ hb)).mpr
    change 192*Real.pi*‖transverse p.1‖ ≤ 12*(48*Real.pi)*(κ*b)
    nlinarith [mul_le_mul_of_nonneg_left hrhi (show 0 ≤ 192*Real.pi by positivity)]

theorem window_damping_normalization {κ b K r : ℝ}
    (hκ : 0 < κ) (hb : 0 < b) (hr : 0 < r) :
    (K/(4*r))*(192*Real.pi*r/(κ*b)) = 48*Real.pi*K/(κ*b) := by
  field_simp
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Localization of uniformly integrable sources on positive-time Euclidean windows -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

def kineticWindow (a A R : ℝ) : Set KineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : Velocity) R) ×ˢ univ

def kineticWindowVolume (a A R : ℝ) : Measure KineticPhase :=
  ((volume.restrict (Icc a A)).prod (volume.restrict (Metric.closedBall (0 : Velocity) R))).prod volume

theorem kineticWindow_measurable (a A R : ℝ) : MeasurableSet (kineticWindow a A R) :=
  (measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet).prod MeasurableSet.univ

theorem kineticWindowVolume_eq (a A R : ℝ) :
    kineticWindowVolume a A R = (volume : Measure KineticPhase).restrict (kineticWindow a A R) := by
  unfold kineticWindowVolume kineticWindow
  rw [Measure.volume_eq_prod,Measure.volume_eq_prod,← Measure.prod_restrict,← Measure.prod_restrict]
  simp only [Measure.restrict_univ]

theorem localizedSource_eq_window {a A R : ℝ} (ha : 0 ≤ a) {χ : KineticPhase → ℝ}
    (hχ : tsupport χ ⊆ kineticWindow a A R) (f Q : KineticPhase → ℝ) :
    localizedSource A χ f Q = fun z =>
      χ z*(kineticWindow a A R).indicator Q z+
        (transportDerivative χ z+χ z)*(kineticWindow a A R).indicator f z := by
  funext z
  by_cases hz : z ∈ kineticWindow a A R
  · have ht : z.1.1 ∈ Icc 0 A := ⟨ha.trans hz.1.1.1,hz.1.1.2⟩
    simp only [localizedSource,ite_eq_left ht,indicator_of_mem hz]
  · have hn : z ∉ tsupport χ := fun h => hz (hχ h)
    have hc := image_eq_zero_of_notMem_tsupport hn
    have hd := transportDerivative_eq_zero hn
    simp only [localizedSource,hc,hd,zero_mul,add_zero,ite_self,indicator_of_notMem hz]

private theorem ui_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (hg : UniformIntegrable g 1 μ) :
    UniformIntegrable (fun n x => f n x+g n x) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.add hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

theorem localizedSource_ui_window {a A R : ℝ} (ha : 0 ≤ a) {χ : KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ kineticWindow a A R) {f Q : ℕ → KineticPhase → ℝ}
    (hf : UniformIntegrable f 1 (kineticWindowVolume a A R))
    (hQ : UniformIntegrable Q 1 (kineticWindowVolume a A R)) :
    UniformIntegrable (fun n => localizedSource A χ (f n) (Q n)) 1 volume := by
  have hf0 := Compactness.uniformIntegrable_indicator_of_restrict (kineticWindow_measurable a A R)
    (kineticWindowVolume_eq a A R ▸ hf)
  have hQ0 := Compactness.uniformIntegrable_indicator_of_restrict (kineticWindow_measurable a A R)
    (kineticWindowVolume_eq a A R ▸ hQ)
  obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  let D : KineticPhase → ℝ := fun z => transportDerivative χ z+χ z
  have hDm : Continuous D := (transportDerivative_continuous hχ).add hχ.continuous
  have hDc : HasCompactSupport D := (transportDerivative_hasCompactSupport hc).add hc
  obtain ⟨B,hB⟩ := hDm.bounded_above_of_compact_support hDc
  have h1 := Compactness.uniformIntegrable_of_bounded_multiplier hQ0 hχ.continuous.measurable
    (⟨max C 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |χ z| ≤ C from hC z).trans (le_max_left _ _))
  have h2 := Compactness.uniformIntegrable_of_bounded_multiplier hf0 hDm.measurable
    (⟨max B 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (show |D z| ≤ B from hB z).trans (le_max_left _ _))
  simpa only [localizedSource_eq_window ha hs,D] using ui_add h1 h2

end BoltzmannNonuniqueness.TransportCutoff

end

end

end OAI
