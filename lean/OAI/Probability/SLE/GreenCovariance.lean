import Mathlib
import OAI.Probability.SLE.StoppedFields

namespace OAI

/-! Green Covariance for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal
namespace SLEExactGauge
namespace SpatialAngularFamily
variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u δ : ℝ}
lemma physicalWeight_joint_measurable (b : SpatialAngularFamily B hm κ z u δ)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : Measurable z)
    (η : Z × Ω → ℝ≥0) (hη : Measurable η) :
    Measurable (fun p : Z × Ω => (b.section p.1).physicalWeight (η p) p.2) := by
  let τ (p : Z × Ω) := min (η p) (b.τ p)
  have hτ : Measurable τ := hη.min (stopping_time_measurable_nnreal b.stopping)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hq := measurable_initialLogCoordinates.comp hz
  have hQ := (clipped_family_joint_measurable b.c).comp
    (hτ.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))
  exact (greenLogDensity_contDiff κ).continuous.measurable.comp
    (hQ.prodMk (hBm.comp (hτ.prodMk measurable_snd)))

lemma physicalWeight_uniform_bound (b : SpatialAngularFamily B hm κ z u δ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (l : ℝ) (hl : ∀ x, l ≤ Real.log (z x).im)
    (x : Z) (ω : Ω) (t : ℝ≥0) :
    ‖(b.section x).physicalWeight t ω‖ ≤ Real.exp (codimension κ * (u - Real.log 2 - l)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg ((b.section x).physicalWeight_bound hκ hκ8 t ω).1]
  apply ((b.section x).physicalWeight_bound hκ hκ8 t ω).2.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith [hl x]) (codimension_pos κ hκ8).le

end SpatialAngularFamily

 

lemma spatial_angular_weight_integral_tendsto
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u : ℝ} {δ : ℕ → ℝ}
    (b : ∀ n, SpatialAngularFamily B hm κ z u (δ n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : Measurable z)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hzH : ∀ x, z x ∈ upperHalfPlane)
    (l : ℝ) (hl : ∀ x, l ≤ Real.log (z x).im)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (σ τ : Z × Ω → ℝ≥0) (hσ : Measurable σ) (hτ : Measurable τ) :
    Tendsto (fun n => ∫ x, (b n |>.section x).physicalWeight (τ (x,ω)) ω -
      (b n |>.section x).physicalWeight (σ (x,ω)) ω ∂ν) atTop
      (𝓝 (∫ x, physicalStoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G (z x) u (τ (x,ω)) -
        physicalStoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G (z x) u (σ (x,ω)) ∂ν)) := by
  let K := Real.exp (codimension κ * (u - Real.log 2 - l))
  apply tendsto_integral_of_dominated_convergence (fun _ => 2 * K)
  · intro n
    exact (((b n).physicalWeight_joint_measurable hBc hz τ hτ).sub
      ((b n).physicalWeight_joint_measurable hBc hz σ hσ)).comp
        (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro x
    exact (norm_sub_le _ _).trans (show ‖(b n |>.section x).physicalWeight (τ (x,ω)) ω‖ +
        ‖(b n |>.section x).physicalWeight (σ (x,ω)) ω‖ ≤ 2 * K from by
      have h1 := (b n).physicalWeight_uniform_bound hκ hκ8 l hl x ω (τ (x,ω))
      have h2 := (b n).physicalWeight_uniform_bound hκ hκ8 l hl x ω (σ (x,ω))
      dsimp only [K]; linarith)
  · apply Eventually.of_forall
    intro x
    exact (physicalWeight_tendsto_source (fun n => (b n).section x) hδ hBc hκ hκ8
      (hzH x) ω γ G F hw (τ (x,ω))).sub
      (physicalWeight_tendsto_source (fun n => (b n).section x) hδ hBc hκ hκ8
        (hzH x) ω γ G F hw (σ (x,ω)))

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatial_slab_finite_exponential_of_localizations
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u : ℝ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (b : ∀ n, SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n))
    (l : ℝ) (hl : ∀ z : A, l ≤ Real.log z.val.im)
    (hlevel : ∀ z : A, (2 * z.val.im) * Real.exp (-u) < ε)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  let ν := volume.comap (Subtype.val : A → ℂ)
  let σ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 r S
  let τ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 ε S
  have hσ : Measurable σ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe r S)
  have hτ : Measurable τ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe ε S)
  let X (n : ℕ) (ω : a.samples) := ∫ z : A,
        ((b n).section z).physicalWeight (τ (z,ω)) ω -
        ((b n).section z).physicalWeight (σ (z,ω)) ω ∂ν
  let Y (ω : a.samples) := ∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (τ (z,ω)) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (σ (z,ω)) z ∂ν
  have hXm (n : ℕ) : Measurable (X n) :=
    (((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe τ hτ).sub
      ((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe σ hσ)).stronglyMeasurable.integral_prod_left'.measurable
  have hlim (ω : a.samples) : Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
    have hh := spatial_angular_weight_integral_tendsto (ν := ν) b hδ a.continuous_B
      measurable_subtype_coe hκ (by linarith) (fun z => hε.trans_le (hεr.trans (hheight z z.2)))
      l hl ω (γ ω) (a.G ω) (a.F ω) (a.witness ω) σ τ hσ hτ
    convert hh using 1
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [(a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z ε hε (hεr.trans (hheight z z.2)) u (hlevel z) (τ (z,ω)) (boundedSpatialHit_le _ _ _ _),
      (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r (hε.trans_le hεr) (hheight z z.2) u ((hlevel z).trans_le hεr)
        (σ (z,ω)) (boundedSpatialHit_le _ _ _ _)]
  apply compensated_exponential_limit_energy X (fun _ _ => slabVariance κ ε r A) Y
    (fun _ => slabVariance κ ε r A) θ
  · intro n
    exact ((((hXm n).const_mul θ).sub_const (θ^2 * slabVariance κ ε r A / 2)).exp).ennreal_ofReal.aemeasurable
  · exact Eventually.of_forall hlim
  · exact Eventually.of_forall fun _ => tendsto_const_nhds
  · intro n
    exact a.localized_spatial_slab_exponential hκ hκ4 A hA hfin ε r hε hεr hheight u (δ n) (b n) M hM S θ

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma logAngleSq_initial (κ : ℝ) (z : ℂ) (hz : 0 < z.im) :
    logAngleSq κ (initialLogCoordinates z) 0 = z.im^2 / ‖z‖^2 := by
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  rw [logAngleSq, initialLogCoordinates_im, he]
  congr 1
  rw [← Complex.normSq_eq_norm_sq]
  simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]

lemma initial_spatial_bounds (κ r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : ℂ) (hz : r ≤ z.im) (hzR : ‖z‖ ≤ R) :
    (Real.log r ≤ Real.log z.im ∧ Real.log z.im ≤ Real.log R) ∧
    r^2 / R^2 ≤ logAngleSq κ (initialLogCoordinates z) 0 ∧
    ‖initialLogCoordinates z‖ ≤ R + |Real.log r| + |Real.log R| := by
  have hy : 0 < z.im := hr.trans_le hz
  have him : z.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzR)
  have hl := Real.log_le_log hr hz
  have hh := Real.log_le_log hy him
  refine ⟨⟨hl, hh⟩, ?_, ?_⟩
  · rw [logAngleSq_initial κ z hy]
    have hn : 0 < ‖z‖ := hy.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm z))
    calc
      r^2 / R^2 ≤ z.im^2 / R^2 := div_le_div_of_nonneg_right
        (sq_le_sq₀ hr.le hy.le |>.mpr hz) (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hn)
        (sq_le_sq₀ (norm_nonneg z) hR.le |>.mpr hzR)
  · have hlog : |Real.log z.im| ≤ |Real.log r| + |Real.log R| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (Real.log r), abs_nonneg (Real.log R)]
      · linarith [le_abs_self (Real.log R), abs_nonneg (Real.log r)]
    have hnorm : ‖initialLogCoordinates z‖ ≤ |z.re| + |Real.log z.im| := by
      have hh := norm_add_le (z.re : ℂ) ((Real.log z.im : ℂ) * Complex.I)
      simpa only [initialLogCoordinates, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _),
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using hh
    have hre := (Complex.abs_re_le_norm z).trans hzR
    exact hnorm.trans (by linarith)

lemma exists_uniform_radius_level (ε R : ℝ) (hε : 0 < ε) (_hR : 0 ≤ R) :
    ∃ u : ℝ, 0 ≤ u ∧ (2 * R) * Real.exp (-u) < ε := by
  have ht : Tendsto (fun u : ℝ => (2 * R) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * R)
  obtain ⟨u, hu0, hu⟩ := (eventually_ge_atTop (0 : ℝ)).and ((tendsto_order.mp ht).2 ε hε) |>.exists
  exact ⟨u, hu0, hu⟩

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatial_slab_finite_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  have hr : 0 < r := hε.trans_le hεr
  have hR : 0 < R := hr.trans_le hrR
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  let ν := volume.comap (Subtype.val : A → ℂ)
  let : IsFiniteMeasure ν := ⟨by
    have hh := Measure.comap_apply_le (Subtype.val : A → ℂ) volume
      (show NullMeasurableSet (univ : Set A) ν from MeasurableSet.univ.nullMeasurableSet)
    apply lt_of_le_of_lt hh
    simpa only [Set.image_univ, Subtype.range_coe] using lt_top_iff_ne_top.mpr hfin⟩
  obtain ⟨u, hu, hul⟩ := exists_uniform_radius_level ε R hε hR.le
  let α := r^2 / R^2
  have hα : 0 < α := by dsimp [α]; positivity
  let δ (n : ℕ) := α / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ α := div_le_self hα.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul α
  have hbounds (z : A) := initial_spatial_bounds κ r R hr hR z (hheight z z.2) (hbound z z.2)
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let b (n : ℕ) : SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n) :=
    (exists_spatial_angular_family a.measurable_B hBm a.continuous_B a.zero_B κ Subtype.val
      measurable_subtype_coe (Real.log r) (Real.log R) (Real.log_le_log hr hrR)
      (fun z => (hbounds z).1) u (δ n) hu (hδpos n)
      (fun z => (hδle n).trans (hbounds z).2.1)).some
  have hlevel (z : A) : (2 * z.val.im) * Real.exp (-u) < ε := by
    have hi : z.val.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hbound z z.2))
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * z.val.im ≤ 2 * R) (Real.exp_pos _).le).trans_lt hul
  have hh := a.spatial_slab_finite_exponential_of_localizations hκ hκ4 A hA hfin ε r hε hεr
    hheight u δ hδlim b (Real.log r) (fun z => (hbounds z).1.1) hlevel
    (R + |Real.log r| + |Real.log R|) (fun z => (hbounds z).2.2) S θ
  have he (ω : a.samples) :
      (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) =
      ∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z :=
    integral_subtype_comap (μ := volume) hA (fun z =>
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z)
  simpa only [he] using hh

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma boundedSpatialGreen_measurable (r : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℂ × a.samples => greenDensity κ
      (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2)
      (boundedSpatialHit (γ p.2) p.1 r T) p.1) := by
  have hγ (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have ht := spatialHitTime_measurable (fun ω : a.samples => γ ω)
    a.trace_continuous hγ r
  have hτ : Measurable (fun p : ℂ × a.samples => boundedSpatialHit (γ p.2) p.1 r T) :=
    (ht.min (measurable_const (a := (T : WithTop ℝ≥0)))).untopD 0
  have hh := a.jointGreen_measurable.comp (hτ.prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using hh

 

theorem spatialGreen_tendsto_and_bound_of_level [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) :
    ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      Tendsto (fun n : ℕ => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
        (𝓝 (spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) ∧
      ∀ n : ℕ, ‖greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z‖ ≤
        Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness)
      z (hr.trans_le hy) u hu
  filter_upwards [heq, hNoHit] with ω he hn
  have hident (n : ℕ) : physicalStoppedGreen κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z u (boundedSpatialHit (γ ω) z r n) =
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω)
        (boundedSpatialHit (γ ω) z r n) z :=
    (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r hr hy u hlevel _ (boundedSpatialHit_le _ _ _ _)
  refine ⟨?_, ?_⟩
  · simpa only [hident] using (a.witness ω).spatialGreen_limit
      ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel hn
  · intro n
    dsimp only [Function.comp_apply] at he
    rw [← hident n, ← he.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
    exact (hMb _ ω).2

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatialGreen_ae_spatial_limit [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    ∃ K : ℝ, ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      ∀ᵐ z ∂(volume.restrict A),
      Tendsto (fun n : ℕ => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
        (𝓝 (spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) ∧
      ∀ n : ℕ, ‖greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z‖ ≤ K := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  obtain ⟨u, hu, hul⟩ := exists_uniform_radius_level r R hr (hr.trans_le hrR).le
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log r))
  refine ⟨K, ?_⟩
  let f (n : ℕ) (p : ℂ × a.samples) := greenDensity κ
    (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2)
    (boundedSpatialHit (γ p.2) p.1 r n) p.1
  let g (p : ℂ × a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2) p.1 r
  have hf (n : ℕ) : Measurable (f n) := a.boundedSpatialGreen_measurable r n
  have hg : Measurable g := a.spatialGreenWeight_measurable r
  have hm : MeasurableSet {p : ℂ × a.samples |
      Tendsto (fun n => f n p) atTop (𝓝 (g p)) ∧ ∀ n, ‖f n p‖ ≤ K} :=
    (measurableSet_tendsto_fun hf hg).inter (by
      change MeasurableSet {p : ℂ × a.samples | ∀ n : ℕ, ‖f n p‖ ≤ K}
      have he : {p : ℂ × a.samples | ∀ n : ℕ, ‖f n p‖ ≤ K} =
          ⋂ n : ℕ, {p : ℂ × a.samples | ‖f n p‖ ≤ K} := by
        ext p
        simp only [mem_iInter, mem_ofPred_eq]
      rw [he]
      exact MeasurableSet.iInter (fun n => measurableSet_le (hf n |>.norm) (measurable_const (a := K))))
  apply (Measure.ae_ae_comm (μ := volume.restrict A) (ν := μ) hm).mp
  filter_upwards [ae_restrict_mem hA] with z hz
  have hlevel : (2 * z.im) * Real.exp (-u) < r := by
    have hi : z.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hbound z hz))
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * z.im ≤ 2 * R) (Real.exp_pos _).le).trans_lt hul
  filter_upwards [a.spatialGreen_tendsto_and_bound_of_level hκ hκ8 z r hr
    (hheight z hz) u hu hlevel] with ω hω
  refine ⟨hω.1, fun n => (hω.2 n).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (by linarith [Real.log_le_log hr (hheight z hz)]) (codimension_pos κ hκ8).le

 

theorem spatial_slab_area_tendsto [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      Tendsto (fun n : ℕ => ∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε n) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
      (𝓝 (∫ z in A,
        spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε -
        spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) := by
  let ν := volume.restrict A
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  obtain ⟨Kε, hεlim⟩ := a.spatialGreen_ae_spatial_limit hκ hκ8 A hA ε R hε
    (hεr.trans hrR) (fun z hz => hεr.trans (hheight z hz)) hbound
  obtain ⟨Kr, hrlim⟩ := a.spatialGreen_ae_spatial_limit hκ hκ8 A hA r R
    (hε.trans_le hεr) hrR hheight hbound
  filter_upwards [hεlim, hrlim] with ω hωε hωr
  apply tendsto_integral_of_dominated_convergence (fun _ => Kε + Kr)
  · intro n
    exact (((a.boundedSpatialGreen_measurable ε n).sub
      (a.boundedSpatialGreen_measurable r n)).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hωε, hωr] with z hzε hzr
    exact (norm_sub_le _ _).trans (add_le_add (hzε.2 n) (hzr.2 n))
  · filter_upwards [hωε, hωr] with z hzε hzr
    exact hzε.1.sub hzr.1

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def spatialSlabIncrement (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (A : Set ℂ) (ε r : ℝ) : ℝ :=
  ∫ z in A, spatialGreenWeight κ U γ G z ε - spatialGreenWeight κ U γ G z r

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialSlabIncrement_measurable (A : Set ℂ) (ε r : ℝ) :
    Measurable (fun ω : a.samples => spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r) :=
  ((a.spatialGreenWeight_measurable ε).sub (a.spatialGreenWeight_measurable r)).stronglyMeasurable.integral_prod_left'.measurable

 

theorem spatial_slab_terminal_exponential [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) A ε r - θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  let X (n : ℕ) (ω : a.samples) := ∫ z in A,
    greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε n) z -
    greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z
  let Y (ω : a.samples) := spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω)
    (γ ω) (a.G ω) A ε r
  have hXm (n : ℕ) : Measurable (X n) :=
    ((a.boundedSpatialGreen_measurable ε n).sub
      (a.boundedSpatialGreen_measurable r n)).stronglyMeasurable.integral_prod_left'.measurable
  apply compensated_exponential_limit_energy X (fun _ _ => slabVariance κ ε r A) Y
    (fun _ => slabVariance κ ε r A) θ
  · intro n
    exact ((((hXm n).const_mul θ).sub_const (θ^2 * slabVariance κ ε r A / 2)).exp).ennreal_ofReal.aemeasurable
  · exact a.spatial_slab_area_tendsto hκ (by linarith) A hA hfin ε r R hε hεr hrR hheight hbound
  · exact Eventually.of_forall fun _ => tendsto_const_nhds
  · intro n
    exact a.spatial_slab_finite_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound n θ

 
theorem spatial_slab_terminal_tail [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (V x : ℝ) (hV : 0 < V) (hv : slabVariance κ ε r A ≤ V) (hx : 0 ≤ x) :
    (P.comap Subtype.val) {ω : a.samples | x ≤ spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r} ≤
      ENNReal.ofReal (Real.exp (-x^2 / (2 * V))) := by
  apply subGaussian_tail_of_compensated (a.spatialSlabIncrement_measurable A ε r).aemeasurable hV hx
  intro θ
  calc
    _ ≤ ∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) A ε r - θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val) := by
      apply lintegral_mono
      intro ω
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg θ)]
    _ ≤ 1 := a.spatial_slab_terminal_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound θ

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma hasSubgaussianMGF_of_compensated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (c : ℝ≥0)
    (h : ∀ θ : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω - θ^2 * c / 2)) ∂μ) ≤ 1) :
    HasSubgaussianMGF X c μ := by
  have hb (θ : ℝ) : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (c * θ^2 / 2)) := by
    have he (ω : Ω) : Real.exp (θ * X ω) = Real.exp (c * θ^2 / 2) *
        Real.exp (θ * X ω - θ^2 * c / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul'' _ (((hX.const_mul θ).sub_const (θ^2*c/2)).exp.ennreal_ofReal)]
    simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (c * θ^2/2)))) (h θ)
  have hi (θ : ℝ) : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
    refine ⟨(hX.const_mul θ).exp.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)).mpr
    exact (hb θ).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, fun θ => ?_⟩
  change (∫ ω, Real.exp (θ * X ω) ∂μ) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le) (hi θ).1]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb θ)).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)

lemma HasSubgaussianMGF.mono_parameter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun θ => (h.mgf_le θ).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg θ)) (by norm_num)

 

lemma subgaussian_sum_amplitudes
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (b : ℕ → ℝ≥0) (N : ℕ)
    (h : ∀ n < N, HasSubgaussianMGF (X n) (b n ^ 2) μ) :
    HasSubgaussianMGF (fun ω => ∑ n ∈ Finset.range N, X n ω)
      ((∑ n ∈ Finset.range N, b n)^2) μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsum := (ih (fun n hn => h n (Nat.lt_succ_of_lt hn))).add (h N (Nat.lt_succ_self N))
    simpa only [NNReal.sqrt_sq, Finset.sum_range_succ] using hsum

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def slabAmplitude (κ q : ℝ) (A : Set ℂ) : ℝ :=
  Real.sqrt (((Real.sqrt κ * greenExponent κ * q ^ (-codimension κ)) ^ 2 / 2) *
    (layerGreenConstant * (volume A).toReal))

lemma slabAmplitude_nonneg (κ q : ℝ) (A : Set ℂ) : 0 ≤ slabAmplitude κ q A :=
  Real.sqrt_nonneg _

lemma slabVariance_real_formula (κ ε r : ℝ) (A : Set ℂ) :
    slabVariance κ ε r A =
      ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (layerGreenConstant * r^2 * (volume A).toReal)) := by
  simp only [slabVariance, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (show 0 ≤ (Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4 by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (mul_nonneg layerGreenConstant_pos.le (sq_nonneg r))]

lemma slabVariance_scale (κ q r : ℝ) (A : Set ℂ) (hq : 0 < q) (hr : 0 < r) :
    slabVariance κ (q*r) r A =
      (slabAmplitude κ q A * r ^ (1 - codimension κ)) ^ 2 := by
  rw [slabVariance_real_formula, Real.mul_rpow hq.le hr.le]
  have he : r ^ (1 - codimension κ) = r * r ^ (-codimension κ) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  rw [he]
  symm
  rw [mul_pow, slabAmplitude, Real.sq_sqrt]
  · ring
  · exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (mul_nonneg layerGreenConstant_pos.le ENNReal.toReal_nonneg)

lemma slabVariance_scale_le {κ q ε r : ℝ} (A : Set ℂ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq : 0 < q) (hr : 0 < r) (hqr : q*r ≤ ε) :
    slabVariance κ ε r A ≤ (slabAmplitude κ q A * r ^ (1 - codimension κ)) ^ 2 := by
  rw [← slabVariance_scale κ q r A hq hr, slabVariance_real_formula, slabVariance_real_formula]
  have hL := layerGreenConstant_pos.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (sq_le_sq₀
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
      (Real.rpow_nonneg ((mul_pos hq hr).trans_le hqr).le _))
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
      (Real.rpow_nonneg (mul_pos hq hr).le _))).mpr
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hq hr) hqr (neg_nonpos.mpr (codimension_pos κ hκ8).le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialRealMass_sub_eq_slab
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A =
      spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r := by
  exact (integral_sub (a.spatialGreenWeight_spatial_integrable hκ hκ8 ε hε A hA hfin
    (fun z hz => hεr.trans (hheight z hz)) ω)
    (a.spatialGreenWeight_spatial_integrable hκ hκ8 r (hε.trans_le hεr) A hA hfin hheight ω)).symm

 

end RegularSLEPresentation
end SLEExactGauge
end
end
end
end
end

end OAI
