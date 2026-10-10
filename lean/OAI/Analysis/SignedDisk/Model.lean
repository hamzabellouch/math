import Mathlib

namespace OAI

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

namespace CenteredDiskEndpoint

/-- The Euclidean plane, not the product space with its max norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def diskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ :=
  (∫ y in Metric.ball x r, f y) / (Real.pi * r ^ 2)

/-- Absolute disk average, retaining possible infinite values. -/
def absoluteDiskAverage (f : Plane → ℝ) (x : Plane) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Metric.ball x r, ENNReal.ofReal |f y|) /
    ENNReal.ofReal (Real.pi * r ^ 2)

/-- The actual centered disk maximal function, over every positive real radius. -/
def maximal (f : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), absoluteDiskAverage f x r

/-- Real representative; the endpoint also asserts that `maximal f` is finite a.e. -/
def maximalReal (f : Plane → ℝ) (x : Plane) : ℝ := (maximal f x).toReal

/-- The i-th coordinate derivative of a smooth test function. -/
def testPartial (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- Distributional first derivatives represented by a vector-valued function. -/
def HasWeakGradient (f : Plane → ℝ) (g : Plane → Plane) : Prop :=
  ∀ (φ : Plane → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ∀ i : Fin 2, (∫ x, f x * testPartial φ i x) = -∫ x, g x i * φ x

/-- Real inhomogeneous W^(1,1) on the whole plane. -/
def InW11 (f : Plane → ℝ) : Prop :=
  Integrable f ∧ ∃ g : Plane → Plane, Integrable g ∧ HasWeakGradient f g

/-- Local W^(1,1), expressed using the same distributional gradient convention. -/
def InW11Loc (f : Plane → ℝ) : Prop :=
  LocallyIntegrable f ∧
    ∃ g : Plane → Plane, LocallyIntegrable g ∧ HasWeakGradient f g

/-- The gradient L1 norm in Euclidean norm. -/
def gradientNorm (g : Plane → Plane) : ℝ := ∫ x, ‖g x‖

/-- Signed envelope over all real radii in the closed band, including its endpoints. -/
def signedBand (f : Plane → ℝ) (a b : ℝ) (x : Plane) : ℝ :=
  sSup ((fun r => diskAverage f x r) '' Icc a b)

def SignedFiniteBandStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ (a : ℝ), 0 < a → ∀ m : ℕ,
      LocallyIntegrable (signedBand f a ((2 : ℝ)^m * a)) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (signedBand f a ((2 : ℝ)^m * a)) G ∧
        gradientNorm G ≤ C * gradientNorm (gradient f)

/-- Exact endpoint, including finiteness before passing to the real representative.
Quantifying the input gradient makes the norm bound independent of a choice of
representative of its weak derivatives. -/
def EndpointStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Plane → ℝ) (g : Plane → Plane),
      Integrable f → Integrable g → HasWeakGradient f g →
      (∀ᵐ x, maximal f x ≠ ⊤) ∧
      LocallyIntegrable (maximalReal f) ∧
      InW11Loc (maximalReal f) ∧
      ∃ G : Plane → Plane, Integrable G ∧
        HasWeakGradient (maximalReal f) G ∧ gradientNorm G ≤ C * gradientNorm g

/-- The normalization is precisely planar Lebesgue disk area. -/
theorem volume_disk (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_nonneg,
    ENNReal.ofReal_pow hr]
  exact mul_comm _ _

/-- For every admissible input and positive radius the extended average agrees
with the real absolute-value average, rather than a signed average. -/
theorem absoluteDiskAverage_eq_ofReal {f : Plane → ℝ} {x : Plane} {r : ℝ}
    (hf : IntegrableOn f (Metric.ball x r)) (hr : 0 < r) :
    absoluteDiskAverage f x r = ENNReal.ofReal (diskAverage (fun y => |f y|) x r) := by
  have hden : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  rw [absoluteDiskAverage, diskAverage, ENNReal.ofReal_div_of_pos hden,
    ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun y => abs_nonneg (f y)))]

theorem absoluteDiskAverage_ne_top {f : Plane → ℝ} {x : Plane} {r : ℝ}
    (hf : IntegrableOn f (Metric.ball x r)) (hr : 0 < r) :
    absoluteDiskAverage f x r ≠ ⊤ := by
  rw [absoluteDiskAverage_eq_ofReal hf hr]
  exact ENNReal.ofReal_ne_top

theorem absoluteDiskAverage_le_maximal (f : Plane → ℝ) (x : Plane) {r : ℝ}
    (hr : 0 < r) : absoluteDiskAverage f x r ≤ maximal f x := by
  exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)

theorem maximal_abs (f : Plane → ℝ) : maximal (fun y => |f y|) = maximal f := by
  funext x
  simp only [maximal, absoluteDiskAverage, abs_abs]

theorem inW11_of_gradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : Integrable f) (hg : Integrable g) (hw : HasWeakGradient f g) : InW11 f :=
  ⟨hf, g, hg, hw⟩

theorem inW11Loc_of_gradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) (hw : HasWeakGradient f g) : InW11Loc f :=
  ⟨hf, g, hg.locallyIntegrable, hw⟩

theorem integral_smul_sub_const {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {b : α → E} {K : α → ℝ}
    (hb : Integrable b μ) (hK : Integrable (fun y => K y • b y) μ)
    (hzero : ∫ y, b y ∂μ = 0) (c : ℝ) :
    (∫ y, (K y - c) • b y ∂μ) = ∫ y, K y • b y ∂μ := by
  simp_rw [sub_smul]
  have hc : Integrable (fun y => c • b y) μ := hb.smul c
  rw [integral_sub hK hc, integral_smul, hzero, smul_zero, sub_zero]

/-- The small-support zero-mass discount for actual integrable vector densities.
The kernel need only be Lipschitz; no smoothness or unproved moment estimate is
assumed. -/
theorem localized_cancellation {b : Plane → Plane} {K : Plane → ℝ}
    (hb : Integrable b) (hzero : ∫ y, b y = 0)
    {L : ℝ≥0} (hK : LipschitzWith L K) (z : Plane) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y - z‖ ≤ s) :
    ‖∫ y, K y • b y‖ ≤ (L : ℝ) * s * ∫ y, ‖b y‖ := by
  have hbound : ∀ᵐ y, ‖(K y - K z) • b y‖ ≤ ((L : ℝ) * s) * ‖b y‖ := by
    filter_upwards [hsupp] with y hy
    by_cases hby : b y = 0
    · simp [hby]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right
        ((hK.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
        (norm_nonneg _)
  have hdiff : Integrable (fun y => (K y - K z) • b y) :=
    (hb.norm.smul ((L : ℝ) * s)).mono'
      ((hK.continuous.sub continuous_const).aestronglyMeasurable.smul hb.aestronglyMeasurable)
      hbound
  have hprod : Integrable (fun y => K y • b y) := by
    have h := hdiff.add (hb.smul (K z))
    change Integrable (fun y => (K y - K z) • b y + K z • b y) at h
    simpa only [← add_smul, sub_add_cancel] using h
  rw [← integral_smul_sub_const hb hprod hzero (K z)]
  calc
    ‖∫ y, (K y - K z) • b y‖ ≤ ∫ y, ((L : ℝ) * s) * ‖b y‖ :=
      norm_integral_le_of_norm_le (hb.norm.smul ((L : ℝ) * s)) hbound
    _ = (L : ℝ) * s * ∫ y, ‖b y‖ := integral_const_mul _ _

open InnerProductSpace
open scoped RealInnerProductSpace

/-- A change of representatives on null sets does not change weak derivatives. -/
theorem HasWeakGradient.congr_ae {f f' : Plane → ℝ} {g g' : Plane → Plane}
    (h : HasWeakGradient f g) (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    HasWeakGradient f' g' := by
  intro φ hφ hφc i
  calc
    (∫ x, f' x * testPartial φ i x) = ∫ x, f x * testPartial φ i x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    _ = -∫ x, g x i * φ x := h φ hφ hφc i
    _ = -∫ x, g' x i * φ x := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

/-- The distributional gradient is unique as an a.e. class. -/
theorem HasWeakGradient.ae_unique {f : Plane → ℝ} {g g' : Plane → Plane}
    (h : HasWeakGradient f g) (h' : HasWeakGradient f g')
    (hg : LocallyIntegrable g) (hg' : LocallyIntegrable g') : g =ᵐ[volume] g' := by
  have hcoord (i : Fin 2) : ∀ᵐ x, g x i = g' x i := by
    have hgi : LocallyIntegrable (fun x => g x i) := fun x =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrableAtFilter_comp (hg x)
    have hgi' : LocallyIntegrable (fun x => g' x i) := fun x =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrableAtFilter_comp (hg' x)
    apply ae_eq_of_integral_contDiff_smul_eq hgi hgi'
    intro φ hφ hφc
    have heq := (h φ hφ hφc i).symm.trans (h' φ hφ hφc i)
    simpa only [neg_inj, smul_eq_mul, mul_comm] using heq
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  ext i
  exact hx i

/-- Coordinate convention agreement with Mathlib's classical Euclidean gradient. -/
theorem classicalGradient_apply (f : Plane → ℝ) (x : Plane) (i : Fin 2) :
    gradient f x i = testPartial f i x := by
  simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul, testPartial] using
    (inner_gradient_left (f := f) (x := x) (y := EuclideanSpace.single i 1))

/-- No integrability hypothesis is smuggled into the definition of the weak
identity: every C¹ function satisfies it when tested against compact support. -/
theorem contDiff_hasWeakGradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    HasWeakGradient f (gradient f) := by
  intro φ hφ hφc i
  have hfd : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφd : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφds : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  simp_rw [classicalGradient_apply, testPartial]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hfd.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · exact (hf.continuous.mul hφd).integrable_of_hasCompactSupport hφds.mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  · intro x _
    exact hf.differentiable one_ne_zero x
  · intro x _
    exact hφ.differentiable (by simp) x

end CenteredDiskEndpoint

open scoped RealInnerProductSpace

namespace CenteredDiskEndpoint
open Filter

/-- Spherical boundaries are null, so the choice of an open disk does not alter
Lebesgue differentiation averages. -/
theorem disk_ae_eq_closedDisk (x : Plane) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
  · exact (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

theorem average_closedDisk_eq (f : Plane → ℝ) (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (⨍ y in Metric.closedBall x r, f y) = diskAverage f x r := by
  rw [← setAverage_congr (disk_ae_eq_closedDisk x r), setAverage_eq,
    diskAverage, measureReal_def, volume_disk x hr, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- Almost every point is a Lebesgue point for absolute disk averages. -/
theorem ae_tendsto_diskAverage_abs {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, Tendsto (fun r => diskAverage (fun y => |f y|) x r)
      (𝓝[>] (0 : ℝ)) (𝓝 |f x|) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf.abs.locallyIntegrable 0]
    with x hx
  have h := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall (fun r => by simp))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact average_closedDisk_eq (fun y => |f y|) x hr.le

/-- Away from zero the denominator alone bounds all absolute averages. -/
theorem diskAverage_abs_le_of_radius_le {f : Plane → ℝ} (hf : Integrable f)
    (x : Plane) {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    diskAverage (fun y => |f y|) x r ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) := by
  have hr : 0 < r := ha.trans_le har
  have hnum : (∫ y in Metric.ball x r, |f y|) ≤ ∫ y, |f y| :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun y => abs_nonneg (f y))) hf.abs
  have hden : Real.pi * a ^ 2 ≤ Real.pi * r ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ ha.le hr.le).2 har) Real.pi_nonneg
  dsimp [diskAverage]
  calc
    (∫ y in Metric.ball x r, |f y|) / (Real.pi * r ^ 2) ≤
        (∫ y, |f y|) / (Real.pi * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) :=
      div_le_div_of_nonneg_left (integral_nonneg (fun y => abs_nonneg (f y)))
        (by positivity) hden

/-- A genuine clause of the endpoint, in fact valid for every L¹ input. No
maximal bound, gradient hypothesis, or selected radius is used here. -/
theorem ae_maximal_ne_top {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, maximal f x ≠ ⊤ := by
  filter_upwards [ae_tendsto_diskAverage_abs hf] with x hx
  obtain ⟨C, hC⟩ := hx.isBoundedUnder_le
  obtain ⟨a, ha, haC⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hC
  have hbound (r : ℝ) (hr : 0 < r) :
      diskAverage (fun y => |f y|) x r ≤ max C ((∫ y, |f y|) / (Real.pi * a ^ 2)) := by
    by_cases hra : r ≤ a
    · exact (haC ⟨hr, hra⟩).trans (le_max_left _ _)
    · exact (diskAverage_abs_le_of_radius_le hf x ha (le_of_not_ge hra)).trans
        (le_max_right _ _)
  have hmax : maximal f x ≤ ENNReal.ofReal
      (max C ((∫ y, |f y|) / (Real.pi * a ^ 2))) := by
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    rw [absoluteDiskAverage_eq_ofReal hf.integrableOn hr]
    exact ENNReal.ofReal_le_ofReal (hbound r hr)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmax

end CenteredDiskEndpoint

open MeasureTheory Set Filter
open scoped Topology ENNReal

open scoped Real RealInnerProductSpace

namespace DiskGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mem_tangent_ball_iff {z y θ : E} (hθ : ‖θ‖ = 1) {L : ℝ} (hL : 0 < L) :
    y ∈ Metric.ball (z + L • θ) L ↔ ‖y - z‖ ^ 2 < 2 * L * ⟪y - z, θ⟫ := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hv : y - (z + L • θ) = (y - z) - L • θ := by abel
  rw [hv, ← sq_lt_sq₀ (norm_nonneg _) hL.le, norm_sub_sq_real,
    norm_smul, Real.norm_eq_abs, abs_of_pos hL, hθ, mul_one, real_inner_smul_right]
  constructor <;> intro h <;> nlinarith

theorem tangent_ball_mono {z θ : E} (hθ : ‖θ‖ = 1) {L L' : ℝ}
    (hL : 0 < L) (hLL' : L ≤ L') :
    Metric.ball (z + L • θ) L ⊆ Metric.ball (z + L' • θ) L' := by
  intro y hy
  rw [mem_tangent_ball_iff hθ hL] at hy
  rw [mem_tangent_ball_iff hθ (hL.trans_le hLL')]
  have hinner : 0 < ⟪y - z, θ⟫ := by
    by_contra hh
    have hh' : ⟪y - z, θ⟫ ≤ 0 := le_of_not_gt hh
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * L by positivity) hh'
    nlinarith [sq_nonneg ‖y - z‖]
  exact hy.trans_le (mul_le_mul_of_nonneg_right (by linarith) hinner.le)

def entryParameter (z y θ : E) : ℝ := ‖y - z‖ ^ 2 / (2 * ⟪y - z, θ⟫)

theorem mem_tangent_ball_iff_entry {z y θ : E} (hθ : ‖θ‖ = 1)
    {L : ℝ} (hL : 0 < L) (ha : 0 < ⟪y - z, θ⟫) :
    y ∈ Metric.ball (z + L • θ) L ↔ entryParameter z y θ < L := by
  rw [mem_tangent_ball_iff hθ hL, entryParameter, div_lt_iff₀ (by positivity)]
  ring_nf

/-- Uniform estimate on the affine difference of squared distances in a thin shell. -/
theorem shell_square_error {l δ d : ℝ} (hl : 0 ≤ l) (hl3 : l ≤ 3)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hd : 0 ≤ d) (hclose : |d - l| ≤ 2 * δ) :
    |d ^ 2 - l ^ 2| ≤ 13 * δ := by
  have hd_upper : d ≤ l + 2 * δ := (abs_le.mp hclose).2 |> fun h => by linarith
  have hsum : 0 ≤ d + l := add_nonneg hd hl
  calc
    |d ^ 2 - l ^ 2| = |d - l| * (d + l) := by
      rw [show d ^ 2 - l ^ 2 = (d - l) * (d + l) by ring, abs_mul, abs_of_nonneg hsum]
    _ ≤ (2 * δ) * (d + l) := mul_le_mul_of_nonneg_right hclose hsum
    _ ≤ 13 * δ := by nlinarith

/-- A shell point separated from the tangency point has positive radial projection. -/
theorem shell_projection_lower {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hl : 0 < l) (hl3 : l ≤ 3)
    (hδ : δ ≤ ρ ^ 2 / 1600) (hw : ρ ^ 2 ≤ w2)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    ρ ^ 2 / 12 ≤ a := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have he := (abs_le.mp herr).2
  have hla : 0 < a := by nlinarith
  nlinarith

theorem entry_window {ρ δ l a w2 : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (ha : ρ ^ 2 / 12 ≤ a)
    (herr : |w2 - 2 * l * a| ≤ 13 * δ) :
    |w2 / (2 * a) - l| ≤ 78 * δ / ρ ^ 2 := by
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have h2a : 0 < 2 * a := by positivity
  rw [show w2 / (2 * a) - l = (w2 - 2 * l * a) / (2 * a) by field_simp,
    abs_div, abs_of_pos h2a]
  calc
    |w2 - 2 * l * a| / (2 * a) ≤ 13 * δ / (2 * a) :=
      div_le_div_of_nonneg_right herr h2a.le
    _ ≤ 78 * δ / ρ ^ 2 := by
      apply (div_le_div_iff₀ h2a hr2).2
      nlinarith [mul_le_mul_of_nonneg_right ha hδ]

/-- Bound for the entry parameter for an actual shell near a tangent disk. -/
theorem shell_entry_window {z y θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600)
    (hsep : ρ ≤ ‖y - z‖)
    (hclose : |dist y (z + l • θ) - l| ≤ 2 * δ) :
    ρ ^ 2 / 12 ≤ ⟪y - z, θ⟫ ∧
    |entryParameter z y θ - l| ≤ 78 * δ / ρ ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hδ1 : δ ≤ 1 / 4 := by nlinarith
  have hsq : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hd := shell_square_error hl0.le hl3 hδ.le hδ1 (dist_nonneg (x := y)) hclose
  have hv : y - (z + l • θ) = (y - z) - l • θ := by abel
  have herr : |‖y - z‖ ^ 2 - 2 * l * ⟪y - z, θ⟫| ≤ 13 * δ := by
    rw [dist_eq_norm, hv, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hl0, hθ, mul_one] at hd
    convert hd using 1
    congr 1
    ring
  have ha := shell_projection_lower hρ hl0 hl3 hδρ hsq herr
  exact ⟨ha, entry_window hρ hδ.le ha herr⟩

theorem earlier_tangent_disk_subset {z θ : E} (hθ : ‖θ‖ = 1) {l ρ δ : ℝ}
    (hl : 1 / 2 ≤ l) (hl3 : l ≤ 3) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ ^ 2 / 1600) :
    {y : E | ρ ≤ ‖y - z‖} ∩
      Metric.ball (z + (l - 200 * δ / ρ ^ 2) • θ) (l - 200 * δ / ρ ^ 2) ⊆
      Metric.ball (z + l • θ) (l - 2 * δ) := by
  let v : ℝ := 200 * δ / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hvpos : 0 < v := by dsimp [v]; positivity
  have hvsmall : v ≤ 1 / 8 := by
    dsimp [v]
    apply (div_le_iff₀ hr2).2
    linarith
  have hv_eq : v * ρ ^ 2 = 200 * δ := by
    dsimp [v]; exact div_mul_cancel₀ _ hr2.ne'
  have hl0 : 0 < l := by linarith
  have hlv : 0 < l - v := by linarith
  have hδquarter : δ ≤ 1 / 4 := by nlinarith
  have hrad : 0 < l - 2 * δ := by nlinarith
  rintro y ⟨hsep, hy⟩
  change y ∈ Metric.ball (z + (l - v) • θ) (l - v) at hy
  rw [mem_tangent_ball_iff hθ hlv] at hy
  have hnorm : ρ ^ 2 ≤ ‖y - z‖ ^ 2 :=
    (sq_le_sq₀ hρ.le (norm_nonneg _)).2 hsep
  have hapos : 0 < ⟪y - z, θ⟫ := by
    by_contra ha
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ 2 * (l - v) by positivity) (le_of_not_gt ha)
    nlinarith
  have halower : ρ ^ 2 / 6 < ⟪y - z, θ⟫ := by nlinarith
  have hva := mul_lt_mul_of_pos_left halower hvpos
  have hsqdist : dist y (z + l • θ) ^ 2 < (l - 2 * δ) ^ 2 := by
    rw [dist_eq_norm, show y - (z + l • θ) = (y - z) - l • θ by abel,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hl0, hθ, mul_one]
    nlinarith [mul_le_mul_of_nonneg_right hl3 hδ.le]
  exact (sq_lt_sq₀ dist_nonneg hrad.le).1 hsqdist

end DiskGeometry

end SignedDisk

end

end OAI
