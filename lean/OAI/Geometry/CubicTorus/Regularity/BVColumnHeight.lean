import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVGraphEnergy

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalColumnHeight (U : Set Torus) (a : Torus) (n : Cover) (r : ℝ) (y : Plane) : ℝ :=
  (∫ t in Icc (-r / 4) (r / 4),
    characteristic U (a + quotientMap (normalPlaneEmbedding n y + t • n))) - r / 4

lemma measurable_normalColumnHeight {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) : Measurable (normalColumnHeight U a n r) := by
  have hc : Continuous (fun p : Plane × ℝ ↦
      a + quotientMap (normalPlaneEmbedding n p.1 + p.2 • n)) :=
    continuous_const.add (continuous_quotientMap.comp
      (((normalPlaneLinearIsometry n).continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)))
  exact (((measurable_characteristic hU).comp hc.measurable).stronglyMeasurable.integral_prod_right').measurable.sub_const _

lemma normalColumn_integrable {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (y : Plane) :
    IntegrableOn (fun t ↦ characteristic U
      (a + quotientMap (normalPlaneEmbedding n y + t • n))) (Icc (-r / 4) (r / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_characteristic hU).comp
      (continuous_const.add (continuous_quotientMap.comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U _

lemma normalColumnHeight_bound {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) (y : Plane) :
    |normalColumnHeight U a n r y| ≤ r / 4 := by
  have hi := normalColumn_integrable hU a n r y
  have hlo : 0 ≤ ∫ t in Icc (-r / 4) (r / 4),
      characteristic U (a + quotientMap (normalPlaneEmbedding n y + t • n)) :=
    integral_nonneg (fun t ↦ characteristic_nonneg U _)
  have hhi := integral_mono hi (integrable_const (1 : ℝ)) (fun t ↦
    (le_abs_self _).trans (characteristic_bound U _))
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ r / 4 - -r / 4)] at hhi
  dsimp [normalColumnHeight]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma trapped_frontier_torus_height {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} {r ε : ℝ}
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a r) :
    |⟪n, shortestLift (c - a)⟫| ≤ ε * r := by
  apply abs_le.mpr
  constructor
  · by_contra! hh
    have hmem := htrap.2 (show c ∈ normalCap a (-n) r (ε * r) from
      ⟨hc.2, by rw [inner_neg_left]; linarith⟩)
    have hb := hc.1
    rw [frontier, hU.interior_eq] at hb
    exact hb.2 hmem
  · by_contra! hh
    exact htrap.1 ⟨hc.2, hh⟩ (frontier_subset_closure hc.1)

theorem normalColumnHeight_eq_good_height {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r ε η : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (hη : η ≤ 1 / 2)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r / 2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c - a)) ∈ Metric.ball (0 : Plane) (r / 4)) :
    normalColumnHeight U a n r (normalPlaneCoordinates n (shortestLift (c - a))) =
      ⟪n, shortestLift (c - a)⟫ := by
  let y := normalPlaneCoordinates n (shortestLift (c - a))
  let q := ⟪n, shortestLift (c - a)⟫
  let f : ℝ → Torus := fun t ↦ a + quotientMap (normalPlaneEmbedding n y + t • n)
  have hphase := trapped_good_column_phases hU hn hr hrsmall hε hη htrap hc hcone hy
  have hq : |q| ≤ ε * r := trapped_frontier_torus_height hU htrap
    ⟨hc.1, (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) hc.2⟩
  have hqlo : -r / 4 ≤ q := by
    have hh := (abs_le.mp hq).1
    nlinarith [mul_lt_mul_of_pos_right hε hr]
  have hqhi : q ≤ r / 4 := by
    have hh := (abs_le.mp hq).2
    nlinarith [mul_lt_mul_of_pos_right hε hr]
  have hfc : f q = c := by
    dsimp [f, q, y]
    rw [normalPlaneCoordinates_reconstruct hn, quotientMap_shortestLift, add_sub_cancel]
  have heq : ∀ t ∈ Icc (-r / 4) (r / 4),
      characteristic U (f t) = (Iio q).indicator (fun _ : ℝ ↦ (1 : ℝ)) t := by
    intro t ht
    by_cases htq : t < q
    · have htU : f t ∈ U := hphase.1 t ht htq
      simp [characteristic, htU, htq]
    · have htU : f t ∉ U := by
        rcases lt_or_eq_of_le (le_of_not_gt htq) with hlt | he
        · exact fun hh ↦ hphase.2 t ht hlt (subset_closure hh)
        · rw [← he, hfc]
          have hb := hc.1
          rw [frontier, hU.interior_eq] at hb
          exact hb.2
      simp [characteristic, htU, htq]
  have hset : Icc (-r / 4) (r / 4) ∩ Iio q = Ico (-r / 4) q := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, h.2.le.trans hqhi⟩, h.2⟩
  change (∫ t in Icc (-r / 4) (r / 4), characteristic U (f t)) - r / 4 = q
  rw [setIntegral_congr_fun measurableSet_Icc heq, setIntegral_indicator measurableSet_Iio,
    hset, integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hqlo)]
  ring

theorem normalColumnHeight_disagreement_volume_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀ * ρ ^ 2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε η : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (hη : η ≤ 1 / 2)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) :
    (volume : Measure Plane) {y ∈ Metric.ball (0 : Plane) (r / 4) |
      normalColumnHeight U a n r y ≠ g y} ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c₀)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
  let Q : Torus → Plane := fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))
  have hcover : {y ∈ Metric.ball (0 : Plane) (r / 4) |
      normalColumnHeight U a n r y ≠ g y} ⊆
      Q '' ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := trapped_boundary_projects_disk hU a hn hr hrsmall hε htrap hy.1
    have hxS : x ∉ S := by
      intro hm
      apply hy.2
      rw [← hxy, hS x hm]
      exact normalColumnHeight_eq_good_height hU hn hr hrsmall hε hη htrap hx
        (hcone x hm) (by simpa only [hxy] using hy.1)
    exact ⟨x, ⟨hx, hxS⟩, hxy⟩
  apply (measure_mono hcover).trans
  apply plane_projection_volume_le_perimeter σ (frontier U) hR hc₀ hl n a _
    (fun x hx ↦ hx.1.1)
  intro x hx
  exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ 1 / 4)) hx.1.2

theorem normalColumnHeight_graph_L1_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀ * ρ ^ 2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε η : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (hη : η ≤ 1 / 2)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ) (hg : Measurable g)
    (hheight : ∀ y ∈ Metric.ball (0 : Plane) (r / 4), |g y| ≤ r / 4)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) :
    (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
      ENNReal.ofReal |normalColumnHeight U a n r y - g y| ∂(volume : Measure Plane)) ≤
      ENNReal.ofReal (r / 2) *
        (((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c₀)) *
          (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r / 2)) \ S)) := by
  let D : Set Plane := {y ∈ Metric.ball (0 : Plane) (r / 4) |
    normalColumnHeight U a n r y ≠ g y}
  have hD : MeasurableSet D := measurableSet_ball.inter
    (measurableSet_eq_fun (measurable_normalColumnHeight hU.measurableSet a n r) hg).compl
  have hbound : ∀ y ∈ Metric.ball (0 : Plane) (r / 4),
      ENNReal.ofReal |normalColumnHeight U a n r y - g y| ≤
        D.indicator (fun _ ↦ ENNReal.ofReal (r / 2)) y := by
    intro y hy
    by_cases he : normalColumnHeight U a n r y = g y
    · simp [he]
    · rw [Set.indicator_of_mem (show y ∈ D from ⟨hy, he⟩)]
      apply ENNReal.ofReal_le_ofReal
      have hh := abs_sub_le (normalColumnHeight U a n r y) 0 (g y)
      simp only [sub_zero, zero_sub, abs_neg] at hh
      linarith [normalColumnHeight_bound hU.measurableSet a n hr.le y, hheight y hy]
  calc
    _ ≤ ∫⁻ y in Metric.ball (0 : Plane) (r / 4),
        D.indicator (fun _ ↦ ENNReal.ofReal (r / 2)) y :=
      setLIntegral_mono' measurableSet_ball hbound
    _ = ENNReal.ofReal (r / 2) * (volume : Measure Plane) D := by
      rw [lintegral_indicator hD, lintegral_const, Measure.restrict_restrict hD]
      simp only [Measure.restrict_apply_univ, Set.inter_eq_left.mpr (show D ⊆
        Metric.ball (0 : Plane) (r / 4) from fun _ h ↦ h.1)]
    _ ≤ _ := mul_le_mul_right (normalColumnHeight_disagreement_volume_le hU σ hR hc₀ hl
      a hn hr hrsmall hε hη htrap S g hS hcone) _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

def normalScalarTest (a n : Cover) (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) : ℝ :=
  χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a))

lemma normalScalarTest_contDiff (a n : Cover) {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalScalarTest a n χ φ) := by
  exact (hχ.comp (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).mul
    (hφ.comp ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma normalRotation_single_succ (n : Cover) (i : Fin 2) :
    normalRotation n (EuclideanSpace.single i.succ 1) =
      normalPlaneEmbedding n (EuclideanSpace.single i 1) := by
  rw [normalPlaneEmbedding, normalProductChart_apply]
  congr 1
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp
  · simp [Pi.single_apply]

lemma normalScalarTest_normal_line (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) (t : ℝ) :
    normalScalarTest a n χ φ (x + t • n) =
      χ (⟪n, x - a⟫ + t) * φ (normalPlaneCoordinates n (x - a)) := by
  have he : x + t • n - a = (x - a) + t • n := by abel
  rw [normalScalarTest, he, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, map_add, map_smul, normalPlaneCoordinates_normal hn,
    smul_zero, add_zero]

lemma normalScalarTest_plane_line (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) (u : Plane) (t : ℝ) :
    normalScalarTest a n χ φ (x + t • normalPlaneEmbedding n u) =
      χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a) + t • u) := by
  have he : x + t • normalPlaneEmbedding n u - a =
      (x - a) + t • normalPlaneEmbedding n u := by abel
  rw [normalScalarTest, he, inner_add_right, inner_smul_right,
    normalPlaneEmbedding_inner hn, mul_zero, add_zero, map_add, map_smul,
    normalPlaneCoordinates_embedding]

theorem laplacian_normalScalarTest (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) :
    Δ (normalScalarTest a n χ φ) x =
      iteratedDeriv 2 χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) +
      χ ⟪n, x - a⟫ * Δ φ (normalPlaneCoordinates n (x - a)) := by
  have htest := normalScalarTest_contDiff a n hχ hφ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map (normalRotation n))]
  simp only [OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]
  rw [Fin.sum_univ_succ, normalRotation_axis hn]
  have hv : iteratedFDeriv ℝ 2 (normalScalarTest a n χ φ) x ![n, n] =
      iteratedDeriv 2 χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) := by
    rw [iteratedFDeriv_two_line htest]
    simp_rw [normalScalarTest_normal_line a hn]
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_comp_const_add]
    simp
  rw [hv]
  congr 1
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin 2) ℝ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalRotation_single_succ, iteratedFDeriv_two_line htest]
  simp_rw [normalScalarTest_plane_line a hn]
  rw [iteratedDeriv_const_mul_field, EuclideanSpace.basisFun_apply,
    iteratedFDeriv_two_line hφ]

lemma fderiv_normalScalarTest_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) :
    fderiv ℝ (normalScalarTest a n χ φ) x n =
      deriv χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) := by
  have htest := normalScalarTest_contDiff a n hχ hφ
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • n) n 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add x
  have hh := (((htest.differentiable (by simp)) (x + (0 : ℝ) • n)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt (fun t : ℝ ↦ x + t • n) n 0 from hl))
  have hh' : deriv (fun t : ℝ ↦ normalScalarTest a n χ φ (x + t • n)) 0 =
      fderiv ℝ (normalScalarTest a n χ φ) x n := by
    simpa [Function.comp_def] using hh.deriv
  rw [← hh']
  have he := funext (normalScalarTest_normal_line a hn χ φ x)
  rw [he, deriv_mul_const, deriv_comp_const_add]
  · simp
  · exact (hχ.comp (contDiff_const.add contDiff_id)).differentiable (by simp) |>.differentiableAt

lemma normalScalarTest_tsupport (a n : Cover) (χ : ℝ → ℝ) (φ : Plane → ℝ) :
    tsupport (normalScalarTest a n χ φ) ⊆
      {x | ⟪n, x - a⟫ ∈ tsupport χ} ∩
        {x | normalPlaneCoordinates n (x - a) ∈ tsupport φ} := by
  apply closure_minimal _
    ((isClosed_closure.preimage (continuous_const.inner (continuous_id.sub continuous_const))).inter
      (isClosed_closure.preimage ((normalPlaneCoordinates n).continuous.comp
        (continuous_id.sub continuous_const))))
  intro x hx
  have hnz : χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) ≠ 0 := hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hnz),
    subset_tsupport _ (right_ne_zero_of_mul hnz)⟩

lemma normalScalarTest_tsupport_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ} {r : ℝ} (hr : 0 < r)
    (hχ : tsupport χ ⊆ Icc (-r / 3) (r / 3))
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    tsupport (normalScalarTest a n χ φ) ⊆ Metric.ball a r := by
  intro x hx
  have hh := normalScalarTest_tsupport a n χ φ hx
  have hv : |⟪n, x - a⟫| ≤ r / 3 := by
    have ht := hχ hh.1
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hp : ‖normalPlaneCoordinates n (x - a)‖ ≤ r / 3 := by
    simpa using hφ hh.2
  have htri := norm_add_le (normalPlaneEmbedding n (normalPlaneCoordinates n (x - a)))
    (⟪n, x - a⟫ • n)
  rw [normalPlaneCoordinates_reconstruct hn, normalPlaneEmbedding_norm, norm_smul,
    Real.norm_eq_abs, hn, mul_one] at htri
  change dist x a < r
  rw [dist_eq_norm]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalColumnChart (a n : Cover) : (ℝ × Plane) ≃ᵐ Cover :=
  (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
    (normalProductChart n)).trans (MeasurableEquiv.addLeft a)

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

lemma normalColumnChart_characteristic (U : Set Torus) (a : Cover) {n : Cover}
    (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    characteristic U (quotientMap (normalColumnChart a n (t, y))) =
      characteristic U (quotientMap a + quotientMap (normalPlaneEmbedding n y + t • n)) := by
  rw [normalColumnChart_apply a hn, quotientMap_add]

lemma normalColumnChart_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {r t : ℝ} (hr : 0 < r) {y : Plane} (ht : |t| ≤ r / 2)
    (hy : ‖y‖ ≤ r / 3) : normalColumnChart a n (t, y) ∈ Metric.ball a r := by
  rw [Metric.mem_ball, dist_eq_norm, normalColumnChart_apply a hn, add_sub_cancel_left]
  have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
  rw [normalPlaneEmbedding_norm, norm_smul, Real.norm_eq_abs, hn, mul_one] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalMove (n : Cover) (f : Cover → ℝ) (x : Cover) : Cover := x + f x • n

def normalJacobian (n : Cover) (f : Cover → ℝ) (x : Cover) : ℝ :=
  1 + fderiv ℝ f x n

def normalPullback (n : Cover) (f : Cover → ℝ) (F : Cover → Cover) (x : Cover) : Cover :=
  normalJacobian n f x • F (normalMove n f x) -
    fderiv ℝ f x (F (normalMove n f x)) • n

lemma normalMove_hasFDerivAt (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (normalMove n f)
      (ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight n) x := by
  exact (hasFDerivAt_id x).add (hf.hasFDerivAt.smul_const n)

lemma normalMove_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMove n f) := contDiff_id.add (hf.smul_const n)

lemma normalPullback_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (normalPullback n f F) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hG := hF.comp (normalMove_contDiff n hf)
  exact (contDiff_const.add (hd.clm_apply contDiff_const)).smul hG |>.sub
    ((hd.clm_apply hG).smul contDiff_const)

lemma divergence_comp_normalMove (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) {F : Cover → Cover}
    (hF : DifferentiableAt ℝ F (normalMove n f x)) :
    divergence (fun y ↦ F (normalMove n f y)) x =
      divergence F (normalMove n f x) +
        fderiv ℝ f x (fderiv ℝ F (normalMove n f x) n) := by
  have hd := (hF.hasFDerivAt.comp x (normalMove_hasFDerivAt n hf)).fderiv
  change fderiv ℝ (fun y ↦ F (normalMove n f y)) x = _ at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPullback_divergence (n : Cover) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (normalPullback n f F) x =
      normalJacobian n f x * divergence F (normalMove n f x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := normalMove_hasFDerivAt n hfd
  have hg := (hF.differentiable (by simp)).differentiableAt (x := normalMove n f x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const n x)).const_add 1
  have hb := hdf.hasFDerivAt.clm_apply hu
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)) n (F (normalMove n f x))
  change divergence (fun y ↦ normalJacobian n f y • F (normalMove n f y) -
    fderiv ℝ f y (F (normalMove n f y)) • n) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (normalJacobian n f) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (normalJacobian n f) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ F (normalMove n f y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (F (normalMove n f y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ normalJacobian n f y • F (normalMove n f y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (F (normalMove n f y)) • n) x := hB.smul_const n
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU, divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_normalMove n hfd hg]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, zero_add,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero, smul_eq_mul]
  dsimp only [normalJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphHeightExtension (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  g (normalPlaneCoordinates n (x-a))

def graphShear (a n : Cover) (g : Plane → ℝ) : Cover → Cover :=
  normalMove n (graphHeightExtension a n g)

lemma graphShear_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    normalPlaneCoordinates n (graphShear a n g x - a) = normalPlaneCoordinates n (x-a) := by
  rw [graphShear, normalMove, add_sub_right_comm, map_add, map_smul,
    normalPlaneCoordinates_normal hn, smul_zero, add_zero]

lemma graphShear_inverse (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) : Function.LeftInverse (graphShear a n (-g)) (graphShear a n g) := by
  intro x
  change graphShear a n g x + (-g) (normalPlaneCoordinates n (graphShear a n g x-a)) • n = x
  rw [graphShear_projection a hn]
  simp only [Pi.neg_apply, neg_smul, graphShear, normalMove, graphHeightExtension]
  abel

lemma graphShear_continuous (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    Continuous (graphShear a n g) := by
  unfold graphShear normalMove graphHeightExtension
  exact continuous_id.add ((hg.comp ((normalPlaneCoordinates n).continuous.comp
    (continuous_id.sub continuous_const))).smul continuous_const)

def graphShearHomeomorph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) : Cover ≃ₜ Cover where
  toFun := graphShear a n g
  invFun := graphShear a n (-g)
  left_inv := graphShear_inverse a hn g
  right_inv := by
    intro x
    simpa only [neg_neg] using graphShear_inverse a hn (-g) x
  continuous_toFun := graphShear_continuous a n hg
  continuous_invFun := graphShear_continuous a n hg.neg

lemma graphShear_columnChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphShear a n g (normalColumnChart a n (t,y)) = normalColumnChart a n (t+g y,y) := by
  change normalColumnChart a n (t,y) +
    g (normalPlaneCoordinates n (normalColumnChart a n (t,y)-a)) • n = _
  rw [normalColumnChart_projection a hn, normalColumnChart_apply a hn,
    normalColumnChart_apply a hn, add_smul]
  abel

lemma columnShear_measurePreserving {g : Plane → ℝ} (hg : Measurable g) :
    MeasurePreserving (fun p : ℝ × Plane ↦ (p.1+g p.2, p.2)) := by
  have hs : MeasurePreserving (fun p : Plane × ℝ ↦ (p.1, p.2+g p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y ↦ (measurePreserving_add_right volume (g y)).map_eq)
  have hh := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure ℝ))).comp (hs.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))))
  simpa only [Function.comp_def, Prod.swap, Measure.volume_eq_prod] using hh

lemma graphShear_measurePreserving (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Measurable g) : MeasurePreserving (graphShear a n g) := by
  have hi : MeasurePreserving (normalColumnChart a n).symm :=
    MeasurePreserving.symm (normalColumnChart a n) (normalColumnChart_measurePreserving a n)
  have hh := (normalColumnChart_measurePreserving a n).comp
    ((columnShear_measurePreserving hg).comp hi)
  convert hh using 1
  funext x
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart a n).surjective x
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact graphShear_columnChart a hn g t y

lemma graphHeightExtension_contDiff (a n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (graphHeightExtension a n g) :=
  hg.comp ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const))

lemma graphHeightExtension_fderiv (a n : Cover) {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (x : Cover) : fderiv ℝ (graphHeightExtension a n g) x =
      (fderiv ℝ g (normalPlaneCoordinates n (x-a))).comp (normalPlaneCoordinates n) := by
  unfold graphHeightExtension
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, graphHeightExtension] using
    ((hg _).hasFDerivAt.comp x hp).fderiv

lemma graphHeightExtension_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    fderiv ℝ (graphHeightExtension a n g) x n = 0 := by
  rw [graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    normalPlaneCoordinates_normal hn, map_zero]

lemma graphShear_jacobian (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    normalJacobian n (graphHeightExtension a n g) x = 1 := by
  rw [normalJacobian, graphHeightExtension_normal a hn hg, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphSublevelIndicator (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  {z : Cover | ⟪n,z-a⟫ < graphHeightExtension a n g z}.indicator (fun _ ↦ 1) x

def graphAreaVector (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover :=
  n - normalPlaneEmbedding n (gradient g y)

lemma graphSublevelIndicator_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSublevelIndicator a n g (graphShear a n g x) = halfspaceIndicator n (x-a) := by
  have hheight : ⟪n, graphShear a n g x - a⟫ = ⟪n,x-a⟫ + graphHeightExtension a n g x := by
    simp only [graphShear, normalMove, add_sub_right_comm, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hp : graphHeightExtension a n g (graphShear a n g x) = graphHeightExtension a n g x :=
    congrArg g (graphShear_projection a hn g x)
  simp only [graphSublevelIndicator, Set.indicator, Set.mem_ofPred_eq, hheight, hp,
    add_lt_iff_neg_right, halfspaceIndicator]

lemma normalPullback_graph_compactSupport (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {F : Cover → Cover} (hs : HasCompactSupport F) :
    HasCompactSupport (normalPullback n (graphHeightExtension a n g) F) := by
  have hc := hs.comp_homeomorph (graphShearHomeomorph a hn hg)
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  dsimp only [Function.comp_def, graphShearHomeomorph] at hx
  have hh : F (graphShear a n g x) = 0 := hx
  simp only [Function.mem_support, not_not]
  change normalPullback n (graphHeightExtension a n g) F x = 0
  change F (normalMove n (graphHeightExtension a n g) x) = 0 at hh
  simp only [normalPullback, hh, smul_zero, map_zero, zero_smul, sub_self]

lemma graphAreaVector_pullback (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (F : Cover → Cover) (y : Plane) :
    ⟪n, normalPullback n (graphHeightExtension a n g) F (a+normalPlaneEmbedding n y)⟫ =
      ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hs : graphShear a n g (a+normalPlaneEmbedding n y) = a+normalGraph n g y := by
    simp only [graphShear, normalMove, graphHeightExtension, add_sub_cancel_left,
      normalPlaneCoordinates_embedding, normalGraph]
    abel
  rw [normalPullback, graphShear_jacobian a hn hg, one_smul, ← graphShear, hs,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    add_sub_cancel_left, normalPlaneCoordinates_embedding]
  rw [graphAreaVector, inner_sub_left]
  congr 1
  rw [show normalPlaneEmbedding n (gradient g y) =
    (normalPlaneLinearIsometry n).toContinuousLinearMap (gradient g y) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
  rfl

lemma graphSublevel_flux_integrable (a n : Cover) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    Integrable (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x) := by
  have hm : MeasurableSet {z : Cover | ⟪n,z-a⟫ < graphHeightExtension a n g z} :=
    isOpen_lt (by fun_prop) (hg.comp ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub continuous_const))) |>.measurableSet
  have hc : HasCompactSupport (divergence F) :=
    hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  have hi := (continuous_divergence hF).integrable_of_hasCompactSupport (μ := volume) hc
  apply (hi.indicator hm).congr
  filter_upwards [] with x
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;> simp [graphSublevelIndicator, hx]

theorem integral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hmp : MeasurePreserving (graphShearHomeomorph a hn hg.continuous).toMeasurableEquiv :=
    graphShear_measurePreserving a hn hg.continuous.measurable
  rw [← hmp.integral_comp' (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x)]
  have he (x : Cover) : graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
      divergence F (graphShearHomeomorph a hn hg.continuous x) =
      halfspaceIndicator n (x-a) * divergence (normalPullback n (graphHeightExtension a n g) F) x := by
    change graphSublevelIndicator a n g (graphShear a n g x) * divergence F (graphShear a n g x) = _
    rw [graphSublevelIndicator_shear a hn, normalPullback_divergence n
      (graphHeightExtension_contDiff a n hg) hF,
      graphShear_jacobian a hn (hg.differentiable (by simp)), one_mul]
    rfl
  change (∫ x : Cover, graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
    divergence F (graphShearHomeomorph a hn hg.continuous x)) = _
  simp_rw [he]
  rw [integral_halfspace_divergence a hn
    (normalPullback_contDiff n (graphHeightExtension_contDiff a n hg) hF)
    (normalPullback_graph_compactSupport a hn hg.continuous hs)]
  apply integral_congr_ae
  exact Eventually.of_forall (graphAreaVector_pullback a hn (hg.differentiable (by simp)) F)

end CubicTorus

end
end

end

end OAI
