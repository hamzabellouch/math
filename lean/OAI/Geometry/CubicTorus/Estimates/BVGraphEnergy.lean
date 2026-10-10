import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVTriangleRegion

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_derivative_norm_le_tilt {n m : Cover} (hn : ‖n‖ = 1)
    (L : Plane →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (horth : ∀ v : Plane, ⟪m, normalPlaneEmbedding n v + L v • n⟫ = 0) :
    ‖L‖ ≤ 2 * ‖m - n‖ := by
  by_cases hlarge : 1 / 2 ≤ ‖m - n‖
  · linarith
  have hsmall : ‖m - n‖ < 1 / 2 := lt_of_not_ge hlarge
  have hc := abs_real_inner_le_norm (m - n) n
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hn] at hc
  norm_num at hc
  have hmn : 1 / 2 ≤ ⟪m, n⟫ := by
    have hh := (abs_le.mp hc).1
    linarith
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv := abs_real_inner_le_norm (m - n) (normalPlaneEmbedding n v)
  rw [inner_sub_left, normalPlaneEmbedding_inner hn, sub_zero,
    normalPlaneEmbedding_norm] at hv
  have he : L v * ⟪m, n⟫ = - ⟪m, normalPlaneEmbedding n v⟫ := by
    have hh := horth v
    rw [inner_add_right, inner_smul_right] at hh
    linarith
  have heabs := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ ⟪m, n⟫), abs_neg] at heabs
  rw [Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left hmn (abs_nonneg (L v))
  nlinarith

lemma normalGraph_gradient_bound_ae {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (hK : K ≤ 1)
    {B : Set Torus} {S : Set Plane} {a : Torus} (N : Plane → Cover)
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) (N x)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → ‖fderiv ℝ g x‖ ≤ 2 * ‖N x - n‖ := by
  filter_upwards [normalGraph_tangent_ae hn hg N hS hflat] with x hx hs
  apply graph_derivative_norm_le_tilt hn _ _ (hx hs)
  exact (norm_fderiv_le_of_lipschitz ℝ hg).trans (by exact_mod_cast hK)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_antilipschitz {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) :
    AntilipschitzWith 1 (normalGraph n g) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have he : normalGraph n g x - normalGraph n g y =
      normalPlaneEmbedding n (x - y) + (g x - g y) • n := by
    change normalPlaneLinearIsometry n x + g x • n -
      (normalPlaneLinearIsometry n y + g y • n) = _
    rw [show normalPlaneEmbedding n (x - y) =
      normalPlaneLinearIsometry n x - normalPlaneLinearIsometry n y from
        (normalPlaneLinearIsometry n).map_sub x y, sub_smul]
    abel
  rw [he]
  have horth : ⟪normalPlaneEmbedding n (x - y), (g x - g y) • n⟫ = 0 := by
    rw [inner_smul_right, real_inner_comm, normalPlaneEmbedding_inner hn, mul_zero]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [normalPlaneEmbedding_norm] at hs
  nlinarith [norm_nonneg (x - y), norm_nonneg (normalPlaneEmbedding n (x - y) + (g x - g y) • n),
    sq_nonneg ‖(g x - g y) • n‖]

lemma normalGraph_torus_antilipschitz {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) :
    AntilipschitzWith 1 (fun x : D ↦ a + quotientMap (normalGraph n g x)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_add_left]
  have hs : ‖normalGraph n g x - normalGraph n g y‖ < 1 / 2 :=
    (norm_sub_le _ _).trans_lt (by linarith [hD x x.property, hD y y.property])
  have he : dist (quotientMap (normalGraph n g x)) (quotientMap (normalGraph n g y)) =
      dist (normalGraph n g x) (normalGraph n g y) := by
    rw [dist_eq_norm, ← quotientMap_sub, ← norm_shortestLift, shortestLift_quotientMap hs,
      dist_eq_norm]
  rw [he]
  simpa using (normalGraph_antilipschitz hn g).le_mul_dist x y

instance plane_hausdorff_two_haar : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure 2 : Measure Plane) := by
  simpa only [finrank_euclideanSpace_fin, Nat.cast_ofNat] using
    (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Plane))

lemma normalGraph_preimage_area_null {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    {T : Set Torus} (hT : Measure.hausdorffMeasure 2 T = 0) :
    (volume : Measure Plane) {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} = 0 := by
  let F : D → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hh := (normalGraph_torus_antilipschitz hn g a D hD).hausdorffMeasure_preimage_le
    (by norm_num : (0 : ℝ) ≤ 2) T
  have hnull : Measure.hausdorffMeasure 2 (F ⁻¹' T) = 0 := by
    apply le_zero_iff.mp
    simpa only [hT, mul_zero] using hh
  have himage := (isometry_subtype_coe : Isometry (Subtype.val : D → Plane)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (F ⁻¹' T)
  have hset : Subtype.val '' (F ⁻¹' T) = {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} := by
    ext x
    simp [F, and_comm]
  rw [hset, hnull] at himage
  exact (Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Plane)
    (Measure.hausdorffMeasure 2)) himage

lemma isMinimizerAt_ae_on_normalGraph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (a : Torus) (S : Set Plane)
    (hsmall : ∀ x ∈ S, ‖normalGraph n g x‖ < 1 / 4)
    (hS : ∀ x ∈ S, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E))
    {p : Torus → Prop} (hp : ∀ᵐ b ∂(spatialNormalMeasure μ : Measure Torus), p b) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S → p (a + quotientMap (normalGraph n g x)) := by
  have hnull : (spatialNormalMeasure μ : Measure Torus) {b | ¬ p b} = 0 := ae_iff.mp hp
  have ha := isMinimizerAt_boundary_area_absolutelyContinuous hV hE hmin hμ hnull
  rw [Measure.restrict_apply₀' isClosed_frontier.measurableSet.nullMeasurableSet] at ha
  have hpre := normalGraph_preimage_area_null hn g a S hsmall ha
  rw [ae_iff]
  apply measure_mono_null _ hpre
  intro x hx
  have hh : x ∈ S ∧ ¬ p (a + quotientMap (normalGraph n g x)) := Classical.not_imp.mp hx
  exact ⟨hh.1, hh.2, hS x hh.1⟩

theorem isMinimizerAt_normalGraph_gradient_bound {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hunit : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hK : K ≤ 1) (a : Torus) (S : Set Plane)
    (hsmall : ∀ x ∈ S, ‖normalGraph n g x‖ < 1 / 4)
    (hS : ∀ x ∈ S, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) :
    ∀ᵐ x ∂(volume : Measure Plane), x ∈ S →
      ‖fderiv ℝ g x‖ ≤ 2 * ‖N (a + quotientMap (normalGraph n g x)) - n‖ := by
  let T := {x ∈ S | BoundaryFlatAt (frontier (openRepresentative E))
    (a + quotientMap (normalGraph n g x)) (N (a + quotientMap (normalGraph n g x)))}
  have hflat := isMinimizerAt_ae_on_normalGraph hV hE hmin hμ hn g a S hsmall hS
    (isMinimizerAt_boundary_flat_ae hV hE hmin hμ hN hpolar hunit)
  have hgrad := normalGraph_gradient_bound_ae hn hg hK
    (fun x ↦ N (a + quotientMap (normalGraph n g x)))
    (S := T) (fun x hx ↦ hS x hx.1) (fun _ hx ↦ hx.2)
  filter_upwards [hflat, hgrad] with x hx hgx hs
  exact hgx ⟨hs, hx hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeAreaFactor : ℝ≥0 := Measure.addHaarScalarFactor
  (volume : Measure Plane) (Measure.hausdorffMeasure 2)

lemma normalGraph_preimage_volume_le {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    (a : Torus) (D : Set Plane) (hD : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    (T : Set Torus) :
    (volume : Measure Plane) {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} ≤
      (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 T := by
  let F : D → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hh := (normalGraph_torus_antilipschitz hn g a D hD).hausdorffMeasure_preimage_le
    (by norm_num : (0 : ℝ) ≤ 2) T
  have hh' : Measure.hausdorffMeasure 2 (F ⁻¹' T) ≤ Measure.hausdorffMeasure 2 T := by
    simpa using hh
  have himage := (isometry_subtype_coe : Isometry (Subtype.val : D → Plane)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ) ≤ 2)) (F ⁻¹' T)
  have hset : Subtype.val '' (F ⁻¹' T) = {x ∈ D | a + quotientMap (normalGraph n g x) ∈ T} := by
    ext x
    simp [F, and_comm]
  rw [hset] at himage
  rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure Plane) (Measure.hausdorffMeasure 2),
    Measure.smul_apply]
  change (planeAreaFactor : ℝ≥0∞) * _ ≤ _
  rw [himage]
  exact mul_le_mul_right hh' _

lemma normalGraph_map_volume_le_perimeter
    (σ : FiniteMeasure Torus) (B U : Set Torus) (_hU : MeasurableSet U)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (a : Torus) (D : Set Plane)
    (hsmall : ∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4)
    (hD : ∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ B ∩ U) :
    Measure.map (fun x ↦ a + quotientMap (normalGraph n g x)) ((volume : Measure Plane).restrict D) ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) • (σ : Measure Torus).restrict U := by
  let F : Plane → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hF : Measurable F :=
    (continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hn hg).continuous)).measurable
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.map_apply hF hT, Measure.restrict_apply (hT.preimage hF),
    Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]
  have hset : F ⁻¹' T ∩ D = {x ∈ D | F x ∈ (T ∩ U) ∩ B} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, ⟨hx.1, (hD x hx.2).2⟩, (hD x hx.2).1⟩
    · intro hx
      exact ⟨hx.2.1.1, hx.1⟩
  rw [hset]
  have hh := normalGraph_preimage_volume_le hn g a D hsmall ((T ∩ U) ∩ B)
  have ha := hausdorff_two_le_measure_of_lower_density σ ((T ∩ U) ∩ B) hR hc
    (fun x hx ↦ hl x hx.2)
  calc
    _ ≤ (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 ((T ∩ U) ∩ B) := hh
    _ ≤ (planeAreaFactor : ℝ≥0∞) * (ENNReal.ofReal (64 / c) * (σ : Measure Torus) ((T ∩ U) ∩ B)) :=
      mul_le_mul_right ha _
    _ ≤ ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) * (σ : Measure Torus) (T ∩ U) := by
      rw [mul_assoc]
      exact mul_le_mul_right (mul_le_mul_right (measure_mono inter_subset_left) _) _

theorem isMinimizerAt_normalGraph_good_energy {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
        LipschitzWith K g → K ≤ 1 → ∀ (a : Torus) (D : Set Plane), MeasurableSet D →
        (∀ x ∈ D, ‖normalGraph n g x‖ < 1 / 4) →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ frontier (openRepresentative E)) →
      ∀ U : Set Torus, MeasurableSet U →
        (∀ x ∈ D, a + quotientMap (normalGraph n g x) ∈ U) →
      (∫⁻ x in D, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ∂(volume : Measure Plane)) ≤
        C * ∫⁻ b in U, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂(spatialNormalMeasure μ : Measure Torus) := by
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C : ℝ≥0∞ := 4 * ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c))
  refine ⟨C, by dsimp [C]; finiteness, ?_⟩
  intro μ hμ N hN hp hn n hnorm g K hg hK a D hD hsmall hBD U hU hDU
  let F : Plane → Torus := fun x ↦ a + quotientMap (normalGraph n g x)
  have hF : Measurable F :=
    (continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hnorm hg).continuous)).measurable
  have hgrad := isMinimizerAt_normalGraph_gradient_bound hV hE hmin hμ hN hp hn hnorm hg hK a D hsmall hBD
  have hgrad' : ∀ᵐ x ∂(volume : Measure Plane).restrict D,
      ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) ≤ 4 * ENNReal.ofReal (‖N (F x) - n‖ ^ 2) := by
    rw [ae_restrict_iff' hD]
    filter_upwards [hgrad] with x hx hxd
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hx hxd) 2
    have he : (2 * ‖N (F x) - n‖) ^ 2 = 4 * ‖N (F x) - n‖ ^ 2 := by ring
    rw [he] at hh
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hh
  have hmeasure := normalGraph_map_volume_le_perimeter (spatialNormalMeasure μ)
    (volumeSupport E ∩ volumeSupport Eᶜ) U hU hR hc (hl μ hμ) hnorm hg a D hsmall
    (fun x hx ↦ ⟨by rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]; exact hBD x hx, hDU x hx⟩)
  have hmeas : Measurable (fun b ↦ ENNReal.ofReal (‖N b - n‖ ^ 2)) :=
    ((hN.sub_const n).norm.pow_const 2).ennreal_ofReal
  calc
    _ ≤ ∫⁻ x in D, 4 * ENNReal.ofReal (‖N (F x) - n‖ ^ 2) := lintegral_mono_ae hgrad'
    _ = 4 * ∫⁻ x in D, ENNReal.ofReal (‖N (F x) - n‖ ^ 2) :=
      lintegral_const_mul _ (hmeas.comp hF)
    _ = 4 * ∫⁻ b, ENNReal.ofReal (‖N b - n‖ ^ 2) ∂Measure.map F ((volume : Measure Plane).restrict D) := by
      rw [lintegral_map hmeas hF]
    _ ≤ 4 * ∫⁻ b, ENNReal.ofReal (‖N b - n‖ ^ 2)
        ∂(((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) •
          (spatialNormalMeasure μ : Measure Torus).restrict U) :=
      mul_le_mul_right (lintegral_mono' hmeasure (le_refl _)) _
    _ = _ := by simp only [lintegral_smul_measure, smul_eq_mul, C, mul_assoc]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalPlaneCoordinates (n : Cover) : Cover →L[ℝ] Plane :=
  (normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint

lemma normalPlaneCoordinates_embedding (n : Cover) (y : Plane) :
    normalPlaneCoordinates n (normalPlaneEmbedding n y) = y := by
  apply ext_inner_left ℝ
  intro z
  rw [normalPlaneCoordinates, ContinuousLinearMap.adjoint_inner_right]
  exact (normalPlaneLinearIsometry n).inner_map_map z y

lemma normalPlaneCoordinates_normal {n : Cover} (hn : ‖n‖ = 1) :
    normalPlaneCoordinates n n = 0 := by
  apply ext_inner_left ℝ
  intro z
  rw [normalPlaneCoordinates, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
  exact (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn z)

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitzWith.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

lemma normalPlaneCoordinates_torus_lipschitz (n : Cover) (a : Torus) :
    LipschitzOnWith 1 (fun x ↦ normalPlaneCoordinates n (shortestLift (x - a)))
      (Metric.ball a (1 / 4)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul
    (shortestLift (x - a)) (shortestLift (y - a))
  have hxy : dist x a + dist y a < 1 / 2 := by
    change dist x a < 1 / 4 at hx
    change dist y a < 1 / 4 at hy
    linarith
  simpa only [dist_shortestLift_sub_local hxy] using hh

lemma exists_frontier_on_interval {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : ℝ → X} (hf : Continuous f)
    {s t : ℝ} (hst : s ≤ t) (hs : f s ∈ U) (ht : f t ∉ closure U) :
    ∃ u ∈ Icc s t, f u ∈ frontier U := by
  by_contra! hn
  have hsub : f '' Icc s t ⊆ U ∪ (closure U)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases h : f u ∈ closure U
    · left
      have hh := hn u hu
      rw [frontier, hU.interior_eq, Set.mem_sdiff, not_and] at hh
      exact not_not.mp (hh h)
    · exact Or.inr h
  have hd : Disjoint U (closure U)ᶜ := disjoint_compl_right.mono_left subset_closure
  rcases (isPreconnected_Icc.image f hf.continuousOn).subset_or_subset hU
      isClosed_closure.isOpen_compl hd hsub with h | h
  · exact ht (subset_closure (h ⟨t, ⟨hst, le_rfl⟩, rfl⟩))
  · exact h ⟨s, ⟨le_rfl, hst⟩, rfl⟩ (subset_closure hs)

lemma trapped_boundary_projects_disk {U : Set Torus} (hU : IsOpen U)
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U) :
    Metric.ball (0 : Plane) (r / 4) ⊆
      (fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) ''
        (frontier U ∩ Metric.ball a (r / 2)) := by
  intro y hy
  have hyn : ‖y‖ < r / 4 := by simpa using hy
  let f : ℝ → Torus := fun t ↦ quotientMap (normalPlaneEmbedding n y + t • n) + a
  have hf : Continuous f :=
    (continuous_quotientMap.comp (continuous_const.add (continuous_id.smul continuous_const))).add continuous_const
  have hsize (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ‖normalPlaneEmbedding n y + t • n‖ < r / 2 := by
    have hab : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    linarith
  have hl (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      shortestLift (f t - a) = normalPlaneEmbedding n y + t • n := by
    dsimp [f]
    rw [add_sub_cancel_right]
    apply shortestLift_quotientMap
    exact (hsize t ht).trans (by linarith)
  have hd (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) : dist (f t) a < r / 2 := by
    rw [dist_eq_norm, ← norm_shortestLift, hl t ht]
    exact hsize t ht
  have hm : -r / 4 ∈ Icc (-r / 4) (r / 4) := ⟨le_rfl, by linarith⟩
  have hp : r / 4 ∈ Icc (-r / 4) (r / 4) := ⟨by linarith, le_rfl⟩
  have hinner (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ⟪n, shortestLift (f t - a)⟫ = t := by
    rw [hl t ht, inner_add_right, normalPlaneEmbedding_inner hn,
      inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  have hs : f (-r / 4) ∈ U := by
    apply htrap.2
    exact ⟨(hd _ hm).trans (by linarith), by
      rw [inner_neg_left, hinner _ hm]
      nlinarith [mul_lt_mul_of_pos_right hε hr]⟩
  have ht : f (r / 4) ∉ closure U := by
    apply htrap.1
    exact ⟨(hd _ hp).trans (by linarith), by
      rw [hinner _ hp]
      nlinarith [mul_lt_mul_of_pos_right hε hr]⟩
  obtain ⟨t, hti, htb⟩ := exists_frontier_on_interval hU hf (by linarith : -r / 4 ≤ r / 4) hs ht
  refine ⟨f t, ⟨htb, hd t hti⟩, ?_⟩
  simp [hl t hti, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

lemma plane_projection_volume_le_perimeter (σ : FiniteMeasure Torus)
    (B : Set Torus) {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ B, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    (n : Cover) (a : Torus) (S : Set Torus) (hS : S ⊆ B)
    (hsmall : S ⊆ Metric.ball a (1 / 4)) :
    (volume : Measure Plane)
      ((fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) '' S) ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) * (σ : Measure Torus) S := by
  have hp := ((normalPlaneCoordinates_torus_lipschitz n a).mono hsmall).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 2)
  have hp' : Measure.hausdorffMeasure 2
      ((fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))) '' S) ≤
      Measure.hausdorffMeasure 2 S := by simpa using hp
  have hl' := hausdorff_two_le_measure_of_lower_density σ S hR hc (fun x hx ↦ hl x (hS hx))
  rw [Measure.isAddLeftInvariant_eq_smul (volume : Measure Plane) (Measure.hausdorffMeasure 2),
    Measure.smul_apply]
  change (planeAreaFactor : ℝ≥0∞) * _ ≤ _
  calc
    _ ≤ (planeAreaFactor : ℝ≥0∞) * Measure.hausdorffMeasure 2 S := mul_le_mul_right hp' _
    _ ≤ (planeAreaFactor : ℝ≥0∞) * (ENNReal.ofReal (64 / c) * (σ : Measure Torus) S) :=
      mul_le_mul_right hl' _
    _ = _ := (mul_assoc _ _ _).symm

lemma normalPlaneCoordinates_reconstruct {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v) + ⟪n, v⟫ • n = v := by
  obtain ⟨⟨t, y⟩, rfl⟩ := (normalProductChart n).surjective v
  rw [normalProductChart_inner hn]
  have he : normalProductChart n (t, y) =
      normalPlaneEmbedding n (WithLp.toLp 2 y) + t • n := by
    rw [normalProductChart_decompose hn]
    simp only [normalPlaneEmbedding, add_comm]
  rw [he]
  simp only [map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn, smul_zero, add_zero]

lemma trapped_graph_holes_volume_le
    {U : Set Torus} (hU : IsOpen U) (σ : FiniteMeasure Torus)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hl : ∀ a ∈ frontier U, ∀ r : ℝ, 0 < r → r ≤ R →
      c * r ^ 2 ≤ (σ : Measure Torus).real (Metric.ball a r))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫) :
    (volume : Measure Plane) {y ∈ Metric.ball (0 : Plane) (r / 4) |
      a + quotientMap (normalGraph n g y) ∉ frontier U} ≤
      ((planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
  let Q : Torus → Plane := fun x ↦ normalPlaneCoordinates n (shortestLift (x - a))
  have hcover : {y ∈ Metric.ball (0 : Plane) (r / 4) |
      a + quotientMap (normalGraph n g y) ∉ frontier U} ⊆
      Q '' ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := trapped_boundary_projects_disk hU a hn hr hrsmall hε htrap hy.1
    have hxS : x ∉ S := by
      intro hm
      have hg : normalGraph n g y = shortestLift (x - a) := by
        rw [← hxy, normalGraph, hS x hm]
        exact normalPlaneCoordinates_reconstruct hn _
      apply hy.2
      rw [hg, quotientMap_shortestLift, add_sub_cancel]
      exact hx.1
    exact ⟨x, ⟨hx, hxS⟩, hxy⟩
  apply (measure_mono hcover).trans
  apply plane_projection_volume_le_perimeter σ (frontier U) hR hc hl n a _
    (fun x hx ↦ hx.1.1)
  intro x hx
  exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ 1 / 4)) hx.1.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normalGraph_full_energy {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ g : Plane → ℝ, ∀ K : ℝ≥0,
        LipschitzWith K g → K ≤ 1 → ∀ a : Torus, ∀ r ε : ℝ,
        0 < r → r < 1 / 2 → ε < 1 / 4 →
        (normalCap a n r (ε * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (ε * r) ⊆ openRepresentative E) →
        (∀ y ∈ Metric.ball (0 : Plane) (r / 4), |g y| ≤ r / 4) →
      ∀ S : Set Torus,
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) →
      (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
        ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤
        C * ((∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
          (spatialNormalMeasure μ : Measure Torus)
            ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S)) := by
  obtain ⟨C₀, hC₀, hgood⟩ := isMinimizerAt_normalGraph_good_energy hV hE hmin
  obtain ⟨R, c, hR, hc, hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C₁ : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)
  let C := C₀ + C₁
  refine ⟨C, by dsimp [C, C₁]; finiteness, ?_⟩
  intro μ hμ N hN hp hn n hnorm g K hg hK a r ε hr hrs hε htrap hheight S hS
  let U := openRepresentative E
  let Ω : Set Plane := Metric.ball 0 (r / 4)
  let F : Plane → Torus := fun y ↦ a + quotientMap (normalGraph n g y)
  let D : Set Plane := {y ∈ Ω | F y ∈ frontier U}
  let H : Set Plane := {y ∈ Ω | F y ∉ frontier U}
  have hF : Continuous F :=
    continuous_const.add (continuous_quotientMap.comp (normalGraph_lipschitz hnorm hg).continuous)
  have hD : MeasurableSet D := measurableSet_ball.inter (isClosed_frontier.measurableSet.preimage hF.measurable)
  have hsize (y : Plane) (hy : y ∈ Ω) : ‖normalGraph n g y‖ < r / 2 := by
    have hyn : ‖y‖ < r / 4 := by simpa [Ω] using hy
    have hh := norm_add_le (normalPlaneEmbedding n y) (g y • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hnorm, mul_one, Real.norm_eq_abs] at hh
    change ‖normalPlaneEmbedding n y + g y • n‖ < r / 2
    linarith [hheight y hy]
  have hsmall (y : Plane) (hy : y ∈ D) : ‖normalGraph n g y‖ < 1 / 4 :=
    (hsize y hy.1).trans (by linarith)
  have hDU (y : Plane) (hy : y ∈ D) : F y ∈ Metric.ball a (r / 2) := by
    change dist (a + quotientMap (normalGraph n g y)) a < r / 2
    rw [dist_eq_norm, add_sub_cancel_left, ← norm_shortestLift,
      shortestLift_quotientMap ((hsmall y hy).trans (by norm_num))]
    exact hsize y hy.1
  have hgd := hgood μ hμ N hN hp hn n hnorm g K hg hK a D hD hsmall
    (fun y hy ↦ hy.2) (Metric.ball a (r / 2)) measurableSet_ball hDU
  have hlo : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c * ρ ^ 2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball x ρ) := by
    rw [show frontier U = volumeSupport E ∩ volumeSupport Eᶜ from
      isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact hl μ hμ
  have hmH := trapped_graph_holes_volume_le (isOpen_openRepresentative E)
    (spatialNormalMeasure μ) hR hc hlo a hnorm hr hrs hε htrap S g hS
  have hbound (y : Plane) : ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ≤ 1 := by
    have hb : ‖fderiv ℝ g y‖ ≤ 1 := (norm_fderiv_le_of_lipschitz ℝ hg).trans (by exact_mod_cast hK)
    have hs : ‖fderiv ℝ g y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (fderiv ℝ g y)]
    simpa using ENNReal.ofReal_le_ofReal hs
  have heH : (∫⁻ y in H, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤
      C₁ * (spatialNormalMeasure μ : Measure Torus)
        ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
    apply (lintegral_mono hbound).trans
    simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using hmH
  have hsum : Ω = D ∪ H := by
    ext y
    simp only [D, H, mem_union, Set.mem_ofPred_eq]
    tauto
  change (∫⁻ y in Ω, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) ≤ _
  calc
    _ ≤ (∫⁻ y in D, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane)) +
        ∫⁻ y in H, ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2) ∂(volume : Measure Plane) := by
      rw [hsum]
      exact lintegral_union_le _ _ _
    _ ≤ C₀ * (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
        C₁ * (spatialNormalMeasure μ : Measure Torus)
          ((frontier U ∩ Metric.ball a (r / 2)) \ S) := add_le_add hgd heH
    _ ≤ C * (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
          ∂(spatialNormalMeasure μ : Measure Torus)) +
        C * (spatialNormalMeasure μ : Measure Torus)
          ((frontier U ∩ Metric.ball a (r / 2)) \ S) := by
      gcongr
      · exact le_self_add
      · exact le_add_self
    _ = _ := (mul_add _ _ _).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_lipschitz_approximation_with_cone {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {D δ R A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ D →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2)
    {ρ ε β : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 32) (hρD : 2 * ρ ≤ D) (hρR : 80 * ρ ≤ R)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hβ : 0 < β)
    (hβsmall : (131072 : ℝ) ^ 2 * (4 * A) * β ≤ (δ ^ 2 * (ε / 8) ^ 6) ^ 2)
    (a : Torus) {n : Cover} (hnorm : ‖n‖ = 1) :
    ∃ S : Set Torus, S ⊆ B ∩ Metric.ball a (ρ / 2) ∧
      (spatialNormalMeasure μ : Measure Torus) ((B ∩ Metric.ball a (ρ / 2)) \ S) ≤
        ENNReal.ofReal (25 * A / β) *
          ENNReal.ofReal (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
            ∂(spatialNormalMeasure μ : Measure Torus)) ∧
      (∀ c ∈ S, ∀ y ∈ B, dist y c ≤ ρ →
        |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c) ∧
      ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
        ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫ := by
  let σ := spatialNormalMeasure μ
  let S := {c : Torus | c ∈ B ∩ Metric.ball a (ρ / 2) ∧
    ∀ s : ℝ, 0 < s → s ≤ 16 * ρ → normalExcess σ N c n s < β}
  have hS : S ⊆ B ∩ Metric.ball a (ρ / 2) := fun _ hc ↦ hc.1
  have hgood (c : Torus) (hc : c ∈ S) : ∀ y ∈ B, dist y c ≤ ρ →
      |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c := by
    apply good_scales_boundary_cone hE hμ hN hpolar hn hδ hd hc.1.1 hnorm hρsmall hρD hε (by linarith)
    intro s hs hs16
    have hmass := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : s < 2 * s))).trans
      (hu c (2 * s) (by positivity) (by linarith))
    have hmass' : (σ : Measure Torus).real (Metric.closedBall c s) ≤ (4 * A) * s ^ 2 := by
      change (σ : Measure Torus).real (Metric.closedBall c s) ≤ A * (2 * s) ^ 2 at hmass
      nlinarith
    have ho := normalOscillation_sq_le_excess σ hN hn hnorm c hs hmass'
    have he := hc.2 s hs hs16
    have hh := ho.trans_lt (mul_lt_mul_of_pos_left he (by positivity : 0 < 4 * A))
    have hh' := mul_lt_mul_of_pos_left hh (by norm_num : (0 : ℝ) < 131072 ^ 2)
    have hT : 0 < δ ^ 2 * (ε / 8) ^ 6 := by positivity
    have hnosc := normalOscillation_nonneg σ N c n s
    nlinarith
  have hbad : ∀ c ∈ (B ∩ Metric.ball a (ρ / 2)) \ S, ∃ r : ℝ,
      0 < r ∧ r ≤ 16 * ρ ∧ β ≤ normalExcess σ N c n r := by
    intro c hc
    have hh : ¬ ∀ s : ℝ, 0 < s → s ≤ 16 * ρ → normalExcess σ N c n s < β := by
      intro hh
      exact hc.2 ⟨hc.1, hh⟩
    push Not at hh
    exact hh
  have hbadmass := normalExcess_bad_set_measure hN hn n hA hβ hρ hρR hu a
    ((B ∩ Metric.ball a (ρ / 2)) \ S)
    (fun c hc ↦ (Metric.ball_subset_ball (by linarith : ρ / 2 ≤ ρ)) hc.1.2) hbad
  have hSsmall : S ⊆ Metric.ball a (1 / 4) :=
    hS.trans (inter_subset_right.trans (Metric.ball_subset_ball (by linarith)))
  have hcone : ∀ x ∈ S, ∀ y ∈ S, |⟪n, shortestLift (x - y)⟫| ≤ ε * dist x y := by
    intro x hx y hy
    apply hgood y hy x hx.1.1
    have hxa : dist x a < ρ / 2 := hx.1.2
    have hya : dist y a < ρ / 2 := hy.1.2
    linarith [dist_triangle_right x y a]
  obtain ⟨g, hg, hgeq⟩ := exists_lipschitz_height_of_cone
    ((fun z ↦ shortestLift (z - a)) '' S) hnorm hε.le hεhalf (lifted_cone_of_torus_cone hSsmall hcone)
  exact ⟨S, hS, hbadmass, hgood, g, hg, fun x hx ↦ hgeq _ ⟨x, hx, rfl⟩⟩

theorem isMinimizerAt_lipschitz_approximation_with_cone {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ S : Set Torus, S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2) ∧
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2)) \ S) ≤
          ENNReal.ofReal C * ENNReal.ofReal
            (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
              ∂(spatialNormalMeasure μ : Measure Torus)) ∧
        (∀ c ∈ S, ∀ y ∈ frontier (openRepresentative E), dist y c ≤ ρ →
          |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c) ∧
        ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
          ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
            ⟪n, shortestLift (x - a)⟫ := by
  obtain ⟨D, δ, hD, hδ, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  obtain ⟨R, A, hR, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  let β := (δ ^ 2 * (ε / 8) ^ 6) ^ 2 / ((131072 : ℝ) ^ 2 * (4 * A))
  have hβ : 0 < β := by dsimp [β]; positivity
  let ρ₀ := min (1 / 32 : ℝ) (min (D / 2) (R / 80))
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  refine ⟨ρ₀, 25 * A / β, hρ₀, by positivity, ?_⟩
  intro μ hμ N hN hp hn a n hnorm ρ hρ hρle
  have hd' : ∀ a ∈ frontier (openRepresentative E), ∀ t : ℝ, 0 < t → t ≤ D →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t) := by
    rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact hd
  apply normalMeasure_lipschitz_approximation_with_cone hE hμ hN hp hn hδ hA hd' (hu μ hμ)
    hρ (hρle.trans (min_le_left _ _))
    (by have := hρle.trans ((min_le_right _ _).trans (min_le_left _ _)); linarith)
    (by have := hρle.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith)
    hε hεhalf hβ
  · dsimp [β]
    have hden : (131072 : ℝ) ^ 2 * (4 * A) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hden]
  · exact hnorm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_coordinates {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneEmbedding n (normalPlaneCoordinates n v) = normalPlaneProjection n v := by
  have h := normalPlaneCoordinates_reconstruct hn v
  rw [normalPlaneProjection]
  exact eq_sub_iff_add_eq.mpr h

lemma good_cone_column_unique {B : Set Torus} {a c : Torus} {n : Cover}
    (hn : ‖n‖ = 1) {ρ ε : ℝ} (hρsmall : ρ < 1 / 2) (hε : ε ≤ 1 / 2)
    (hc : c ∈ Metric.ball a (ρ / 2))
    (hcone : ∀ x ∈ B, dist x c ≤ ρ → |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c)
    {x : Torus} (hx : x ∈ B ∩ Metric.ball a (ρ / 2))
    (hproj : normalPlaneCoordinates n (shortestLift (x - a)) =
      normalPlaneCoordinates n (shortestLift (c - a))) : x = c := by
  have hdist : dist x c ≤ ρ := by
    have hh := dist_triangle_right x c a
    change dist c a < ρ / 2 at hc
    have hx' : dist x a < ρ / 2 := hx.2
    linarith
  have hlocal : dist x a + dist c a < 1 / 2 := by
    have hx' : dist x a < ρ / 2 := hx.2
    change dist c a < ρ / 2 at hc
    linarith
  have hproj' : normalPlaneProjection n (shortestLift (x - c)) = 0 := by
    rw [shortestLift_sub_local hlocal, normalPlaneProjection_sub,
      ← normalPlaneEmbedding_coordinates hn, ← normalPlaneEmbedding_coordinates hn, hproj, sub_self]
  have hb := norm_le_two_normalPlaneProjection (v := shortestLift (x - c)) hn hε (by
    simpa only [norm_shortestLift, ← dist_eq_norm] using hcone x hx.1 hdist)
  rw [hproj', norm_zero, mul_zero, norm_shortestLift, ← dist_eq_norm] at hb
  exact dist_eq_zero.mp (le_antisymm hb dist_nonneg)

lemma phases_of_unique_frontier {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {f : ℝ → X} (hf : Continuous f)
    {s t q : ℝ} (hs : f s ∈ U) (ht : f t ∉ closure U)
    (huniq : ∀ u ∈ Icc s t, f u ∈ frontier U → u = q) :
    (∀ u ∈ Icc s t, u < q → f u ∈ U) ∧
      (∀ u ∈ Icc s t, q < u → f u ∉ closure U) := by
  constructor
  · intro u hu huq
    by_contra hnot
    by_cases hcl : f u ∈ closure U
    · have hbd : f u ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hcl, hnot⟩
      exact (ne_of_lt huq) (huniq u hu hbd)
    · obtain ⟨v, hv, hb⟩ := exists_frontier_on_interval hU hf hu.1 hs hcl
      have hveq := huniq v ⟨hv.1, hv.2.trans hu.2⟩ hb
      linarith [hv.2]
  · intro u hu hqu hcl
    by_cases hmem : f u ∈ U
    · obtain ⟨v, hv, hb⟩ := exists_frontier_on_interval hU hf hu.2 hmem ht
      have hveq := huniq v ⟨hu.1.trans hv.1, hv.2⟩ hb
      linarith [hv.1]
    · have hbd : f u ∈ frontier U := by
        rw [frontier, hU.interior_eq]
        exact ⟨hcl, hmem⟩
      exact (ne_of_gt hqu) (huniq u hu hbd)

theorem trapped_good_column_phases {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r ε η : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (hη : η ≤ 1 / 2)
    (htrap : normalCap a n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (ε * r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r / 2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c - a)) ∈ Metric.ball (0 : Plane) (r / 4)) :
    let y := normalPlaneCoordinates n (shortestLift (c - a))
    let q := ⟪n, shortestLift (c - a)⟫
    (∀ t ∈ Icc (-r / 4) (r / 4), t < q →
      a + quotientMap (normalPlaneEmbedding n y + t • n) ∈ U) ∧
    (∀ t ∈ Icc (-r / 4) (r / 4), q < t →
      a + quotientMap (normalPlaneEmbedding n y + t • n) ∉ closure U) := by
  dsimp only
  let y := normalPlaneCoordinates n (shortestLift (c - a))
  let f : ℝ → Torus := fun t ↦ a + quotientMap (normalPlaneEmbedding n y + t • n)
  have hf : Continuous f := continuous_const.add
    (continuous_quotientMap.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hyn : ‖y‖ < r / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hsize (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ‖normalPlaneEmbedding n y + t • n‖ < r / 2 := by
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    have hab : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    linarith
  have hl (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      shortestLift (f t - a) = normalPlaneEmbedding n y + t • n := by
    dsimp [f]
    rw [add_sub_cancel_left]
    exact shortestLift_quotientMap ((hsize t ht).trans (by linarith))
  have hd (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) : dist (f t) a < r / 2 := by
    rw [dist_eq_norm, ← norm_shortestLift, hl t ht]
    exact hsize t ht
  have hh (t : ℝ) (ht : t ∈ Icc (-r / 4) (r / 4)) :
      ⟪n, shortestLift (f t - a)⟫ = t := by
    rw [hl t ht, inner_add_right, normalPlaneEmbedding_inner hn, inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  have hlo : (-r / 4 : ℝ) ∈ Icc (-r / 4) (r / 4) := ⟨le_rfl, by linarith⟩
  have hhi : (r / 4 : ℝ) ∈ Icc (-r / 4) (r / 4) := ⟨by linarith, le_rfl⟩
  have hstart : f (-r / 4) ∈ U := htrap.2 ⟨(hd _ hlo).trans (by linarith), by
    rw [inner_neg_left, hh _ hlo]
    nlinarith⟩
  have hend : f (r / 4) ∉ closure U := htrap.1 ⟨(hd _ hhi).trans (by linarith), by
    rw [hh _ hhi]
    nlinarith⟩
  apply phases_of_unique_frontier hU hf hstart hend
  intro t ht hb
  have heq : f t = c := good_cone_column_unique hn hrsmall hη hc.2 hcone
    ⟨hb, hd t ht⟩ (by
      rw [hl t ht, map_add, map_smul, normalPlaneCoordinates_embedding,
        normalPlaneCoordinates_normal hn, smul_zero, add_zero])
  rw [← heq, hh t ht]

end CubicTorus

end
end

end

end OAI
