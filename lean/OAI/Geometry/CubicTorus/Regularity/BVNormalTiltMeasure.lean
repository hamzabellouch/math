import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVLipschitzGraph

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_sq_cauchy_finite {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : Integrable f ν) (hf2 : Integrable (fun x ↦ f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ν.real univ * ∫ x, f x ^ 2 ∂ν := by
  by_cases hzero : ν univ = 0
  · rw [Measure.measure_univ_eq_zero.mp hzero]
    simp
  have hmass : 0 < ν.real univ := ENNReal.toReal_pos hzero (measure_ne_top _ _)
  let m := (∫ x, f x ∂ν) / ν.real univ
  have hpoly : 0 ≤ (∫ x, f x ^ 2 ∂ν) - (2 * m) * (∫ x, f x ∂ν) + ν.real univ * m ^ 2 := by
    have hh : 0 ≤ ∫ x, (f x - m) ^ 2 ∂ν := integral_nonneg (fun _ ↦ sq_nonneg _)
    have he : (fun x ↦ (f x - m) ^ 2) = (fun x ↦ (f x ^ 2 - (2 * m) * f x) + m ^ 2) := by
      funext x
      ring
    have hip : Integrable (fun x ↦ f x ^ 2 - (2 * m) * f x) ν := hf2.sub (hf.const_mul (2 * m))
    rw [he, integral_add hip (integrable_const (m ^ 2)),
      integral_sub hf2 (hf.const_mul (2 * m)), integral_const_mul, integral_const, smul_eq_mul] at hh
    exact hh
  have he : ν.real univ * ((∫ x, f x ^ 2 ∂ν) - (2 * m) * (∫ x, f x ∂ν) + ν.real univ * m ^ 2) =
      ν.real univ * (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
    dsimp [m]
    field_simp
    ring
  have hh := mul_nonneg hmass.le hpoly
  rw [he] at hh
  linarith

lemma normalOscillation_sq_le_excess (σ : FiniteMeasure Torus) {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) {n : Cover} (hnorm : ‖n‖ = 1)
    (a : Torus) {r A : ℝ} (hr : 0 < r)
    (hmass : (σ : Measure Torus).real (Metric.closedBall a r) ≤ A * r ^ 2) :
    normalOscillation σ N a n r ^ 2 ≤ A * normalExcess σ N a n r := by
  have hi : Integrable (fun x ↦ ‖N x - n‖) (σ : Measure Torus) := by
    apply Integrable.of_bound (hN.sub_const _).norm.aestronglyMeasurable 2
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [hx, hnorm, one_add_one_eq_two] using norm_sub_le (N x) n
  have hi2 : Integrable (fun x ↦ ‖N x - n‖ ^ 2) (σ : Measure Torus) := by
    apply Integrable.of_bound ((hN.sub_const _).norm.pow_const 2).aestronglyMeasurable 4
    filter_upwards [hn] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖N x - n‖ ≤ 2 := by simpa only [hx, hnorm, one_add_one_eq_two] using norm_sub_le (N x) n
    nlinarith [norm_nonneg (N x - n)]
  have hc := integral_sq_cauchy_finite ((σ : Measure Torus).restrict (Metric.closedBall a r))
    hi.integrableOn hi2.integrableOn
  rw [Measure.real_def, Measure.restrict_apply_univ] at hc
  have hh := hc.trans (mul_le_mul_of_nonneg_right hmass (integral_nonneg fun _ ↦ sq_nonneg _))
  rw [normalOscillation, normalExcess]
  apply (mul_le_mul_iff_right₀ (pow_pos hr 4)).mp
  convert hh using 1 <;> field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_sq_norm_sub_normal {σ : FiniteMeasure Torus} {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) :
    Integrable (fun x ↦ ‖N x - n‖ ^ 2) (σ : Measure Torus) := by
  apply Integrable.of_bound ((hN.sub_const n).norm.pow_const 2).aestronglyMeasurable ((1 + ‖n‖) ^ 2)
  filter_upwards [hn] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [hx] using norm_sub_le (N x) n

def normalTiltMeasure (σ : FiniteMeasure Torus) (N : Torus → Cover) (n : Cover) : Measure Torus :=
  (σ : Measure Torus).withDensity (fun x ↦ ENNReal.ofReal (‖N x - n‖ ^ 2))

lemma normalTiltMeasure_apply {σ : FiniteMeasure Torus} {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover) {S : Set Torus} (hS : MeasurableSet S) :
    normalTiltMeasure σ N n S = ENNReal.ofReal (∫ x in S, ‖N x - n‖ ^ 2 ∂(σ : Measure Torus)) := by
  rw [normalTiltMeasure, withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_sq_norm_sub_normal hN hn n).integrableOn
    (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm

lemma normalExcess_bad_set_measure {σ : FiniteMeasure Torus} {N : Torus → Cover} (hN : Measurable N)
    (hn : ∀ᵐ x ∂(σ : Measure Torus), ‖N x‖ = 1) (n : Cover)
    {R A δ ρ : ℝ} (hA : 0 < A) (hδ : 0 < δ) (_hρ : 0 < ρ) (hρR : 80 * ρ ≤ R)
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (σ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2)
    (a : Torus) (B : Set Torus) (hB : B ⊆ Metric.ball a ρ)
    (hbad : ∀ c ∈ B, ∃ r : ℝ, 0 < r ∧ r ≤ 16 * ρ ∧ δ ≤ normalExcess σ N c n r) :
    (σ : Measure Torus) B ≤ ENNReal.ofReal (25 * A / δ) *
      ENNReal.ofReal (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2 ∂(σ : Measure Torus)) := by
  let τ := (normalTiltMeasure σ N n).restrict (Metric.closedBall a (17 * ρ))
  have hbad' : ∀ c ∈ B, ∃ r : ℝ, 0 < r ∧ 5 * r ≤ R ∧
      ENNReal.ofReal (δ * r ^ 2) ≤ τ (Metric.closedBall c r) := by
    intro c hc
    obtain ⟨r, hr, hr16, he⟩ := hbad c hc
    refine ⟨r, hr, by linarith, ?_⟩
    have hsub : Metric.closedBall c r ⊆ Metric.closedBall a (17 * ρ) := by
      intro x hx
      have hca : dist c a < ρ := hB hc
      have hxc : dist x c ≤ r := hx
      exact show dist x a ≤ 17 * ρ from by linarith [dist_triangle x c a]
    have henergy : δ * r ^ 2 ≤ ∫ x in Metric.closedBall c r, ‖N x - n‖ ^ 2 ∂(σ : Measure Torus) :=
      (le_div_iff₀ (sq_pos_of_pos hr)).mp he
    dsimp only [τ]
    rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet, inter_eq_left.mpr hsub,
      normalTiltMeasure_apply hN hn n Metric.isClosed_closedBall.measurableSet]
    exact ENNReal.ofReal_le_ofReal henergy
  have hh := measure_bad_scales_le σ τ B hA hδ hu hbad'
  simpa only [τ, Measure.restrict_apply_univ,
    normalTiltMeasure_apply hN hn n Metric.isClosed_closedBall.measurableSet] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_lipschitz_approximation {E B : Set Torus} (hE : MeasurableSet E)
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
  exact ⟨S, hS, hbadmass, g, hg, fun x hx ↦ hgeq _ ⟨x, hx, rfl⟩⟩

theorem isMinimizerAt_lipschitz_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
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
  apply normalMeasure_lipschitz_approximation hE hμ hN hp hn hδ hA hd' (hu μ hμ)
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

lemma volume_zero_of_nonzero_constant_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    (S : Set X) (L : X → X →L[ℝ] ℝ)
    (hL : ∀ x ∈ S, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) S x)
    (hne : ∀ x ∈ S, L x ≠ 0) : ν S = 0 := by
  classical
  have hex : ∀ x : S, ∃ v : X, L x v = 1 := by
    intro x
    have hh : ∃ w : X, L x w ≠ 0 := by
      by_contra! hh
      apply hne x x.property
      ext w
      exact hh w
    obtain ⟨w, hw⟩ := hh
    exact ⟨(L x w)⁻¹ • w, by simp [hw]⟩
  choose v hv using hex
  let A : X → X →L[ℝ] X := fun x ↦ if hx : x ∈ S then
    ContinuousLinearMap.id ℝ X - (L x).smulRight (v ⟨x, hx⟩) else 0
  have hA : ∀ x ∈ S, HasFDerivWithinAt (fun y : X ↦ y) (A x) S x := by
    intro x hx
    dsimp only [A]
    rw [dite_eq_left hx]
    convert (hasFDerivWithinAt_id x S).sub ((hL x hx).smul_const (v ⟨x, hx⟩)) using 1
    funext y
    simp
  have hdet : ∀ x ∈ S, (A x).det = 0 := by
    intro x hx
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro hker
    have hvne : v ⟨x, hx⟩ ≠ 0 := by
      intro hh
      have hh' := hv ⟨x, hx⟩
      rw [hh, map_zero] at hh'
      norm_num at hh'
    have hmem : v ⟨x, hx⟩ ∈ (A x).toLinearMap.ker := by
      change A x (v ⟨x, hx⟩) = 0
      have hvx := hv ⟨x, hx⟩
      change L x (v ⟨x, hx⟩) = 1 at hvx
      simp [A, hx, hvx]
    rw [hker] at hmem
    exact hvne hmem
  have hh := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero ν hA hdet
  simpa only [image_id'] using hh

lemma ae_constant_derivative_eq_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [Measure.IsAddHaarMeasure ν]
    (S : Set X) (L : X → X →L[ℝ] ℝ)
    (hL : ∀ x ∈ S, HasFDerivWithinAt (fun _ : X ↦ (0 : ℝ)) (L x) S x) :
    ∀ᵐ x ∂ν, x ∈ S → L x = 0 := by
  rw [ae_iff]
  have hh := volume_zero_of_nonzero_constant_derivative ν {x ∈ S | L x ≠ 0} L
    (fun x hx ↦ (hL x hx.1).mono (sep_subset _ _)) (fun _ hx ↦ hx.2)
  simpa only [Classical.not_imp] using hh

def normalPlaneLinearIsometry (n : Cover) : Plane →ₗᵢ[ℝ] Cover where
  toFun := normalPlaneEmbedding n
  map_add' y z := by
    simp only [normalPlaneEmbedding, normalProductChart_apply]
    rw [← map_add]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' t y := by
    simp only [normalPlaneEmbedding, normalProductChart_apply, RingHom.id_apply]
    rw [← map_smul]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  norm_map' := normalPlaneEmbedding_norm n

lemma normalPlaneEmbedding_inner {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    ⟪n, normalPlaneEmbedding n y⟫ = 0 := normalProductChart_inner hn 0 _

def normalGraph (n : Cover) (g : Plane → ℝ) (y : Plane) : Cover :=
  normalPlaneEmbedding n y + g y • n

lemma normalGraph_lipschitz {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) : LipschitzWith (1 + K) (normalGraph n g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : normalGraph n g x - normalGraph n g y =
      normalPlaneEmbedding n (x - y) + (g x - g y) • n := by
    change normalPlaneLinearIsometry n x + g x • n -
      (normalPlaneLinearIsometry n y + g y • n) = _
    rw [show normalPlaneEmbedding n (x - y) =
      normalPlaneLinearIsometry n x - normalPlaneLinearIsometry n y from (normalPlaneLinearIsometry n).map_sub x y, sub_smul]
    abel
  have hh := norm_add_le (normalPlaneEmbedding n (x - y)) ((g x - g y) • n)
  rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one] at hh
  have hb := hg.norm_sub_le x y
  rw [dist_eq_norm, he, dist_eq_norm]
  change ‖normalPlaneEmbedding n (x - y) + (g x - g y) • n‖ ≤ (1 + (K : ℝ)) * ‖x - y‖
  linarith

lemma normalGraph_inner {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪n, normalGraph n g y⟫ = g y := by
  simp [normalGraph, inner_add_right, normalPlaneEmbedding_inner hn,
    inner_smul_right, hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma fderiv_gradient_inner {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : Cover) :
    ⟪fderiv ℝ (gradient f) x u, v⟫ = fderiv ℝ (fderiv ℝ f) x u v := by
  have hd := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hh := ((InnerProductSpace.toDual ℝ Cover).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
    x (hd x).hasFDerivAt).fderiv
  change fderiv ℝ (gradient f) x = _ at hh
  rw [hh]
  change ⟪(InnerProductSpace.toDual ℝ Cover).symm (fderiv ℝ (fderiv ℝ f) x u), v⟫ = _
  exact InnerProductSpace.toDual_symm_apply

lemma divergence_gradient_eq_laplacian {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Cover) :
    divergence (gradient f) x = Δ f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.inner_single_right,
    RCLike.conj_to_real, mul_one, one_mul] using
    fderiv_gradient_inner hf x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma laplacian_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ (f ∘ L) x = Δ f (L x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ L)
    (stdOrthonormalBasis ℝ X),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((stdOrthonormalBasis ℝ X).map L)]
  apply Finset.sum_congr rfl
  intro i _
  have hh := L.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hh' := congrArg (fun A ↦ A ![(stdOrthonormalBasis ℝ X) i,
    (stdOrthonormalBasis ℝ X) i]) hh
  have hv : (fun j : Fin 2 ↦ L (![ (stdOrthonormalBasis ℝ X) i,
      (stdOrthonormalBasis ℝ X) i] j)) =
      ![L ((stdOrthonormalBasis ℝ X) i), L ((stdOrthonormalBasis ℝ X) i)] := by
    funext j
    fin_cases j <;> rfl
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def, hv] using hh'

lemma iteratedFDeriv_two_line {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u : X) :
    iteratedFDeriv ℝ 2 f x ![u, u] =
      iteratedDeriv 2 (fun t : ℝ ↦ f (x + t • u)) 0 := by
  let L : ℝ →L[ℝ] X := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f (x + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hh := L.iteratedFDeriv_comp_right ht 0
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hh' := congrArg (fun A ↦ A (fun _ : Fin 2 ↦ (1 : ℝ))) hh
  have hv : (fun _ : Fin 2 ↦ u) = ![u, u] := by
    funext j
    fin_cases j <;> rfl
  simpa [iteratedDeriv, L, Function.comp_def, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hv] using hh'.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_eq_sum_directional {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y ((stdOrthonormalBasis ℝ X) i)) x
      ((stdOrthonormalBasis ℝ X) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply hf]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma compact_laplacian_continuous {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (Δ f) := by
  have he : Δ f = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y
      ((stdOrthonormalBasis ℝ X) i)) x ((stdOrthonormalBasis ℝ X) i) :=
    funext (laplacian_eq_sum_directional hf)
  rw [he]
  apply continuous_finsetSum
  intro i _
  have ht := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply (contDiff_const
    (c := (stdOrthonormalBasis ℝ X) i))
  exact (ht.continuous_fderiv (by simp)).clm_apply continuous_const

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_tsupport_subset {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (Δ f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  apply hx
  rw [laplacian_eq_sum_directional hf]
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hn ((tsupport_fderiv_apply_subset ℝ _ ) hh))]
  rfl

lemma integral_compact_laplacian_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    (∫ x, Δ f x ∂μ) = 0 := by
  have hd (i : Fin (Module.finrank ℝ X)) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ fderiv ℝ f x ((stdOrthonormalBasis ℝ X) i)) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  simp_rw [laplacian_eq_sum_directional hf]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_compact_fderiv_zero (hd i) (hs.fderiv_apply ℝ _) _
  · intro i _
    exact (((hd i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma fderiv_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x v : X) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v)) x := by
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hs.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v

theorem laplacian_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x : X) :
    Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] Δ k) x := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  rw [laplacian_eq_sum_directional hc, convolution_mul]
  simp_rw [laplacian_eq_sum_directional hk, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    let v := (stdOrthonormalBasis ℝ X) i
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y v) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    have he : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v) :=
      funext (fun y ↦ fderiv_compact_convolution hf hk hs y v)
    change fderiv ℝ (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) x v = _
    rw [he, fderiv_compact_convolution hf hd (hs.fderiv_apply ℝ v)]
    rfl
  · intro i _
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y ((stdOrthonormalBasis ℝ X) i)) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hf
      ((hd.continuous_fderiv (by simp)).clm_apply continuous_const) x

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_translate {k : X → ℝ} (a x : X) :
    Δ (fun y ↦ k (a + y)) x = Δ k (a + x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_reflect_translate {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (a x : X) :
    Δ (fun y ↦ k (a - y)) x = Δ k (a - x) := by
  let L : X ≃ₗᵢ[ℝ] X := LinearIsometryEquiv.neg ℝ
  have hh := laplacian_comp_isometry L (hk.comp ((contDiff_const (c := a)).add contDiff_id)) x
  change Δ (fun y ↦ k (a + -y)) x = Δ (fun y ↦ k (a + y)) (-x) at hh
  rw [laplacian_translate] at hh
  simpa only [sub_eq_add_neg] using hh

theorem weak_harmonic_convolution {f k : X → ℝ} {Ω W : Set X}
    (hf : LocallyIntegrable f μ)
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y ∂μ) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    (hW : IsOpen W)
    (hkernel : ∀ x ∈ W, tsupport (fun y ↦ k (x - y)) ⊆ Ω) :
    InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) W := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  have hz (x : X) (hx : x ∈ W) : Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x = 0 := by
    rw [laplacian_compact_convolution hf hk hs, convolution_mul]
    have hp : HasCompactSupport (fun y ↦ k (x - y)) := by
      exact hs.comp_homeomorph (Homeomorph.subLeft x)
    have hh := hweak (fun y ↦ k (x - y)) (hk.comp (contDiff_const.sub contDiff_id)) hp
      (hkernel x hx)
    simpa only [laplacian_reflect_translate hk] using hh
  intro x hx
  refine ⟨(hc.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by norm_cast)).contDiffAt, ?_⟩
  filter_upwards [hW.mem_nhds hx] with y hy
  exact hz y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma harmonic_angular_integral {h : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c |r|)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) = 2 * Real.pi * h c := by
  have hm := hh.circleAverage_eq
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ ↦ h (circleMap c r θ))] at hm
  norm_num only [zero_add] at hm
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hm
  simp only [smul_eq_mul] at hm
  have hp : 2 * Real.pi ≠ 0 := by positivity
  calc
    _ = (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
        ∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) := by field_simp
    _ = _ := by rw [hm]

lemma add_polarCoord_eq_circleMap (c : ℂ) (r θ : ℝ) :
    c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, mul_add]

theorem harmonic_radial_mean {h : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (∫ z : ℂ, κ ‖z‖ * h (c + z)) = h c * ∫ z : ℂ, κ ‖z‖ := by
  let S : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  have hST : S ⊆ T := by intro p hp; exact ⟨hp.1.1, hp.2⟩
  have hTm : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hpcont : Continuous (Complex.polarCoord.symm) := by
    change Continuous (fun p : ℝ × ℝ ↦ _)
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hF : Continuous (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) :=
    continuous_fst.mul ((hk.comp continuous_fst.abs).mul
      (hh.comp (continuous_const.add hpcont)))
  have hG : Continuous (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) :=
    continuous_fst.mul (hk.comp continuous_fst.abs)
  have hSS : S ⊆ Icc (0, -Real.pi) (R, Real.pi) := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2, hp.2.2.le⟩⟩
  have hFi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) S :=
    hF.integrableOn_Icc.mono_set hSS
  have hGi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) S :=
    hG.integrableOn_Icc.mono_set hSS
  have hangle (r : ℝ) (hr : r ∈ Ioc 0 R) :
      (∫ θ in Ioo (-Real.pi) Real.pi, h (c + Complex.polarCoord.symm (r, θ))) =
        2 * Real.pi * h c := by
    simp_rw [add_polarCoord_eq_circleMap]
    apply harmonic_angular_integral
    apply harm.mono
    exact Metric.closedBall_subset_closedBall (by simpa only [abs_of_pos hr.1] using hr.2)
  rw [← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖ * h (c + z)),
    ← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖)]
  simp only [Complex.norm_polarCoord_symm, smul_eq_mul]
  change (∫ p in T, p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) =
    h c * ∫ p in T, p.1 * κ |p.1|
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_)]
  · simp only [Measure.volume_eq_prod] at hFi hGi ⊢
    dsimp only [S] at hFi hGi ⊢
    rw [setIntegral_prod _ hFi, setIntegral_prod _ hGi, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp_rw [← mul_assoc, integral_const_mul, hangle r hr]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi),
      smul_eq_mul]
    ring
  all_goals
    have hr : R < p.1 := by
      by_contra hn
      exact hp.2 ⟨⟨hp.1.1, le_of_not_gt hn⟩, hp.1.2⟩
    simp only [abs_of_pos (show 0 < p.1 from hp.1.1), hs p.1 hr, zero_mul, mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem exists_radial_smoothing_kernel {R : ℝ} (hR : 0 < R) :
    ∃ (k : ℂ → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) k ∧ HasCompactSupport k ∧
      (∀ z, k z = κ ‖z‖) ∧ Continuous κ ∧ (∀ r, R < r → κ r = 0) ∧
      tsupport k ⊆ Metric.closedBall 0 R ∧ (∫ z, k z) = 1 := by
  let b : ℂ → ℝ := fun z ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((2 / R) • z)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ ↦ ((2 : ℝ), (2 / R) • z)) :=
      contDiff_const.prodMk ((contDiff_const (c := (2 / R : ℝ))).smul contDiff_id)
    have ht : ∀ z : ℂ, ((2 : ℝ), (2 / R) • z) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set ℂ) :=
      fun _ ↦ ⟨by norm_num, mem_univ _⟩
    exact (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hg ht
  have hbformula (z : ℂ) : b z = Real.smoothTransition (2 - (2 / R) * ‖z‖) := by
    simp [b, ContDiffBumpBase.ofInnerProductSpace, Real.norm_eq_abs, abs_of_pos hR, show (2 : ℝ) - 1 = 1 from by norm_num]
  have hzero (r : ℝ) (hr : R < r) : Real.smoothTransition (2 - (2 / R) * r) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have hh : 2 < (2 / R) * r := by
      have := (mul_lt_mul_of_pos_left hr (by positivity : 0 < 2 / R))
      field_simp at this ⊢
      nlinarith
    linarith
  have hbs : tsupport b ⊆ Metric.closedBall 0 R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    by_contra hn
    have hr : R < ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
    exact hz (by rw [hbformula, hzero _ hr])
  have hbc : HasCompactSupport b := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hbs
  have hbpos : 0 < ∫ z, b z := by
    apply hb.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc
      (fun _ ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _ |>.1)
    rw [hbformula 0]
    norm_num [Real.smoothTransition.one_of_one_le]
  let k : ℂ → ℝ := fun z ↦ b z / ∫ y, b y
  let κ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 - (2 / R) * r) / ∫ y, b y
  have hks : tsupport k ⊆ Metric.closedBall 0 R := by
    change tsupport (fun z ↦ b z * (∫ y, b y)⁻¹) ⊆ _
    exact tsupport_mul_subset_left.trans hbs
  have hkc : HasCompactSupport k := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hks
  refine ⟨k, κ, hb.div_const _, hkc, ?_, ?_, ?_, hks, ?_⟩
  · intro z
    exact congrArg (fun t : ℝ ↦ t / ∫ y, b y) (hbformula z)
  · exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub (continuous_const.mul continuous_id))).div_const _
  · intro r hr
    simp only [κ, hzero r hr, zero_div]
  · dsimp only [k]
    rw [integral_div, div_self hbpos.ne']

lemma harmonic_radial_convolution {h k : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (h ⋆[ContinuousLinearMap.mul ℝ ℝ] k) c = h c := by
  rw [convolution_eq_swap, ← integral_neg_eq_self]
  simp only [ContinuousLinearMap.mul_apply']
  simp only [hk, norm_neg, sub_neg_eq_add, mul_comm (h _)]
  rw [harmonic_radial_mean hh hc hs harm]
  have hi' : (∫ z : ℂ, κ ‖z‖) = 1 := by simpa only [hk] using hi
  rw [hi', mul_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma real_convolution_comm (f g : X → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] f := by
  ext x
  rw [convolution_mul_swap, convolution_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ mul_comm _ _)

lemma compact_convolution_assoc {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k)) x := by
  apply convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c) hf.aestronglyMeasurable
    hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hgs.convolutionExists_right _ hf hg)
  · exact Eventually.of_forall (hks.norm.convolutionExists_right _ hg.norm.locallyIntegrable hk.norm)
  · exact (hgs.norm.convolution (ContinuousLinearMap.mul ℝ ℝ) hks.norm).convolutionExists_right _
      (fun x ↦ (hf x).norm) (hks.norm.continuous_convolution_right _ hg.norm.locallyIntegrable hk.norm) x

lemma compact_convolutions_commute {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) x := by
  rw [compact_convolution_assoc hf hg hgs hk hks,
    compact_convolution_assoc hf hk hks hg hgs, real_convolution_comm g k]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in

lemma reflected_tsupport_subset_ball {k : X → ℝ} {c x : X} {r R : ℝ}
    (hk : tsupport k ⊆ Metric.closedBall 0 r) (hx : dist x c + r < R) :
    tsupport (fun y ↦ k (x - y)) ⊆ Metric.ball c R := by
  have hs : tsupport (fun y ↦ k (x - y)) ⊆
      (fun y ↦ x - y) ⁻¹' tsupport k := tsupport_comp_subset_preimage k (by fun_prop)
  intro y hy
  have ht := hk (hs hy)
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at ht
  rw [Metric.mem_ball]
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ = dist x y + dist x c := by rw [dist_comm y x]
    _ ≤ r + dist x c := by linarith
    _ < R := by linarith

end CubicTorus

end
end

end

end OAI
