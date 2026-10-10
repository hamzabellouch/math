import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVAnnulusSelection

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem weakCMC_column_height_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {w : NormalBundle → ℝ} (hw : Integrable w (μ : Measure NormalBundle))
    (hb : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1‖ *
        ‖(z.2 : Cover) - n‖ ^ 2 ≤ w z) :
    |(∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
      H * (∫ z, normalScalarTest a n (normalColumnCutoff r hr) φ z.1 *
        ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle))| ≤
      (1 / 2 : ℝ) * ∫ z, w z ∂(μ : Measure NormalBundle) := by
  rw [weakCMC_column_height_identity hU hμ hH hn hr hrsmall hε htrap hφ hs hcell,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hw
  filter_upwards [hb] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hd : |fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1
      (z.2 : Cover)| ≤ ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1‖ := by
    simpa only [Real.norm_eq_abs, z.2.property, mul_one] using
      (fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1).le_opNorm (z.2 : Cover)
  exact (mul_le_mul_of_nonneg_left hd (sq_nonneg _)).trans (by simpa only [mul_comm] using hz)

lemma integral_pairing_perturbation {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f g q e : X → ℝ} {A R C : ℝ}
    (hf : Integrable (fun x ↦ f x * q x) ν)
    (hg : Integrable (fun x ↦ g x * q x) ν)
    (he : Integrable e ν)
    (hb : ∀ᵐ x ∂ν, |(g x - f x) * q x| ≤ e x)
    (hr : |(∫ x, f x * q x ∂ν) + A| ≤ R)
    (hA : |A| ≤ C) :
    |∫ x, g x * q x ∂ν| ≤ R + C + ∫ x, e x ∂ν := by
  have hd : |(∫ x, g x * q x ∂ν) - ∫ x, f x * q x ∂ν| ≤ ∫ x, e x ∂ν := by
    rw [← integral_sub hg hf, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le he
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, sub_mul] using hx
  have h₁ := abs_add_le ((∫ x, f x * q x ∂ν) + A) (-A)
  have h₂ := abs_add_le ((∫ x, g x * q x ∂ν) - ∫ x, f x * q x ∂ν)
    (∫ x, f x * q x ∂ν)
  simp only [add_neg_cancel_right, abs_neg, sub_add_cancel] at h₁ h₂
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma norm_normalPlaneCoordinates_le (n : Cover) : ‖normalPlaneCoordinates n‖ ≤ 1 := by
  simp [normalPlaneCoordinates]

lemma normalColumnTest_fderiv_le {r : ℝ} (hr : 0 < r) (a n x : Cover)
    {φ : Plane → ℝ} (hφ : Differentiable ℝ φ) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ φ y‖ ≤ D) (hx : |⟪n, x - a⟫| ≤ r / 4) :
    ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) x‖ ≤ D := by
  have ht : ContinuousAt (fun y : Cover ↦ ⟪n, y - a⟫) x :=
    (continuous_const.inner (continuous_id.sub continuous_const)).continuousAt
  have he := (normalColumnCutoff_eventually_one hr hx).comp_tendsto ht
  have heq : normalScalarTest a n (normalColumnCutoff r hr) φ =ᶠ[𝓝 x]
      (fun y ↦ φ (normalPlaneCoordinates n (y - a))) := by
    filter_upwards [he] with y hy
    simp only [Function.comp_def] at hy
    simp only [normalScalarTest, hy, one_mul]
  rw [heq.fderiv_eq]
  have hd := (hφ (normalPlaneCoordinates n (x - a))).hasFDerivAt.comp x
    ((normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))
  simp only [Function.comp_def, id_eq] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_id]
  exact ((fderiv ℝ φ (normalPlaneCoordinates n (x - a))).opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (norm_normalPlaneCoordinates_le n)).trans (hD _))

theorem weakCMC_column_residual_bound {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {B D : ℝ} (_hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D) :
    |∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y| ≤
      (D / 2) * (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) +
      |H| * B * (μ : Measure NormalBundle).real
        {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} := by
  let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball a r}
  let ψ := normalScalarTest a n (normalColumnCutoff r hr) φ
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hν : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
    continuous_subtype_val.comp continuous_snd
  have hS : MeasurableSet S := measurableSet_ball.preimage hx.measurable
  have htest : tsupport ψ ⊆ Metric.ball a r := normalColumnTest_tsupport_ball a hn hr hs
  have htilt : Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover) - n‖ ^ 2)
      (μ : Measure NormalBundle) :=
    ((hν.sub continuous_const).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (S.indicator (fun z : NormalBundle ↦ D * ‖(z.2 : Cover) - n‖ ^ 2))
      (μ : Measure NormalBundle) := (htilt.const_mul D).indicator hS
  have hbound : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖fderiv ℝ ψ z.1‖ * ‖(z.2 : Cover) - n‖ ^ 2 ≤
        S.indicator (fun z : NormalBundle ↦ D * ‖(z.2 : Cover) - n‖ ^ 2) z := by
    filter_upwards [normalMeasure_frontier_ae hU.measurableSet hμ] with z hz
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS]
      have hh := trapped_frontier_height hU hrsmall htrap hzS hz
      have hh' : |⟪n, (z.1 : Cover) - a⟫| ≤ r / 4 := hh.trans (by nlinarith)
      exact mul_le_mul_of_nonneg_right
        (normalColumnTest_fderiv_le hr a n z.1 (hφ.differentiable (by simp)) hd hh')
        (sq_nonneg _)
    · rw [indicator_of_notMem hzS, fderiv_of_notMem_tsupport ℝ
        (show (z.1 : Cover) ∉ tsupport ψ from fun hz ↦ hzS (htest hz))]
      simp
  have hres := weakCMC_column_height_residual hU hμ hH hn hr hrsmall hε htrap
    hφ hs hcell hw hbound
  rw [integral_indicator hS, integral_const_mul] at hres
  have hval : ∀ z : NormalBundle, |ψ z.1 * ⟪(z.2 : Cover), n⟫| ≤ S.indicator (fun _ ↦ B) z := by
    intro z
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS, abs_mul]
      have hh : |⟪(z.2 : Cover), n⟫| ≤ 1 := by
        simpa only [z.2.property, hn, one_mul] using abs_real_inner_le_norm (z.2 : Cover) n
      have hp : |ψ z.1| ≤ B := by
        dsimp [ψ, normalScalarTest]
        rw [abs_mul, abs_of_nonneg ((normalColumnCutoff r hr).nonneg)]
        exact (mul_le_of_le_one_left (abs_nonneg _)
          ((normalColumnCutoff r hr).le_one)).trans (hb _)
      exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans (by simpa only [mul_one] using hp)
    · rw [indicator_of_notMem hzS]
      have hp : ψ z.1 = 0 := image_eq_zero_of_notMem_tsupport
        (show (z.1 : Cover) ∉ tsupport ψ from fun hz ↦ hzS (htest hz))
      simp [hp]
  have hi : |∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)| ≤
      B * (μ : Measure NormalBundle).real S := by
    rw [← Real.norm_eq_abs]
    have hh : ‖∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)‖ ≤
        ∫ z : NormalBundle, S.indicator (fun _ ↦ B) z ∂(μ : Measure NormalBundle) :=
      norm_integral_le_of_norm_le ((integrable_const B).indicator hS)
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using hval z)
    simpa only [integral_indicator hS, integral_const, smul_eq_mul, mul_comm, measureReal_def, Measure.restrict_apply_univ] using hh
  have ht := abs_add_le ((∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
    H * (∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)))
    (-(H * (∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle))))
  simp only [add_neg_cancel_right, abs_neg, abs_mul] at ht
  have hi' := mul_le_mul_of_nonneg_left hi (abs_nonneg H)
  dsimp only [ψ] at hi' ht
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma integral_pairing_local_error {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f g q : X → ℝ} {S : Set X} (hS : MeasurableSet S)
    (hf : Integrable (fun x ↦ f x * q x) ν)
    (hg : Integrable (fun x ↦ g x * q x) ν)
    (he : IntegrableOn (fun x ↦ g x - f x) S ν)
    (hqzero : ∀ x ∉ S, q x = 0) {Q : ℝ}
    (hq : ∀ x, |q x| ≤ Q) :
    |(∫ x, g x * q x ∂ν) - ∫ x, f x * q x ∂ν| ≤
      Q * ∫ x in S, |g x - f x| ∂ν := by
  rw [← integral_sub hg hf, ← Real.norm_eq_abs]
  have he' : Integrable (S.indicator (fun x ↦ Q * |g x - f x|)) ν :=
    IntegrableOn.integrable_indicator (he.abs.const_mul Q) hS
  have hb : ∀ x, ‖g x * q x - f x * q x‖ ≤ S.indicator (fun x ↦ Q * |g x - f x|) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← sub_mul, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hq x) (abs_nonneg _)).trans_eq (mul_comm _ _)
    · rw [indicator_of_notMem hx, hqzero x hx]
      simp
  have hh := norm_integral_le_of_norm_le he' (Eventually.of_forall hb)
  simpa only [integral_indicator hS, integral_const_mul] using hh

theorem weakCMC_graph_residual_bound {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (r / 4))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) {g : Plane → ℝ} (hg : Continuous g) :
    |∫ y : Plane, g y * Δ φ y| ≤
      (D / 2) * (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) +
      |H| * B * (μ : Measure NormalBundle).real
        {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} +
      Q * (∫ y in Metric.ball (0 : Plane) (r / 4),
        |g y - normalColumnHeight U (quotientMap a) n r y|) := by
  let f := normalColumnHeight U (quotientMap a) n r
  have hs' : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3) :=
    hs.trans (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))
  have hres := weakCMC_column_residual_bound hU hμ hH hn hr hrsmall hε htrap
    hφ hs' hcell hB hD hb hd
  have hc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (r / 3)).of_isClosed_subset
    isClosed_closure hs'
  have hcs : HasCompactSupport (Δ φ) := hc.of_isClosed_subset isClosed_closure
    (laplacian_tsupport_subset hφ)
  have hdφ := compact_laplacian_continuous hφ
  have hφi : Integrable (Δ φ) := hdφ.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y ↦ f y * Δ φ y) :=
    hφi.bdd_mul (c := r / 4) (measurable_normalColumnHeight hU.measurableSet _ _ _).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [f, Real.norm_eq_abs] using
        normalColumnHeight_bound hU.measurableSet (quotientMap a) n hr.le y)
  have hgi : Integrable (fun y ↦ g y * Δ φ y) :=
    (hg.mul hdφ).integrable_of_hasCompactSupport hcs.mul_left
  have hfi : IntegrableOn f (Metric.ball (0 : Plane) (r / 4)) :=
    (integrableOn_const (C := r / 4) measure_ball_lt_top.ne).mono'
      (measurable_normalColumnHeight hU.measurableSet _ _ _).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [f, Real.norm_eq_abs] using
        normalColumnHeight_bound hU.measurableSet (quotientMap a) n hr.le y)
  have hgon : IntegrableOn g (Metric.ball (0 : Plane) (r / 4)) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) (r / 4))).mono_set
      Metric.ball_subset_closedBall
  have he := integral_pairing_local_error measurableSet_ball hf hgi (hgon.sub hfi)
    (fun y hy ↦ image_eq_zero_of_notMem_tsupport
      (fun hh ↦ hy (hs (laplacian_tsupport_subset hφ hh)))) hq
  have ht := abs_add_le ((∫ y : Plane, g y * Δ φ y) - ∫ y, f y * Δ φ y)
    (∫ y : Plane, f y * Δ φ y)
  simp only [sub_add_cancel] at ht
  dsimp only [f] at he ht
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma laplacian_comp_smul {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) (x : X) :
    Δ (fun y ↦ f (r • y)) x = r ^ 2 * Δ f (r • x) := by
  let L : X →L[ℝ] X := r • ContinuousLinearMap.id ℝ X
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh := L.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := congrArg (fun A ↦ A ![(stdOrthonormalBasis ℝ X) i,
    (stdOrthonormalBasis ℝ X) i]) hh
  have hm := (iteratedFDeriv ℝ 2 f (r • x)).map_smul_univ (fun _ ↦ r)
    (![(stdOrthonormalBasis ℝ X) i, (stdOrthonormalBasis ℝ X) i])
  simp only [Fin.prod_univ_two, smul_eq_mul] at hm
  simpa only [L, Function.comp_def, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ← sq] using he.trans hm

lemma planar_scaled_laplacian_pairing {f φ : Plane → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {r : ℝ} (hr : 0 < r) :
    (∫ y : Plane, f (r • y) * Δ φ y) =
      ∫ y : Plane, f y * Δ (fun z ↦ φ (r⁻¹ • z)) y := by
  have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
    (fun y ↦ f y * Δ (fun z ↦ φ (r⁻¹ • z)) y) r (hR := hr.le)
  have hd : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  simp only [laplacian_comp_smul hφ, inv_smul_smul₀ hr.ne', hd, smul_eq_mul,
    inv_pow] at hh
  have hfun : (fun y : Plane ↦ f (r • y) * ((r ^ 2)⁻¹ * Δ φ y)) =
      (fun y : Plane ↦ (r ^ 2)⁻¹ * (f (r • y) * Δ φ y)) := by
    funext y
    ring
  rw [hfun, integral_const_mul] at hh
  simp_rw [laplacian_comp_smul hφ, inv_pow]
  exact (mul_left_cancel₀ (by positivity : (r ^ 2)⁻¹ ≠ 0) hh)

lemma fderiv_comp_smul_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} {r : ℝ} (hf : DifferentiableAt ℝ f (r • x)) :
    fderiv ℝ (fun y ↦ f (r • y)) x = r • fderiv ℝ f (r • x) := by
  have hh := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  have he : (fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ X) =
      r • fderiv ℝ f (r • x) := by ext y; simp
  simpa only [Function.comp_def, id_eq, he] using hh.fderiv

lemma scaled_test_support {φ : Plane → ℝ} {r R : ℝ} (hr : 0 < r)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) R) :
    tsupport (fun y ↦ φ (r⁻¹ • y)) ⊆ Metric.ball 0 (r * R) := by
  have hh : tsupport (fun y ↦ φ (r⁻¹ • y)) ⊆ (fun y : Plane ↦ r⁻¹ • y) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ (by fun_prop)
  intro y hy
  have hn : ‖r⁻¹ • y‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hs (hh hy)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hn
  change dist y 0 < r * R
  rw [dist_zero_right]
  have hm := mul_lt_mul_of_pos_left hn hr
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphRescale (r e m : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  r * (m + e * f (r⁻¹ • y))

lemma graphRescale_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (r e m : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (graphRescale r e m f) := by
  exact contDiff_const.mul (contDiff_const.add (contDiff_const.mul (hf.comp (by fun_prop))))

lemma graphRescale_fderiv {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : r ≠ 0) (e m : ℝ) (y : Plane) :
    fderiv ℝ (graphRescale r e m f) y = e • fderiv ℝ f (r⁻¹ • y) := by
  have hd : DifferentiableAt ℝ (fun y : Plane ↦ f (r⁻¹ • y)) y :=
    (hf.comp (by fun_prop)).differentiable (by simp) |>.differentiableAt
  unfold graphRescale
  rw [fderiv_const_mul ((hd.const_mul e).const_add m),
    fderiv_const_add m, fderiv_const_mul hd,
    fderiv_comp_smul_eq ((hf.differentiable (by simp)) _), smul_smul,smul_smul]
  congr 1
  field_simp

lemma plane_integral_rescale_ball (f : Plane → ℝ) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), f (r⁻¹ • y)) =
      r^2 * ∫ y in Metric.ball (0 : Plane) b, f y := by
  have he (y : Plane) : r⁻¹ • y ∈ Metric.ball (0 : Plane) b ↔
      y ∈ Metric.ball (0 : Plane) (r*b) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
    rw [← div_eq_inv_mul,div_lt_iff₀ hr]
    rw [mul_comm b r]
  have hh := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure Plane)
    ((Metric.ball (0 : Plane) b).indicator f) hr.le
  have hh' : (fun y : Plane ↦ (Metric.ball (0 : Plane) b).indicator f (r⁻¹ • y)) =
      (Metric.ball (0 : Plane) (r*b)).indicator (fun y ↦ f (r⁻¹ • y)) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Plane) (r*b)
    · rw [indicator_of_mem hy,indicator_of_mem ((he y).mpr hy)]
    · rw [indicator_of_notMem hy,indicator_of_notMem (fun h ↦ hy ((he y).mp h))]
  rw [hh',integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at hh
  simpa only [show Module.finrank ℝ Plane = 2 from finrank_euclideanSpace_fin,smul_eq_mul] using hh

lemma graphRescale_relative_energy {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {r : ℝ} (hr : 0 < r) (e m b : ℝ) (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) (r*b), ‖fderiv ℝ (graphRescale r e m f) y-e • p‖^2) =
      r^2*e^2*(∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ f y-p‖^2) := by
  simp_rw [graphRescale_fderiv hf hr.ne',← smul_sub,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs]
  rw [integral_const_mul,plane_integral_rescale_ball (fun y ↦ ‖fderiv ℝ f y-p‖^2) hr]
  ring

lemma graphRescale_blend (χ f u : Plane → ℝ) (r e m : ℝ) :
    graphRescale r e m (graphBlend χ f u) =
      graphBlend (fun y ↦ χ (r⁻¹ • y)) (graphRescale r e m f) (graphRescale r e m u) := by
  funext y
  simp only [graphRescale,graphBlend]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_scaled_graph_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (χ f u : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) f →
        ContDiff ℝ (⊤ : ℕ∞) u → ∀ (p : Plane →L[ℝ] ℝ) (r e m q h a b B K : ℝ),
      0 < r → 0 < e → 0 < a → a < b → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η →
      (∀ y, χ y ∈ Icc 0 1) → (∀ y, q ≤ ‖y‖ → χ y = 0) →
      (∀ y, ‖y‖ < q → |m+e*f y| ≤ h) → (∀ y, ‖y‖ < q → |m+e*u y| ≤ h) →
      q+h ≤ a → (∀ t, ‖deriv Real.smoothTransition t‖ ≤ K) →
      sublevelVolume (E ∆ torusGraphRegion cubeCenter n (graphRescale r e m f)) radialSquared ((r*b)^2) < r^3*e^2*B →
      bundleOrientedExcess μ (graphSlopeNormal n (e • (InnerProductSpace.toDual ℝ Plane).symm p)) (r*a) ≤
        r^2*e^2*((∫ y in Metric.ball (0 : Plane) b,
          ‖fderiv ℝ (graphBlend χ f u) y-p‖^2)/2+4*K*b*B/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_interior_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro n hn χ f u hχ hf hu p r e m q h a b B K hr he ha hab hbs hsmall hχb hzero hfH huH hmargin hK hvol
  have hbpos : 0 < b := ha.trans hab
  let g := graphRescale r e m f
  let v := graphRescale r e m (graphBlend χ f u)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := graphRescale_contDiff hf r e m
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := graphRescale_contDiff (graphBlend_contDiff hχ hf hu) r e m
  have hnorm (y : Plane) : ‖r⁻¹ • y‖ = ‖y‖/r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    ring
  have hunchange (y : Plane) (hy : r*q ≤ ‖y‖) : g y = v y := by
    have hz : χ (r⁻¹ • y) = 0 := hzero _ (by rw [hnorm,le_div_iff₀ hr]; nlinarith)
    simp only [g,v,graphRescale,graphBlend_eq_of_zero hz]
  have hgH (y : Plane) (hy : ‖y‖ < r*q) : |g y| ≤ r*h := by
    dsimp [g,graphRescale]
    rw [abs_mul,abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left (hfH _ _) hr.le
    rw [hnorm,div_lt_iff₀ hr]
    nlinarith
  have hvH (y : Plane) (hy : ‖y‖ < r*q) : |v y| ≤ r*h := by
    have hyr : ‖r⁻¹ • y‖ < q := by rw [hnorm,div_lt_iff₀ hr]; nlinarith
    have heq : m+e*graphBlend χ f u (r⁻¹ • y) =
        graphBlend χ (fun y ↦ m+e*f y) (fun y ↦ m+e*u y) (r⁻¹ • y) := by
      simp only [graphBlend]
      ring
    dsimp [v,graphRescale]
    rw [abs_mul,abs_of_pos hr,heq]
    exact mul_le_mul_of_nonneg_left (graphBlend_abs_le (hχb _) (hfH _ hyr) (huH _ hyr)) hr.le
  have hra : 0 < r*a := mul_pos hr ha
  have hrab : r*a < r*b := mul_lt_mul_of_pos_left hab hr
  have hsupp : torusGraphRegion cubeCenter n g ∆ torusGraphRegion cubeCenter n v ⊆
      sublevelRegion radialSquared ((r*a)^2) :=
    torusGraphRegion_interior_symmDiff hn hra.le (hrab.le.trans hbs.le)
      (by nlinarith [mul_le_mul_of_nonneg_left hmargin hr.le]) hunchange hgH hvH
  have htot : sublevelVolume (E ∆ torusGraphRegion cubeCenter n v) radialSquared ((r*b)^2) <
      (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hbs.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hh := hcomp n hn v hv (e • (InnerProductSpace.toDual ℝ Plane).symm p)
    (torusGraphRegion cubeCenter n g) (measurableSet_torusGraphRegion _ _ hg.continuous)
    (r*a) (r*b) (r^3*e^2*B) ((r*b)^3*(Real.pi*8/3)) K hra hrab hbs hsmall hK hsupp hvol htot
  have heq : e • (InnerProductSpace.toDual ℝ Plane).symm p =
      (InnerProductSpace.toDual ℝ Plane).symm (e • p) := by simp only [map_smul]
  rw [heq] at hh ⊢
  simp_rw [plane_relative_gradient_norm] at hh
  dsimp only [v] at hh
  rw [graphRescale_relative_energy (graphBlend_contDiff hχ hf hu) hr] at hh
  apply hh.trans_eq
  have hd : b^2-a^2 ≠ 0 := by nlinarith
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_sequential_oriented_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (r e m h B : ℕ → ℝ) (n : ℕ → Cover) (f : ℕ → Plane → ℝ)
    (hr : ∀ i, 0 < r i) (he : ∀ i, 0 < e i) (hn : ∀ i, ‖n i‖ = 1)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hrlim : Tendsto r atTop (𝓝 0)) (helim : Tendsto e atTop (𝓝 0))
    (hmlim : Tendsto m atTop (𝓝 0)) (hhlim : Tendsto h atTop (𝓝 0))
    (hBlim : Tendsto B atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (p : Plane →L[ℝ] ℝ) {A H : ℝ} (hA : 0 ≤ A)
    (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
    (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
    (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
    (hheight : ∀ i y, ‖y‖ < 2*θ → |m i+e i*f i y| ≤ h i)
    (hmismatch : ∀ i,
      sublevelVolume (E ∆ torusGraphRegion cubeCenter (n i) (graphRescale (r i) (e i) (m i) (f i)))
        radialSquared ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      bundleOrientedExcess μ (graphSlopeNormal (n (ψ i))
        (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
      (r (ψ i))^2*(e (ψ i))^2*(2*H+ε) := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_scaled_graph_comparison hV hE hmin hμ
  obtain ⟨s,q,a,b,D,χ,ψ,hs,hsq,hqa,hab,hb,hψ,hχ,hD,hd,hχb,hone,hzero,hblend⟩ :=
    strong_L2_annulus_replacement hθ f hf hu p hA henergy hH hconv hε
  have ha : 0 < a := (hθ.trans_le hs).trans (hsq.trans hqa)
  have hbpos : 0 < b := ha.trans hab
  have hH0 : 0 ≤ H := (integral_nonneg fun y ↦ sq_nonneg _).trans hH
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0 : Plane) (2*θ)).exists_bound_of_continuousOn hu.continuous.continuousOn
  let M := max M₀ 0
  have hM (y : Plane) (hy : ‖y‖ < q) : |u y| ≤ M := by
    apply (hM₀ y ?_).trans (le_max_left _ _)
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (hy.trans (hqa.trans hab)).le.trans hb
  let height : ℕ → ℝ := fun i ↦ max (h i) (|m i|+e i*M)
  have hheightlim : Tendsto height atTop (𝓝 0) := by
    simpa only [abs_zero,zero_mul,zero_add,max_self] using hhlim.max (hmlim.abs.add (helim.mul_const M))
  obtain ⟨K,hKpos,hK⟩ := smoothTransition_exists_deriv_bound
  have hrblim : Tendsto (fun i ↦ r (ψ i)*b) atTop (𝓝 0) := by
    simpa using (hrlim.comp hψ.tendsto_atTop).mul_const b
  have hvlim : Tendsto (fun i ↦ (r (ψ i)*b)^3*(Real.pi*8/3)) atTop (𝓝 0) := by
    simpa using (hrblim.pow 3).mul_const (Real.pi*8/3)
  have herrlim : Tendsto (fun i ↦ 4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_div,zero_add,Function.comp_def] using
      (((hBlim.comp hψ.tendsto_atTop).const_mul (4*K*b)).div_const (b^2-a^2)).add
        ((hrel.comp hψ.tendsto_atTop).const_mul (C*b^3))
  refine ⟨ψ,hψ,?_⟩
  filter_upwards [hblend,
    hrblim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hvlim.eventually (gt_mem_nhds hη),
    (hheightlim.comp hψ.tendsto_atTop).eventually (gt_mem_nhds (sub_pos.mpr hqa)),
    herrlim.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with i hblend hbs hsmall hmargin herr
  dsimp only [Function.comp_def] at hmargin
  have hfheight (y : Plane) (hy : ‖y‖ < q) : |m (ψ i)+e (ψ i)*f (ψ i) y| ≤ height (ψ i) :=
    (hheight _ _ ((hy.trans (hqa.trans hab)).trans_le hb)).trans (le_max_left _ _)
  have huheight (y : Plane) (hy : ‖y‖ < q) : |m (ψ i)+e (ψ i)*u y| ≤ height (ψ i) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos (he _)]
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hM y hy) (he _).le)).trans (le_max_right _ _)
  have hvol : sublevelVolume
      (E ∆ torusGraphRegion cubeCenter (n (ψ i)) (graphRescale (r (ψ i)) (e (ψ i)) (m (ψ i)) (f (ψ i))))
      radialSquared ((r (ψ i)*b)^2) < (r (ψ i))^3*(e (ψ i))^2*B (ψ i) := by
    apply (sublevelVolume_mono _ _ ?_).trans_lt (hmismatch _)
    apply (sq_le_sq₀ (mul_nonneg (hr _).le hbpos.le) (mul_nonneg (hr _).le (by positivity))).mpr
    exact mul_le_mul_of_nonneg_left hb (hr _).le
  have hh := hcomp (n (ψ i)) (hn _) χ (f (ψ i)) u hχ (hf _) hu p
    (r (ψ i)) (e (ψ i)) (m (ψ i)) q (height (ψ i)) a b (B (ψ i)) K
    (hr _) (he _) ha hab hbs hsmall hχb hzero hfheight huheight (by linarith) hK hvol
  have heq : (r (ψ i))^2*(e (ψ i))^2*
      ((∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
        4*K*b*B (ψ i)/(b^2-a^2))+C*(r (ψ i)*b)^3 =
      (r (ψ i))^2*(e (ψ i))^2*
        ((∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
          (4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2))) := by
    field_simp [(he (ψ i)).ne']
    ring
  rw [heq] at hh
  have hinside : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2)/2+
      (4*K*b*B (ψ i)/(b^2-a^2)+C*b^3*(r (ψ i)/(e (ψ i))^2)) ≤ 2*H+ε := by linarith
  have hmono := bundleOrientedExcess_mono μ
    (graphSlopeNormal_unit (hn (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)).le
    (mul_nonneg (hr (ψ i)).le hθ.le)
    (mul_le_mul_of_nonneg_left (hs.trans (hsq.le.trans hqa.le)) (hr (ψ i)).le)
  exact hmono.trans (hh.trans (mul_le_mul_of_nonneg_left hinside (by positivity)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

lemma graphSmooth_affine (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e : ℝ) (x : Plane) :
    m+e*graphSmooth b f x = ∫ y, (m+e*f (x-y)) ∂graphSmoothingMeasure b := by
  rw [integral_add (integrable_const _) ((graphSmooth_integrable b hf x).const_mul e),
    integral_const_mul]
  simp [graphSmooth]

lemma graphSmooth_affine_abs_le (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e H : ℝ)
    (hH : ∀ y, |m+e*f y| ≤ H) (x : Plane) : |m+e*graphSmooth b f x| ≤ H := by
  rw [graphSmooth_affine b hf]
  calc
    _ ≤ ∫ y, |m+e*f (x-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, H ∂graphSmoothingMeasure b := by
      apply integral_mono ((integrable_const m).add ((graphSmooth_integrable b hf x).const_mul e)).norm
        (integrable_const _)
      exact fun y ↦ hH _
    _ = _ := by simp

theorem exists_sharp_smooth_graph {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ LipschitzWith K g ∧
      (∀ x, |g x-f x| ≤ δ) ∧
      (∀ R : ℝ, (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ g x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2) ∧
      ∀ m e H : ℝ, (∀ y, |m+e*f y| ≤ H) → ∀ y, |m+e*g y| ≤ H := by
  let ρ := δ/((K : ℝ)+1)
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    rw [div_le_iff₀ (by positivity : 0 < (K : ℝ)+1)]
    nlinarith [K.coe_nonneg]
  let b : ContDiffBump (0 : Plane) := ⟨ρ/2,ρ,by positivity,by linarith⟩
  refine ⟨graphSmooth b f,graphSmooth_contDiff b hf,graphSmooth_lipschitz b hf,?_,?_,?_⟩
  · intro x
    apply (graphSmooth_error b hf x).trans
    change (K : ℝ)*ρ ≤ δ
    have hh : ((K : ℝ)+1)*ρ = δ := by dsimp [ρ]; field_simp
    nlinarith
  · intro R
    apply (graphSmooth_local_energy b hf R).2.trans
    exact setIntegral_mono_set (lipschitz_gradient_sq_integrable_ball hf (R+δ))
      (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.ball_subset_ball (add_le_add le_rfl hρδ)).eventuallyLE
  · intro m e H hH y
    exact graphSmooth_affine_abs_le b hf m e H hH y

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def columnPhase (q t : ℝ) : ℝ := (Iio q).indicator (fun _ ↦ (1 : ℝ)) t

def columnGraphMismatch (U : Set Torus) (a : Torus) (n : Cover)
    (r : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ :=
  ∫ t in Icc (-r/4) (r/4), |characteristic U
    (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|

lemma columnPhase_measurable (q : ℝ) : Measurable (columnPhase q) :=
  measurable_const.indicator measurableSet_Iio

lemma columnPhase_difference_le (U : Set Torus) (x : Torus) (q t : ℝ) :
    |characteristic U x-columnPhase q t| ≤ 1 := by
  by_cases hx : x ∈ U <;> by_cases ht : t < q <;>
    simp [characteristic, columnPhase, hx, ht]

lemma columnGraphMismatch_integrable {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (g : Plane → ℝ) (y : Plane) :
    IntegrableOn (fun t ↦ |characteristic U
      (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|)
      (Icc (-r/4) (r/4)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (((measurable_characteristic hU).comp
      (continuous_const.add (continuous_quotientMap.comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable).sub
      (columnPhase_measurable (g y))).abs.aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_abs] using columnPhase_difference_le U _ (g y) t

lemma columnGraphMismatch_nonneg (U : Set Torus) (a : Torus) (n : Cover)
    (r : ℝ) (g : Plane → ℝ) (y : Plane) :
    0 ≤ columnGraphMismatch U a n r g y := integral_nonneg (fun _ ↦ abs_nonneg _)

lemma measurable_columnGraphMismatch {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (columnGraphMismatch U a n r g) := by
  have hc : Continuous (fun p : Plane × ℝ ↦
      a+quotientMap (normalPlaneEmbedding n p.1+p.2 • n)) :=
    continuous_const.add (continuous_quotientMap.comp
      (((normalPlaneLinearIsometry n).continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)))
  have hs : MeasurableSet {p : Plane × ℝ | p.2 < g p.1} :=
    measurableSet_lt measurable_snd (hg.comp measurable_fst)
  have hm : Measurable (fun p : Plane × ℝ ↦ columnPhase (g p.1) p.2) := by
    exact measurable_const.indicator hs
  exact ((((measurable_characteristic hU).comp hc.measurable).sub hm).abs.stronglyMeasurable.integral_prod_right').measurable

lemma good_column_characteristic {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (α*r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r/2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c-a)) ∈ Metric.ball (0 : Plane) (r/4))
    {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    characteristic U (a+quotientMap (normalPlaneEmbedding n
      (normalPlaneCoordinates n (shortestLift (c-a)))+t • n)) =
      columnPhase ⟪n, shortestLift (c-a)⟫ t := by
  have hp := trapped_good_column_phases hU hn hr hrs hα hη htrap hc hcone hy
  by_cases hlt : t < ⟪n, shortestLift (c-a)⟫
  · have hm := hp.1 t ht hlt
    simp [characteristic, columnPhase, hm, hlt]
  · have hm : a+quotientMap (normalPlaneEmbedding n
        (normalPlaneCoordinates n (shortestLift (c-a)))+t • n) ∉ U := by
      rcases lt_or_eq_of_le (le_of_not_gt hlt) with hgt | he
      · exact fun h ↦ hp.2 t ht hgt (subset_closure h)
      · rw [← he, normalPlaneCoordinates_reconstruct hn, quotientMap_shortestLift, add_sub_cancel]
        have hh := hc.1
        rw [frontier, hU.interior_eq] at hh
        exact hh.2
    simp [characteristic, columnPhase, hm, hlt]

lemma columnGraphMismatch_eq_zero_good {U : Set Torus} (hU : IsOpen U)
    {a c : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap a (-n) r (α*r) ⊆ U)
    (hc : c ∈ frontier U ∩ Metric.ball a (r/2))
    (hcone : ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c)
    (hy : normalPlaneCoordinates n (shortestLift (c-a)) ∈ Metric.ball (0 : Plane) (r/4))
    (g : Plane → ℝ) (he : g (normalPlaneCoordinates n (shortestLift (c-a))) =
      ⟪n, shortestLift (c-a)⟫) :
    columnGraphMismatch U a n r g (normalPlaneCoordinates n (shortestLift (c-a))) = 0 := by
  unfold columnGraphMismatch
  rw [he]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [good_column_characteristic hU hn hr hrs hα hη htrap hc hcone hy ht, sub_self, abs_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma small_column_lift (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hrs : r < 1/2) {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4))
    {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a) =
      normalPlaneEmbedding n y+t • n ∧
      dist (a+quotientMap (normalPlaneEmbedding n y+t • n)) a < r/2 := by
  have hy' : ‖y‖ < r/4 := by simpa only [mem_ball, dist_zero_right] using hy
  have hab : |t| ≤ r/4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hnorm : ‖normalPlaneEmbedding n y+t • n‖ < r/2 := by
    have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
    rw [normalPlaneEmbedding_norm, norm_smul, hn, mul_one, Real.norm_eq_abs] at hh
    linarith
  have hl : shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a) =
      normalPlaneEmbedding n y+t • n := by
    rw [add_sub_cancel_left]
    exact shortestLift_quotientMap (hnorm.trans (by linarith))
  exact ⟨hl, by rw [dist_eq_norm, ← norm_shortestLift, hl]; exact hnorm⟩

lemma trapped_column_phases {U : Set Torus} {a : Torus} {n : Cover} (hn : ‖n‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hrs : r < 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4)) {t : ℝ} (ht : t ∈ Icc (-r/4) (r/4)) :
    (t < -(α*r) → a+quotientMap (normalPlaneEmbedding n y+t • n) ∈ U) ∧
      (α*r < t → a+quotientMap (normalPlaneEmbedding n y+t • n) ∉ closure U) := by
  have hh := small_column_lift a hn hrs hy ht
  have hh' : ⟪n, shortestLift ((a+quotientMap (normalPlaneEmbedding n y+t • n))-a)⟫ = t := by
    rw [hh.1, inner_add_right, normalPlaneEmbedding_inner hn, inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    ring
  constructor
  · intro htlo
    apply htrap.2
    exact ⟨hh.2.trans (by linarith), by rw [inner_neg_left, hh']; linarith⟩
  · intro hthi
    exact htrap.1 ⟨hh.2.trans (by linarith), by rw [hh']; exact hthi⟩

lemma columnGraphMismatch_trapped_le {U : Set Torus} (hU : MeasurableSet U)
    {a : Torus} {n : Cover} (hn : ‖n‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα0 : 0 ≤ α) (hα : α < 1/4)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (g : Plane → ℝ) {y : Plane} (hy : y ∈ Metric.ball (0 : Plane) (r/4))
    (hg : |g y| ≤ α*r) : columnGraphMismatch U a n r g y ≤ 2*α*r := by
  have hsub : Icc (-(α*r)) (α*r) ⊆ Icc (-r/4) (r/4) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hi : IntegrableOn ((Icc (-(α*r)) (α*r)).indicator (fun _ : ℝ ↦ (1 : ℝ)))
      (Icc (-r/4) (r/4)) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc
    _ ≤ ∫ t in Icc (-r/4) (r/4), (Icc (-(α*r)) (α*r)).indicator (fun _ : ℝ ↦ (1 : ℝ)) t := by
      apply integral_mono_ae (columnGraphMismatch_integrable hU a n r g y) hi
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      by_cases hs : t ∈ Icc (-(α*r)) (α*r)
      · rw [indicator_of_mem hs]
        exact columnPhase_difference_le U _ (g y) t
      · rw [indicator_of_notMem hs]
        have hp := trapped_column_phases hn hr hrs htrap hy ht
        simp only [mem_Icc, not_and_or, not_le] at hs
        rcases hs with hlo | hhi
        · have hu := hp.1 hlo
          have hlt : t < g y := hlo.trans_le (abs_le.mp hg).1
          simp [characteristic, columnPhase, hu, hlt]
        · have hu : a+quotientMap (normalPlaneEmbedding n y+t • n) ∉ U :=
            fun h ↦ hp.2 hhi (subset_closure h)
          have hlt : ¬ t < g y := not_lt.mpr ((abs_le.mp hg).2.trans hhi.le)
          simp [characteristic, columnPhase, hu, hlt]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Icc, inter_eq_right.mpr hsub,
        integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, ENNReal.toReal_ofReal (by nlinarith [mul_nonneg hα0 hr.le] : 0 ≤ α*r - -(α*r))]
      ring

end CubicTorus

end
end

end

end OAI
