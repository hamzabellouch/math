import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVInteriorMultiplier

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma torusGraphRegion_symmDiff_real_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume.real ((U ∆ torusGraphRegion (c : Cover) n g) ∩ Metric.ball (quotientMap (c : Cover)) s) ≤
      ∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U (quotientMap (c : Cover)) n r g y := by
  have hh := torusGraphRegion_symmDiff_ball_le (c:=c) hU hn hrs hs hg
  rw [← ofReal_integral_eq_lintegral_ofReal
    (columnGraphMismatch_integrable_ball hU _ n hr hg.measurable (r/4))
    (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hh
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at ht
  exact ht

theorem exists_physical_smooth_graph {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {r δ α : ℝ} (hr : 0 < r) (hrs : r < 1) (hδ : 0 < δ) (hδr : δ ≤ r/8)
    (hα : α ≤ 1/4) (hheight : ∀ y, |g y| ≤ α*r) :
    ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith K G ∧
      (∀ y, |G y| ≤ α*r) ∧
      (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ∧
      (let B := (∫ y in Metric.ball (0 : Plane) (r/4),
          columnGraphMismatch U (quotientMap (c : Cover)) n r g y)+
            δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4))
       (∫ y in Metric.ball (0 : Plane) (r/4),
          |G y-normalColumnHeight U (quotientMap (c : Cover)) n r y|) ≤ B ∧
       ∀ s : ℝ, s ≤ r/4 → torusVolume.real ((U ∆ torusGraphRegion (c : Cover) n G) ∩
         Metric.ball (quotientMap (c : Cover)) s) ≤ B) := by
  obtain ⟨G,hG,hGL,he,henergy,hH⟩ := exists_sharp_smooth_graph hg hδ
  have hh (y : Plane) : |G y| ≤ α*r := by
    simpa only [zero_add,one_mul] using hH 0 1 (α*r) (by simpa only [zero_add,one_mul] using hheight) y
  have hb (y : Plane) : |G y| ≤ r/4 := (hh y).trans (by nlinarith)
  refine ⟨G,hG,hGL,hh,?_,?_⟩
  · exact (henergy (r/8)).trans (setIntegral_mono_set
      (lipschitz_gradient_sq_integrable_ball hg (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball (by linarith)).eventuallyLE)
  · have herr := columnGraphMismatch_integral_change_le hU (quotientMap (c : Cover)) n hr.le
      hG.continuous.measurable hg.continuous.measurable he (r/4)
    have hv : (volume : Measure Plane).real (Metric.ball 0 (r/4)) =
        r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_one_div] using plane_ball_real_volume_scale hr (1/4)
    rw [hv] at herr
    have herr' : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
        (quotientMap (c : Cover)) n r G y) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
          (quotientMap (c : Cover)) n r g y)+δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_assoc] using herr
    exact ⟨(normalColumnHeight_integral_error_le hU _ n hr.le hG.continuous.measurable hb (r/4)).trans herr',
      fun s hs ↦ (torusGraphRegion_symmDiff_real_ball_le hU hn hr.le hrs hs hG.continuous).trans herr'⟩

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_smooth_trapped_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ D : ℝ, 0 < r₀ ∧ 0 ≤ D ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 → ∀ r α e : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1/4 →
        0 < e → e ≤ 1/2 →
        (normalCap (quotientMap (c : Cover)) n r (α*r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c : Cover)) (-n) r (α*r) ⊆ openRepresentative E) →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith 1 G ∧
        (∀ y, |G y| ≤ α*r) ∧
        (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤ r^2*e^2*D ∧
        (let B := r^3*e^2*(D*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4)))
         (∫ y in Metric.ball (0 : Plane) (r/4),
            |G y-normalColumnHeight (openRepresentative E) (quotientMap (c : Cover)) n r y|) ≤ B ∧
         ∀ s : ℝ, s ≤ r/4 → torusVolume.real
           (((openRepresentative E) ∆ torusGraphRegion (c : Cover) n G) ∩
             Metric.ball (quotientMap (c : Cover)) s) ≤ B) := by
  obtain ⟨R,C,hR,hC,happ⟩ := isMinimizerAt_tightly_trapped_graph_approximation
    hV hE hmin (by norm_num : (0:ℝ)<1/2) le_rfl
  refine ⟨min R (1/4),C.toReal,by positivity,ENNReal.toReal_nonneg,?_⟩
  intro μ hμ N hN hp hunit c n hn r α e hr hrr hα0 hα he hes htrap htilt
  have hrs : r < 1 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S,g,hg,hh,hS,hgood,hcone,hbad,henergy,hmismatch⟩ :=
    happ μ hμ N hN hp hunit (quotientMap (c : Cover)) n hn r α hr
      (hrr.trans (min_le_left _ _)) hα0 hα htrap
  have hg1 : LipschitzWith 1 g := hg.weaken (by
    change (2:ℝ)*(1/2) ≤ 1
    norm_num)
  let T := ∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
    ∂(spatialNormalMeasure μ : Measure Torus)
  have hT : 0 ≤ T := integral_nonneg fun x ↦ sq_nonneg _
  have hgE : (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ≤ C.toReal*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal (lipschitz_gradient_sq_integrable_ball hg1 (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _)] at henergy
    have ht := ENNReal.toReal_mono (by finiteness) henergy
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun y ↦ sq_nonneg _)] using ht
  have hgM : (∫ y in Metric.ball (0 : Plane) (r/4),
      columnGraphMismatch (openRepresentative E) (quotientMap (c : Cover)) n r g y) ≤
        C.toReal*α*r*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (columnGraphMismatch_integrable_ball (isOpen_openRepresentative E).measurableSet
        _ n hr.le hg1.continuous.measurable (r/4))
      (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hmismatch
    have ht := ENNReal.toReal_mono (by finiteness) hmismatch
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun x ↦ sq_nonneg _),ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofReal
        (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] using ht
  have hδ : 0 < r*e^3 := by positivity
  have he3 : e^3 ≤ 1/8 := by nlinarith [mul_le_mul_of_nonneg_left hes he.le, sq_nonneg (e-1/2)]
  have hδr : r*e^3 ≤ r/8 := by nlinarith
  obtain ⟨G,hG,hGL,hheight,hGE,hGM⟩ := exists_physical_smooth_graph (c:=c)
    (isOpen_openRepresentative E).measurableSet hn hg1 hr hrs hδ hδr hα.le hh
  have hB : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch
      (openRepresentative E) (quotientMap (c : Cover)) n r g y)+
      (r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) ≤
      r^3*e^2*(C.toReal*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4))) := by
    have hx := hgM.trans (mul_le_mul_of_nonneg_left htilt (by positivity : 0 ≤ C.toReal*α*r))
    calc
      _ ≤ C.toReal*α*r*(r^2*e^2)+(r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := add_le_add hx le_rfl
      _ = _ := by ring
  refine ⟨G,hG,hGL,hheight,?_,hGM.1.trans hB,fun s hs ↦ (hGM.2 s hs).trans hB⟩
  exact hGE.trans (hgE.trans ((mul_le_mul_of_nonneg_left htilt ENNReal.toReal_nonneg).trans_eq (by ring)))

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem weakCMC_spatial_normalized_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {r α e A C : ℝ}
    (hr : 0 < r) (hrs : r < 3/8) (hα : α < 1/4) (he : 0 < e)
    (htrap : normalCap (quotientMap (c : Cover)) n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap (c : Cover)) (-n) r (α*r) ⊆ U)
    (htilt : (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (ha : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) r) ≤ A*r^2)
    {g : Plane → ℝ} (hg : Continuous g)
    (hcol : (∫ y in Metric.ball (0 : Plane) (r/4),
      |g y-normalColumnHeight U (quotientMap (c : Cover)) n r y|) ≤ C*r^3*e^2)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (1/4))
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) (m : ℝ) :
    |∫ y : Plane, graphNormalize r e m g y*Δ φ y| ≤
      (D/2+C*Q)*e+|H| * B*A*(r/e) := by
  have hc := closedBall_interior (c:=c) hrs
  have hcb := Metric.ball_subset_closedBall.trans hc
  apply weakCMC_normalized_graph_residual hU hμ hH hn hr (by linarith) hα he htrap hc
    (g := g) (m := r*m) ?_ ?_ hg hcol hφ hs hB hD hQ hb hd hq
  · rw [← integral_polar_tilt_ball hN hp (c : Cover) n r hcb]
    apply (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
      (Eventually.of_forall fun x ↦ sq_nonneg _) ?_).trans htilt
    exact (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).eventuallyLE
  · change cellBallMass μ (c : Cover) r ≤ A*r^2
    rwa [cellBallMass_eq_spatialNormalMeasure μ (c : Cover) r hcb]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem weakCMC_normalized_sequence_harmonic {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e m C : ℕ → ℝ) (g : ℕ → Plane → ℝ) (A : ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < 3/8)
    (hα : ∀ i, α i < 1/4) (he : ∀ i, 0 < e i)
    (htrap : ∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ U)
    (htilt : ∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2)
    (ha : ∀ i, (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c i : Cover)) (r i)) ≤ A*(r i)^2)
    (hg : ∀ i, Continuous (g i))
    (hcol : ∀ i, (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight U (quotientMap (c i : Cover)) (n i) (r i) y|) ≤ C i*(r i)^3*(e i)^2)
    (helim : Tendsto e atTop (𝓝 0)) (hClim : Tendsto C atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Plane) (1/4) →
      Tendsto (fun i ↦ ∫ y, graphNormalize (r i) (e i) (m i) (g i) y*Δ φ y) atTop (𝓝 0) := by
  intro φ hφ hc hs
  obtain ⟨B,D,Q,hB,hD,hQ,hb,hd,hq⟩ := smooth_compact_test_bounds hφ hc
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hrE : Tendsto (fun i ↦ r i/e i) atTop (𝓝 0) := by
    have hfun : (fun i ↦ (r i/(e i)^2)*e i) = (fun i ↦ r i/e i) := by
      funext i
      field_simp [(he i).ne']
    simpa only [hfun,mul_zero] using hrel.mul helim
  have hl : Tendsto (fun i ↦ (D/2+C i*Q)*e i+|H| * B*A*(r i/e i)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,add_zero] using
      ((tendsto_const_nhds.add (hClim.mul_const Q)).mul helim).add (hrE.const_mul (|H| * B*A))
  apply squeeze_zero' (Eventually.of_forall fun i ↦ abs_nonneg _) _ hl
  exact Eventually.of_forall fun i ↦ weakCMC_spatial_normalized_residual hU hμ hH hN hp hu
    (hn i) (hr i) (hrs i) (hα i) (he i) (htrap i) (htilt i) (ha i) (hg i) (hcol i)
      hφ hs hB hD hQ hb hd hq (m i)

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapped_harmonic_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ Q R D M C : ℝ, 0 < r₀ ∧ 0 < Q ∧ 0 < R ∧ R ≤ 1/8 ∧
      0 ≤ D ∧ 0 ≤ M ∧ 0 < C ∧ Metric.ball (0 : Plane) R ⊆ planeSquare Q ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (m : ℕ → ℝ) (g : ℕ → Plane → ℝ) (ψ : ℕ → ℕ) (u : Plane → ℝ),
        StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) ∧ LipschitzWith 1 (g i) ∧
          (∀ y, |g i y| ≤ α i*r i) ∧ |m i| ≤ α i ∧
          (∫ y in planeSquare Q, ‖fderiv ℝ (graphNormalize (r i) (e i) (m i) (g i)) y‖^2) ≤ D ∧
          (∫ y in planeSquare Q, (graphNormalize (r i) (e i) (m i) (g i) y)^2) ≤ M ∧
          (∀ s : ℝ, s ≤ r i/4 → torusVolume.real
            (((openRepresentative E) ∆ torusGraphRegion (c i : Cover) (n i) (g i)) ∩
              Metric.ball (quotientMap (c i : Cover)) s) ≤
              (r i)^3*(e i)^2*(D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))))) ∧
        Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) R,
          (graphNormalize (r (ψ i)) (e (ψ i)) (m (ψ i)) (g (ψ i)) y-u y)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ y in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u y-fderiv ℝ u 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨R₀,D,hR₀,hD,happ⟩ := isMinimizerAt_smooth_trapped_approximation hV hE hmin
  obtain ⟨R₁,A,hR₁,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨Q,hQ,hQs⟩ := exists_small_planeSquare
  obtain ⟨R,C,hR,hC,hRQ,hharm⟩ := planeSquare_H1_strong_harmonic hQ
  let M := 16*Q^2*‖planeProductCoordinates.symm.toContinuousLinearMap‖^2*D
  have hMs : 0 ≤ M := by dsimp [M]; positivity
  have hRR : min R (1/8) ≤ 4*R := (min_le_left _ _).trans (by linarith)
  refine ⟨min (min R₀ R₁) (1/4),Q,min R (1/8),D,M,C,by positivity,hQ,by positivity,
    min_le_right _ _,hD,hMs,hC,(Metric.ball_subset_ball hRR).trans hRQ,?_⟩
  intro μ hμ H hH N hN hp hu c n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt
  have hr₀ (i) : r i ≤ R₀ := (hrr i).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ (i) : r i ≤ R₁ := (hrr i).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrs (i) : r i < 3/8 := lt_of_le_of_lt ((hrr i).trans (min_le_right _ _)) (by norm_num)
  have ha (i) := harea μ hμ (quotientMap (c i : Cover)) (r i) (hr i) (hr₁ i)
  have hgraphs (i) := happ μ hμ N hN hp hu (c i) (n i) (hn i) (r i) (α i) (e i)
    (hr i) (hr₀ i) (hα0 i) (hα i) (he i) (hes i) (htrap i) (htilt i)
  choose g hg hL hh henergy herror using hgraphs
  have hmeans (i) := smooth_graph_normalized_H1 (hg i) (hL i) (hr i) (he i) hQ hQs (hh i)
    (by simpa only [mul_one_div] using henergy i)
  choose m hm hgrad hval using hmeans
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  let L (i : ℕ) : ℝ≥0 := ⟨(e i)⁻¹,inv_nonneg.mpr (he i).le⟩*1
  have hfL (i) : LipschitzWith (L i) (f i) := graphNormalize_lipschitz (hL i) (hr i) (he i) (m i)
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hHU (w : WallVariation) : normalFirstVariation μ w = H*directionalFlux (openRepresentative E) w.coordinate w.function := by
    rw [directionalFlux_congr_ae hUE]
    exact hH w
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using (hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))
  have hcol (i) : (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight (openRepresentative E) (quotientMap (c i : Cover)) (n i) (r i) y|) ≤
      B i*(r i)^3*(e i)^2 := by
    exact (herror i).1.trans_eq (by dsimp [B]; ring)
  have hw := weakCMC_normalized_sequence_harmonic (isOpen_openRepresentative E) hμU hHU hN hp hu
    c n r α e m B g A hn hr hrs hα he htrap htilt ha (fun i ↦ (hg i).continuous)
    hcol helim hBlim hrel
  obtain ⟨ψ,u,hψ,huS,hconv,huE⟩ := hharm f L hfL M D hD hval hgrad
    (fun φ hφ hc hs ↦ hw φ hφ hc (hs.trans (hRQ.trans (hQs.trans (Metric.ball_subset_ball (by norm_num))))))
  refine ⟨m,g,ψ,u,hψ,huS,?_,?_,huE⟩
  · intro i
    exact ⟨hg i,hL i,hh i,hm i,hgrad i,hval i,(herror i).2⟩
  · exact strongL2_restrict_ball (fun i ↦ (graphNormalize_contDiff (hg (ψ i)) _ _ _).continuous)
      huS.continuous (min_le_left _ _) hconv

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma radialDensityWeight_cell_support {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 3/8) (hε : 0 < ε) :
    tsupport (radialDensityWeight (c : Cover) r ε) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := radialDensityWeight_tsupport hr hε hx
  have hd : ‖x-(c : Cover)‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
  have hi := (PiLp.norm_apply_le (x-(c : Cover)) i).trans hd
  change ‖x i - (c : Cover) i‖ ≤ r at hi
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hi
  constructor <;> linarith

lemma radialDensityWeight_periodize {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/4) (hε : 0 < ε) :
    latticePeriodize (radialDensityWeight (c : Cover) r ε) = sublevelCutoff (radialSquared c) (r^2) ε := by
  funext x
  rw [← periodic_representative (latticePeriodize_periodic _) x,
    ← periodic_representative (sublevelCutoff_periodic radialSquared_periodic (r^2) ε) x]
  let z := representative (quotientMap x)
  have hz : z ∈ fundamentalCube := representative_mem_fundamentalCube _
  rw [(latticePeriodize_eventuallyEq (radialDensityWeight_hasCompactSupport (a := (c : Cover)) hr hε)
    (radialDensityWeight_cell_support hr (by linarith) hε)
    (fun i ↦ ⟨(hz i).1, (hz i).2.le⟩)).eq_of_nhds]
  change radialDensityWeight (c : Cover) r ε z = sublevelCutoff (radialSquared c) (r^2) ε z
  by_cases hz' : ‖z-(c : Cover)‖ < r
  · have he := (radialSquared_eventuallyEq_norm_sq (hz'.trans hs)).eq_of_nhds
    simp only [radialDensityWeight, sublevelCutoff, he]
  · have hh : ¬ (radialSquared c) z < r^2 := by
      rw [radialSquared_sublevel_iff hz (by nlinarith)]
      have hb : r ≤ ‖z-(c : Cover)‖ := le_of_not_gt hz'
      nlinarith [norm_nonneg (z-(c : Cover))]
    rw [radialDensityWeight_zero hr hε (le_of_not_gt hz')]
    exact (Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt hh)) hε.le)).symm

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

def bundleOrientedExcess (c : InteriorCenter) (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) : ℝ :=
  ∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, 1-⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)

lemma bundleOrientedExcess_eq (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) :
    (bundleOrientedExcess c) μ ν r = (μ : Measure NormalBundle).real {z | (radialSquared c) z.1 < r^2} -
      ∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle) := by
  rw [bundleOrientedExcess, integral_sub (integrable_const 1)
    ((show Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply_univ]

theorem isMinimizerAt_oriented_graph_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (ν : Cover), ‖ν‖ ≤ 1 → ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ r K d : ℝ, 0 < r → r < 1/4 → (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      HasDerivAt (sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c)) d (r^2) →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (r^2) < η →
      (bundleOrientedExcess c) μ ν r ≤ graphBallOrientedCost (c : Cover) n ν g r +
        2*K*(2*r)*d + C*sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (r^2) := by
  obtain ⟨η,C,hη,hC,hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η,C,hη,hC,?_⟩
  intro c n hn ν hν g hg r K d hr hs hK hd ht
  let F := torusGraphRegion (c : Cover) n g
  have hF : MeasurableSet F := measurableSet_torusGraphRegion _ _ hg.continuous
  let ε : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let m := sublevelVolume (E ∆ F) (radialSquared c)
  let A : ℕ → ℝ := fun i ↦ ∫ y : Plane, radialDensityWeight (c : Cover) r (ε i)
    ((c : Cover)+normalGraph n g y)*graphOrientedCost n ν g y
  let N : ℕ → ℝ := fun i ↦ ∫ z : NormalBundle, sublevelCutoff (radialSquared c) (r^2) (ε i) z.1 *
    ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)
  let D : ℕ → ℝ := fun i ↦ K*(2*r)*((m (r^2)-m (r^2-ε i))/ε i)
  let L : ℕ → ℝ := fun i ↦ A i + N i + D i
  have hAlim := graphBallOrientedCost_tendsto (c : Cover) hn hν hg hr he helim
  have hNlim := normalMeasure_sublevelCutoff_inner_tendsto μ (radialSquared_contDiff (c:=c)).continuous
    (radialSquared_periodic (c:=c)) he helim (r^2) hν
  have hDlim : Tendsto D atTop (𝓝 (K*(2*r)*d)) :=
    tendsto_const_nhds.mul (tendsto_backward_quotient_of_hasDerivAt hd he helim)
  have hlim : Tendsto L atTop (𝓝 (graphBallOrientedCost (c : Cover) n ν g r +
      (∫ z : NormalBundle in {z | (radialSquared c) z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)) +
      K*(2*r)*d)) := (hAlim.add hNlim).add hDlim
  have hlocal (i : ℕ) (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff (radialSquared c) (r^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L i := by
    let w := radialDensityWeight (c : Cover) r (ε i)
    have hw : ContDiff ℝ (⊤ : ℕ∞) w := radialDensityWeight_contDiff _ _ _
    have hwc : HasCompactSupport w := radialDensityWeight_hasCompactSupport hr.le (he i)
    have hws : tsupport w ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
      radialDensityWeight_cell_support hr.le (by linarith) (he i)
    have hperiod : latticePeriodize w = sublevelCutoff (radialSquared c) (r^2) (ε i) :=
      radialDensityWeight_periodize hr.le hs (he i)
    have hf := integral_graphSublevel_relative_flux_le (c : Cover) hn hg hw hwc
      (fun x ↦ radialDensityWeight_nonneg _ _ _ x) ν hX
    rw [← interior_cutoff_flux_eq (c : Cover) n g hwc hws X,
      ← interior_cutoff_flux_eq (c : Cover) n g hwc hws (fun _ ↦ ν), hperiod] at hf
    have hdif := cutoff_constant_flux_sub_le hE hF
      (sublevelCutoff_contDiff (radialSquared_contDiff (c:=c)) (r^2) (ε i))
      (sublevelCutoff_periodic (radialSquared_periodic (c:=c)) (r^2) (ε i)) hν
    rw [cutoff_constant_flux_normal hE hμ
      (sublevelCutoff_contDiff (radialSquared_contDiff (c:=c)) (r^2) (ε i))
      (sublevelCutoff_periodic (radialSquared_periodic (c:=c)) (r^2) (ε i)) hν] at hdif
    have hgrad := sublevelCutoff_gradient_integral_le (hE.symmDiff hF) (radialSquared_contDiff (c:=c))
      (radialSquared_periodic (c:=c)) hK (norm_gradient_radialSquared hr.le hs.le) (he i)
    change _ ≤ A i + _ at hf
    change _ ≤ N i + _ at hdif
    change _ ≤ D i at hgrad
    dsimp only [L]
    linarith
  obtain ⟨hG,hb⟩ := perimeter_glued_local_flux_le hE hF hμ (radialSquared_contDiff (c:=c))
    (radialSquared_periodic (c:=c)) hK (norm_gradient_radialSquared hr.le hs.le) hd hlim hlocal
  have hdist : regionDistance E (gluedRegion E F (sublevelRegion (radialSquared c) (r^2))) =
      sublevelVolume (E ∆ F) (radialSquared c) (r^2) :=
    regionDistance_gluedRegion hE.nullMeasurableSet hF.nullMeasurableSet
      (measurableSet_sublevelRegion (radialSquared_contDiff (c:=c)).continuous.measurable _).nullMeasurableSet
  have hcomp := hc _ hG (hdist ▸ ht)
  rw [hdist] at hcomp
  rw [hμ.1] at hb
  rw [bundleOrientedExcess_eq]
  change _ ≤ graphBallOrientedCost (c : Cover) n ν g r + 2*K*(2*r)*d +
    C*sublevelVolume (E ∆ F) (radialSquared c) (r^2)
  linarith

lemma bundleOrientedExcess_nonneg (μ : FiniteMeasure NormalBundle) {ν : Cover}
    (hν : ‖ν‖ ≤ 1) (r : ℝ) : 0 ≤ (bundleOrientedExcess c) μ ν r := by
  apply integral_nonneg
  intro z
  have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
  exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν))

lemma bundleOrientedExcess_mono (μ : FiniteMeasure NormalBundle) {ν : Cover}
    (hν : ‖ν‖ ≤ 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    (bundleOrientedExcess c) μ ν r ≤ (bundleOrientedExcess c) μ ν s := by
  have hi : Integrable (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hi.integrableOn
  · exact Eventually.of_forall fun z ↦ by
      have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
      exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν))
  · exact (show {z : NormalBundle | (radialSquared c) z.1 < r^2} ⊆ {z | (radialSquared c) z.1 < s^2} from
      fun z hz ↦ hz.trans_le (sq_le_sq₀ hr (hr.trans hrs) |>.mpr hrs)).eventuallyLE

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_oriented_interior_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ (p : Plane) (F : Set Torus), MeasurableSet F →
      ∀ a b B T K : ℝ, 0 < a → a < b → b < 1/4 → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ torusGraphRegion (c : Cover) n g ⊆ sublevelRegion (radialSquared c) (a^2) →
      sublevelVolume (E ∆ F) (radialSquared c) (b^2) < B →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (b^2) < T →
      (bundleOrientedExcess c) μ (graphSlopeNormal n p) a ≤
        (∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2)/2 +
          4*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_graph_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro c n hn g hg p F hF a b B T K ha hab hbs hT hK hchange he htotal
  let m := sublevelVolume (E ∆ F) (radialSquared c)
  have hm : Monotone m := sublevelVolume_mono _ _
  have ha2b2 : a^2 < b^2 := by nlinarith
  have hmb : m (b^2) < B := he
  have hmb0 : 0 ≤ m (b^2) := measureReal_nonneg
  have hB0 : 0 < B := hmb0.trans_lt hmb
  have hden : 0 < b^2-a^2 := sub_pos.mpr ha2b2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hden.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm ha2b2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hmt : m t < B := (hm ht.2.le).trans_lt hmb
  have hν : ‖graphSlopeNormal n p‖ ≤ 1 := (graphSlopeNormal_unit hn p).le
  have hderG := hasDerivAt_sublevelVolume_of_interior_change radialSquared_contDiff.continuous.measurable
    ht.1 hchange hd.hasDerivAt
  have htotρ : sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (ρ^2) < T :=
    (sublevelVolume_mono _ _ (by rw [hρsq]; exact ht.2.le)).trans_lt htotal
  have hcompare := hcomp c n hn (graphSlopeNormal n p) hν g hg ρ K (deriv m t) hρ0
    (hρb.trans hbs) hK (hρsq ▸ hderG) (htotρ.trans hT)
  have har := graphBallOrientedCost_le_disk (c : Cover) hn hg p ρ
  have henergy : (∫ y in Metric.ball (0 : Plane) ρ, ‖gradient g y-p‖^2) ≤
      ∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2 :=
    setIntegral_mono_set (smooth_graph_relative_energy_integrable hg p b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hρb.le).eventuallyLE
  have hmono := bundleOrientedExcess_mono (c:=c) μ hν ha.le hρa.le
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : 2*K*(2*ρ)*deriv m t ≤ 2*K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : 2*K*(2*ρ)*(B/(b^2-a^2)) ≤ 2*K*(2*b)*(B/(b^2-a^2)) := by
    gcongr
  have hc1 : C*sublevelVolume (E ∆ torusGraphRegion (c : Cover) n g) (radialSquared c) (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left htotρ.le hC
  have heq : 4*K*b*B/(b^2-a^2) = 2*K*(2*b)*(B/(b^2-a^2)) := by ring
  rw [heq]
  linarith

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma torusGraphRegion_interior_symmDiff {n : Cover} (hn : ‖n‖ = 1)
    {f g : Plane → ℝ} {q H a : ℝ} (ha : 0 ≤ a) (has : a ≤ 1/4)
    (hmargin : q+H ≤ a)
    (he : ∀ y, q ≤ ‖y‖ → f y = g y)
    (hf : ∀ y, ‖y‖ < q → |f y| ≤ H)
    (hg : ∀ y, ‖y‖ < q → |g y| ≤ H) :
    torusGraphRegion (c : Cover) n f ∆ torusGraphRegion (c : Cover) n g ⊆
      sublevelRegion (radialSquared c) (a^2) := by
  intro z hz
  let v := representative z-(c : Cover)
  let y := normalPlaneCoordinates n v
  let t := ⟪n,v⟫
  have hz' : (t < f y ∧ ¬t < g y) ∨ (t < g y ∧ ¬t < f y) := hz
  have hy : ‖y‖ < q := by
    by_contra! hy
    have hh := he y hy
    rw [hh] at hz'
    rcases hz' with hz' | hz'
    · exact hz'.2 hz'.1
    · exact hz'.2 hz'.1
  have hf' := abs_le.mp (hf y hy)
  have hg' := abs_le.mp (hg y hy)
  have ht : |t| ≤ H := by
    rw [abs_le]
    rcases hz' with hz' | hz' <;> constructor <;> linarith
  have hv : ‖v‖ ≤ ‖y‖+|t| := by
    rw [← normalPlaneCoordinates_reconstruct hn v]
    exact (norm_add_le _ _).trans (by simp only [normalPlaneEmbedding_norm,norm_smul,
      Real.norm_eq_abs,hn,mul_one,y,t]; rfl)
  rw [sublevelRegion_radialSquared ha has]
  change dist (representative z) (c : Cover) < a
  rw [dist_eq_norm]
  change ‖v‖ < a
  linarith

lemma radial_sublevelVolume_le (E : Set Torus) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ 1/4) :
    sublevelVolume E (radialSquared c) (r^2) ≤ r^3*(Real.pi*4/3) := by
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared hr hrs]
  apply (measureReal_mono inter_subset_right).trans_eq
  rw [Measure.real,volume_cubeBall hr (by linarith),ENNReal.toReal_ofReal (by positivity)]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_scaled_graph_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (c : InteriorCenter) (n : Cover), ‖n‖ = 1 →
      ∀ (χ f u : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) f →
        ContDiff ℝ (⊤ : ℕ∞) u → ∀ (p : Plane →L[ℝ] ℝ) (r e m q h a b B K : ℝ),
      0 < r → 0 < e → 0 < a → a < b → r*b < 1/4 →
      (r*b)^3*(Real.pi*8/3) < η →
      (∀ y, χ y ∈ Icc 0 1) → (∀ y, q ≤ ‖y‖ → χ y = 0) →
      (∀ y, ‖y‖ < q → |m+e*f y| ≤ h) → (∀ y, ‖y‖ < q → |m+e*u y| ≤ h) →
      q+h ≤ a → (∀ t, ‖deriv Real.smoothTransition t‖ ≤ K) →
      sublevelVolume (E ∆ torusGraphRegion (c : Cover) n (graphRescale r e m f)) (radialSquared c) ((r*b)^2) < r^3*e^2*B →
      (bundleOrientedExcess c) μ (graphSlopeNormal n (e • (InnerProductSpace.toDual ℝ Plane).symm p)) (r*a) ≤
        r^2*e^2*((∫ y in Metric.ball (0 : Plane) b,
          ‖fderiv ℝ (graphBlend χ f u) y-p‖^2)/2+4*K*b*B/(b^2-a^2))+C*(r*b)^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_interior_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro c n hn χ f u hχ hf hu p r e m q h a b B K hr he ha hab hbs hsmall hχb hzero hfH huH hmargin hK hvol
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
  have hsupp : torusGraphRegion (c : Cover) n g ∆ torusGraphRegion (c : Cover) n v ⊆
      sublevelRegion (radialSquared c) ((r*a)^2) :=
    torusGraphRegion_interior_symmDiff hn hra.le (hrab.le.trans hbs.le)
      (by nlinarith [mul_le_mul_of_nonneg_left hmargin hr.le]) hunchange hgH hvH
  have htot : sublevelVolume (E ∆ torusGraphRegion (c : Cover) n v) (radialSquared c) ((r*b)^2) <
      (r*b)^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (hra.trans hrab).le hbs.le).trans_lt
    have hbp : 0 < (r*b)^3*Real.pi := by positivity
    nlinarith
  have hh := hcomp c n hn v hv (e • (InnerProductSpace.toDual ℝ Plane).symm p)
    (torusGraphRegion (c : Cover) n g) (measurableSet_torusGraphRegion _ _ hg.continuous)
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

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_sequential_oriented_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → InteriorCenter) (r e m h B : ℕ → ℝ) (n : ℕ → Cover) (f : ℕ → Plane → ℝ)
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
      sublevelVolume (E ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
        (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
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
      (E ∆ torusGraphRegion (c (ψ i) : Cover) (n (ψ i)) (graphRescale (r (ψ i)) (e (ψ i)) (m (ψ i)) (f (ψ i))))
      (radialSquared (c (ψ i))) ((r (ψ i)*b)^2) < (r (ψ i))^3*(e (ψ i))^2*B (ψ i) := by
    apply (sublevelVolume_mono _ _ ?_).trans_lt (hmismatch _)
    apply (sq_le_sq₀ (mul_nonneg (hr _).le hbpos.le) (mul_nonneg (hr _).le (by positivity))).mpr
    exact mul_le_mul_of_nonneg_left hb (hr _).le
  have hh := hcomp (c (ψ i)) (n (ψ i)) (hn _) χ (f (ψ i)) u hχ (hf _) hu p
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
  have hmono := bundleOrientedExcess_mono (c:=c (ψ i)) μ
    (graphSlopeNormal_unit (hn (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)).le
    (mul_nonneg (hr (ψ i)).le hθ.le)
    (mul_le_mul_of_nonneg_left (hs.trans (hsq.le.trans hqa.le)) (hr (ψ i)).le)
  exact hmono.trans (hh.trans (mul_le_mul_of_nonneg_left hinside (by positivity)))

end CubicTorus.MovingCenter

end
end

end

end OAI
