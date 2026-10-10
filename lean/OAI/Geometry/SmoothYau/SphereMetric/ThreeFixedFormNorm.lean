import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ContinuousFamilyEventuallyTest
import OAI.Geometry.SmoothYau.Geometry.ChartPairRankTransfer
import OAI.Geometry.SmoothYau.Geometry.ChartTensorNeighborhoodInst1
import OAI.Geometry.SmoothYau.Geometry.FixedMetricDiagonal
import OAI.Geometry.SmoothYau.Smoothness.CompactSmoothJetMap
import OAI.Geometry.SmoothYau.Spectrum.PinnedMetricContinuousSmoothFamily
import OAI.Geometry.SmoothYau.SphereMetric.ThreeCutoffControlBounds

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
local instance : MeasurableSpace ThreeManifold := borel ThreeManifold
local instance : BorelSpace ThreeManifold := ⟨rfl⟩
lemma threeManifold_preconnected : PreconnectedSpace ThreeManifold := by
  let : PreconnectedSpace (Sphere 2) := Subtype.preconnectedSpace
    (isPreconnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [Euclidean,finrank_euclideanSpace]) (0:Euclidean 3) 1)
  let : PreconnectedSpace Circle := inferInstance
  infer_instance
lemma three_rank_separating_tensor
    (μ : Measure ThreeManifold) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric ThreeModel ThreeManifold) {u v : ThreeManifold → ℝ}
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
    {Λ : ℝ} (hΛ : 0<Λ) (hue : ∀ p, -laplaceBeltrami g u p=Λ*u p)
    (hve : ∀ p, -laplaceBeltrami g v p=Λ*v p)
    {S : Set ThreeManifold} (hS : IsOpen S)
    (hG : ∀ p∈S, 0<coordinateGradientPair g u u p)
    (hrank : ∃ x : ThreeModel, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (hv0 : v≠0) (ho : ∫ x, v x*u x ∂μ=0) :
    ∃ χ : ThreeManifold → ℝ, tsupport χ⊆S ∧
      ContMDiff 𝓘(ℝ,ThreeModel) (𝓘(ℝ,ThreeModel).prod 𝓘(ℝ,ThreeModel →L[ℝ] ThreeModel)) ∞
        (fun y => TotalSpace.mk' (ThreeModel →L[ℝ] ThreeModel) y (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,ThreeModel) y)
        (supportedPinningTensor g u v χ y).toLinearMap=0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y)=0) ∧
      0<∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  have hn (p : ThreeManifold) (hp : p∈S) : metricGradient g u p≠0 := by
    have he := metricGradient_ne_zero_of_chart g hu p
      ((chartAt ThreeModel p).map_source (mem_chart_source ThreeModel p))
      (by intro hz; have hh := hG p hp; simp [coordinateGradientPair,hz] at hh)
    change (fun q : ThreeManifold => metricGradient g u q≠0) ((chartAt ThreeModel p).symm (chartAt ThreeModel p p)) at he
    rw [(chartAt ThreeModel p).left_inv (mem_chart_source ThreeModel p)] at he
    exact he
  suffices hex : ∃ p∈S, bundleTransverse g u p (metricGradient g v p)≠0 by
    obtain ⟨p,hp,ht⟩ := hex
    exact exists_supported_separating_tensor μ g hu hv hS hn hp ht threeModel_finrank
  by_contra hnone
  have hzero (p : ThreeManifold) (hp : p∈S) : bundleTransverse g u p (metricGradient g v p)=0 := by
    by_contra hh
    exact hnone ⟨p,hp,hh⟩
  apply hv0
  apply proportional_orthogonal_zero μ hv.continuous _ ho
  let chart := chartAt ThreeModel threeProfileCenter
  let O := chart.symm ⁻¹' S
  have hO : IsOpen O := hS.preimage (three_chart_symm_continuous threeProfileCenter)
  obtain ⟨x,hx,hr⟩ := hrank
  have hOt : O⊆chart.target := by rw [three_chart_target]; exact subset_univ _
  have hdu : fderiv ℝ (u ∘ chart.symm) x≠0 := by
    intro hz
    have hp := hG _ hx
    rw [←localGradientPair_eq_global hu g threeProfileCenter (hOt hx)] at hp
    change fderiv ℝ (u ∘ (chartAt ThreeModel threeProfileCenter).symm) x=0 at hz
    simp [localGradientPair,hz] at hp
  have hpair : ContDiffAt ℝ 1 (fun y => (u (chart.symm y),coordinateGradientPair g u u (chart.symm y))) x :=
    ((contDiffAt_inChart hu threeProfileCenter (hOt hx)).prodMk
      (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) threeProfileCenter (hOt hx))).of_le
      (by simp)
  obtain ⟨c,hc⟩ := local_eigen_proportional_of_gradient_rank g threeProfileCenter hO hx hOt
    (hu.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (hv.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hdu
    (fun y hy => transverse_zero_chart_kernel g hu hv threeProfileCenter (hOt hy) (hzero _ hy))
    hpair hr (hG _ hx) hΛ (fun y _ => by linarith [hue (chart.symm y)])
    (fun y _ => by linarith [hve (chart.symm y)]) (fun _ _ => rfl)
  let := threeManifold_preconnected
  exact ⟨c,proportional_eigen_global g hu hv Λ c hue hve ⟨chart.symm x,hc⟩⟩
end


section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
local instance : MeasurableSpace ThreeManifold := borel ThreeManifold
local instance : BorelSpace ThreeManifold := ⟨rfl⟩
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

theorem three_nondegenerate_pinning_tensor
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0<coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    (σ : W →ₗ[ℝ] RealSmoothFunctions ThreeModel ThreeManifold)
    (hσ : Injective σ)
    (hσe : ∀ w p, -laplaceBeltrami g (σ w) p = Λ*σ w p)
    (hσo : ∀ w, I.mean g (fun x => σ w x*u x) = 0) :
    ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      (restrictedPinningPencil I g σ K).Nondegenerate := by
  let := threeManifold_preconnected
  apply symmetric_forms_nondegenerate (restrictedPinningPencil I g σ)
  · intro K v w
    exact pinningEnergyPencil_symmetric I g K (σ v) (σ w)
  · intro w hw
    have hv : (σ w : ThreeManifold → ℝ) ≠ 0 := by
      intro hz
      apply hw
      apply hσ
      rw [map_zero]
      exact DFunLike.ext _ _ (congrFun hz)
    have ho : ∫ x, σ w x*u x ∂I.volumeMeasure g = 0 := by
      exact (I.mean_eq_volumeIntegral g (fun x => σ w x*u x)
        ((σ w).contMDiff.continuous.mul u.contMDiff.continuous)).symm.trans (hσo w)
    obtain ⟨χ,hχ,hK,htr,hku,hpos⟩ := three_rank_separating_tensor
      (I.volumeMeasure g) g u.contMDiff (σ w).contMDiff hΛ hue (hσe w) hS hG hrank hv ho
    let K : pinningTensorSpace g (u : ThreeManifold → ℝ)
        S :=
      ⟨supportedPinningTensor g u (σ w) χ,
        hK, supportedPinningTensor_selfAdjoint g u (σ w) χ,htr,hku,by
          intro x hx
          apply supportedPinningTensor_zero
          by_contra hn
          exact hx (hχ (subset_tsupport _ hn))⟩
    refine ⟨K,ne_of_gt ?_⟩
    change 0 < I.mean g (fun x => g.inner x (metricGradient g (σ w) x)
      (supportedPinningTensor g u (σ w) χ x (metricGradient g (σ w) x)))
    rw [I.mean_eq_volumeIntegral g _
      (contMDiff_tensorEnergy g _ hK (σ w).contMDiff (σ w).contMDiff).continuous]
    exact hpos

theorem exists_three_simple_pinned_family
    (I : MetricIntegralAtlas (E := ThreeModel) (M := ThreeManifold))
    (g : SmoothMetric ThreeModel ThreeManifold)
    {Λ : ℝ} (hΛ : 0<Λ) {S : Set ThreeManifold} (hS : IsOpen S)
    (u : RealSmoothFunctions ThreeModel ThreeManifold)
    (hu0 : (u : ThreeManifold → ℝ) ≠ 0)
    (hue : ∀ p, -laplaceBeltrami g u p = Λ*u p)
    (hG : ∀ p∈S, 0<coordinateGradientPair g u u p)
    (hrank : ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈S ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x))
    : ∃ K : pinningTensorSpace g (u : ThreeManifold → ℝ)
      S,
      ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : ThreeManifold → ℝ,
        ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
        (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
          Λ*v x) → ∃ c : ℝ, v = fun x => c*u x := by
  classical
  have hs : Module.finrank ℝ ThreeModel < 2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let A := (nonempty_compactMetricAtlas g 2 hs).some
  let B : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold B
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  let lam : ℝ := Λ
  have hla : 0 < lam := hΛ
  have hαl : α+lam ≠ 0 := ne_of_gt (add_pos hα0 hla)
  let μ : ℝ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hαl
  have hlam : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let T := A.realSpectralResolvent B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
  let uz := A.realOfSmooth (2*(2:ℝ)) hs u u.contMDiff
  let P := A.intrinsicPairing I (2*(2:ℝ)) hs
  let W := Module.End.eigenspace T.toLinearMap μ ⊓ (P.form uz).ker
  let : FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) :=
    compact_eigenspace_finite T (A.realSpectralResolvent_compact B α hα0 (hα α le_rfl).1 (hα α le_rfl).2) hμ
  let : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le
    (show W ≤ Module.End.eigenspace T.toLinearMap μ from inf_le_left)
  have heigen (w : W) : T w = μ • (w : A.realH (2*(2:ℝ))) :=
    Module.End.mem_eigenspace_iff.mp w.property.1
  have hf (w : W) : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(2:ℝ)) w) :=
    (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).1
  let σ := A.realSmoothRepresentativeLM (2*(2:ℝ)) W hf
  have hσe (w : W) (x : ThreeManifold) : -laplaceBeltrami g (σ w) x = lam*σ w x := by
    have hh := (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).2 x
    change -laplaceBeltrami g (A.realValue (2*(2:ℝ)) w) x = lam*A.realValue (2*(2:ℝ)) w x
    convert hh using 1
    simp only [hlam,Nat.cast_ofNat]
  have hp (z : A.realH (2*(2:ℝ))) : P.form uz z =
      I.mean g (fun x => u x*A.realValue (2*(2:ℝ)) z x) := by
    change I.mean g (fun x => A.realValue (2*(2:ℝ)) uz x*A.realValue (2*(2:ℝ)) z x) = _
    congr 1
    funext x
    rw [A.realOfSmooth_value]
  have hσo (w : W) : I.mean g (fun x => σ w x*u x) = 0 := by
    have hw : P.form uz w = 0 := w.property.2
    rw [hp] at hw
    convert hw using 2
    funext x
    exact mul_comm _ _
  obtain ⟨K,hK⟩ := three_nondegenerate_pinning_tensor I g hΛ hS u hue hG hrank σ
    (A.realSmoothRepresentativeLM_injective (2*(2:ℝ)) hs W hf) hσe hσo
  refine ⟨K,A.actual_pinned_eventually_simple I B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
    lam hαl u u.contMDiff hu0 hue K ?_⟩
  intro z hz hzo hzz
  have hzW : z ∈ W := ⟨Module.End.mem_eigenspace_iff.mpr hz,(hp z).trans hzo⟩
  let w : W := ⟨z,hzW⟩
  have hw : w = 0 := hK.1 w (fun v => by
    change I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(2:ℝ)) z) x)
      (K.val x (metricGradient g (A.realValue (2*(2:ℝ)) v) x))) = 0
    exact hzz v (heigen v) ((hp v).symm.trans v.property.2))
  exact congrArg Subtype.val hw
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
local instance threeAmbientFormNorm : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeAmbientFormSpace : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
def threeTensorSupport (R : ℝ) : Compacts ThreeModel :=
  ⟨threeNormalEquiv '' closedBall 0 (R/2), (isCompact_closedBall _ _).image threeNormalEquiv.continuous⟩
abbrev ThreeTensor (R : ℝ) := 𝓓_{threeTensorSupport R}(ThreeModel,MetricForm ThreeModel)
def ThreeExterior (g : SmoothMetric ThreeModel ThreeManifold) (r : ℝ) : Prop :=
  ∀ q∉threeNormalInv '' closedBall 0 r, g.inner q=threeBackgroundMetric.inner q
lemma threeTensorSupport_image (R : ℝ) :
    (chartAt ThreeModel threeProfileCenter).symm '' (threeTensorSupport R : Set ThreeModel)=
      threeNormalInv '' closedBall 0 (R/2) := by
  change (chartAt ThreeModel threeProfileCenter).symm '' (threeNormalEquiv '' closedBall 0 (R/2))=_
  rw [←image_comp]
  rfl
lemma ThreeExterior.mono {g : SmoothMetric ThreeModel ThreeManifold} {r s : ℝ}
    (he : ThreeExterior g r) (hrs : r ≤ s) : ThreeExterior g s := by
  intro q hq
  exact he q (fun hh => hq (image_mono (closedBall_subset_closedBall hrs) hh))
lemma threeExterior_support {g : SmoothMetric ThreeModel ThreeManifold} {R r : ℝ}
    (hr : r≤R/2) (he : ThreeExterior g r) :
    ∀ q∉(chartAt ThreeModel threeProfileCenter).symm '' (threeTensorSupport R : Set ThreeModel),
      g.inner q=threeBackgroundMetric.inner q := by
  rw [threeTensorSupport_image]
  exact he.mono hr
def threeTensorOf (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) : ThreeTensor R :=
  chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threeTensorOf_zero (R : ℝ) : threeTensorOf R threeBackgroundMetric (fun _ _ => rfl)=0 := by
  apply DFunLike.ext
  intro y
  change chartMetricForm threeBackgroundMetric threeProfileCenter y-chartMetricForm threeBackgroundMetric threeProfileCenter y=0
  exact sub_self _
def threePositiveSet (R : ℝ) : Set (ThreeTensor R) :=
  {H | chartTensorPositive threeBackgroundMetric threeProfileCenter (threeTensorSupport R) H}
abbrev ThreePositiveTensor (R : ℝ) := threePositiveSet R
def threeTensorMetric (R : ℝ) (H : ThreePositiveTensor R) : SmoothMetric ThreeModel ThreeManifold :=
  chartTensorMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _) H.val H.property
lemma threePositiveSet_isOpen (R : ℝ) : IsOpen (threePositiveSet R) :=
  isOpen_chartTensorPositive threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _)
lemma threeTensorOf_positive (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) : threeTensorOf R g he∈threePositiveSet R :=
  chartTensorOfMetric_positive threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threeTensorMetric_of (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold)
    (he : ThreeExterior g (R/2)) :
    threeTensorMetric R ⟨threeTensorOf R g he,threeTensorOf_positive R g he⟩=g :=
  chartTensorMetric_ofMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    (three_chart_target threeProfileCenter) g (threeExterior_support le_rfl he)
lemma threePositive_zero (R : ℝ) : (0:ThreeTensor R)∈threePositiveSet R := by
  simpa only [threeTensorOf_zero] using threeTensorOf_positive R threeBackgroundMetric (fun _ _ => rfl)
lemma threeTensorMetric_zero (R : ℝ) : threeTensorMetric R ⟨0,threePositive_zero R⟩=threeBackgroundMetric := by
  simpa only [threeTensorOf_zero] using threeTensorMetric_of R threeBackgroundMetric (fun _ _ => rfl)
lemma threeTensorMetric_family (R : ℝ) (r : ThreeManifold) (i j : CoordIndex ThreeModel) :
    ContinuousSmoothFamilyOn (fun H y => metricCoefficients (threeTensorMetric R H) r y i j)
      (chartAt ThreeModel r).target :=
  family_chartTensorMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
    ((three_chart_target threeProfileCenter).symm ▸ subset_univ _) Subtype.val
    (fun H => H.property) continuous_subtype_val r i j
lemma exists_three_open_model (R : ℝ) (N : Set (SmoothMetric ThreeModel ThreeManifold))
    (hN : IsSmoothNeighborhood threeBackgroundMetric N) :
    ∃ O : Set (ThreeTensor R), IsOpen O ∧ 0∈O ∧
      ∀ H∈O, ∃ hp : H∈threePositiveSet R, threeTensorMetric R ⟨H,hp⟩∈N := by
  let z₀ : ThreePositiveTensor R := ⟨0,threePositive_zero R⟩
  have htest : IsSmoothNeighborhood (threeTensorMetric R z₀) N := by
    rw [show threeTensorMetric R z₀=threeBackgroundMetric from threeTensorMetric_zero R]
    exact hN
  have hev := continuousFamily_eventually_neighborhood (threeTensorMetric R)
    (threeTensorMetric_family R) z₀ htest
  obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
  refine ⟨Subtype.val '' V,(threePositiveSet_isOpen R).isOpenMap_subtype_val V hVo,
    ⟨z₀,hzV,rfl⟩,?_⟩
  rintro H ⟨z,hz,rfl⟩
  exact ⟨z.property,hV hz⟩
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance threePinFormNorm : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threePinFormSpace : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
def ThreeRegular (u : ThreeManifold → ℝ) : Prop :=
  ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0
def ThreeSimple (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ) (lam : ℝ) : Prop :=
  ∀ v, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
    (∀ x, -laplaceBeltrami g v x=lam*v x) → ∃ c : ℝ, v=fun x => c*u x
def threeCollar (b c : ℝ) : Set ThreeManifold :=
  (threeNormalInv '' ball 0 c) \ (threeNormalInv '' closedBall 0 b)
lemma threeCollar_isOpen (b c : ℝ) : IsOpen (threeCollar b c) :=
  (threeNormalInv_isOpenMap _ isOpen_ball).sdiff (threeNormalInv_closedBall_closed b)
lemma threeCollar_nonempty {b c : ℝ} (hb : 0<b) (hbc : b<c) : (threeCollar b c).Nonempty := by
  obtain ⟨y,hy⟩ := exists_norm_eq NormalWaveSpace (show 0 ≤ (b+c)/2 by linarith)
  refine ⟨threeNormalInv y,?_,?_⟩
  · rw [threeNormalInv_mem_ball_iff,hy]; linarith
  · rw [threeNormalInv_mem_closedBall_iff,hy]; linarith
lemma three_exterior_profile_pair
    (g : SmoothMetric ThreeModel ThreeManifold) {b : ℝ} (he : ThreeExterior g b)
    (k : ℕ) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q)
    {q : ThreeManifold} (hq : q∉threeNormalInv '' closedBall 0 b) :
    coordinateGradientPair g u u q=coordinateGradientPair threeBackgroundMetric
      (threeCoupled threeCouplingRadius k) (threeCoupled threeCouplingRadius k) q := by
  have hgerm : u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
    filter_upwards [(threeNormalInv_closedBall_closed b).isOpen_compl.mem_nhds hq] with z hz
    exact hu z hz
  rw [coordinateGradientPair_congr_nhds g hgerm]
  exact coordinateGradientPair_metric_point_eq g threeBackgroundMetric q
    (fun v w => congrArg (fun T => T v w) (he q hq)) _ _
lemma three_clean_collar_gradient
    (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
    (hclean : ThreeCleanBall R) (hc : c<R/2) (he : ThreeExterior g b)
    (k : ℕ) (hk : 1 ≤ k) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius k q) :
    ∀ q∈threeCollar b c, 0<coordinateGradientPair g u u q := by
  intro q hq
  obtain ⟨y,hy,rfl⟩ := hq.1
  obtain ⟨hl,hr⟩ := hclean y (closedBall_subset_closedBall (by linarith : c ≤ R) (ball_subset_closedBall hy))
  rw [three_exterior_profile_pair g he k u hu hq.2]
  apply lt_of_lt_of_le _ (threeCoupled_clean_gradient_lower k hk _ hl hr)
  have hp : (0:ℝ)<‖productA (threeNormalInv y).1‖ := by linarith
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  positivity
lemma three_collar_rank
    (g : SmoothMetric ThreeModel ThreeManifold) {b c : ℝ} (hb : 0<b) (hbc : b<c)
    (he : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m) (u : ThreeManifold → ℝ)
    (hu : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q) :
    ∃ x, (chartAt ThreeModel threeProfileCenter).symm x∈threeCollar b c ∧
      Function.Surjective (fderiv ℝ (fun y => (u ((chartAt ThreeModel threeProfileCenter).symm y),
        coordinateGradientPair g u u ((chartAt ThreeModel threeProfileCenter).symm y))) x) := by
  let ψ := (chartAt ThreeModel threeProfileCenter).symm
  let O := ψ ⁻¹' threeCollar b c
  have hO : IsOpen O := (threeCollar_isOpen b c).preimage (three_chart_symm_continuous _)
  have hne : O.Nonempty := by
    obtain ⟨q,hq⟩ := threeCollar_nonempty hb hbc
    obtain ⟨y,hy,heq⟩ := hq.1
    exact ⟨threeNormalEquiv y,by simpa only [O,ψ,mem_preimage,←heq,threeNormalInv,Function.comp_apply] using hq⟩
  obtain ⟨x,hx,hrank⟩ := threeCoupled_profile_rank_dense hm hO hne
  refine ⟨x,hx,?_⟩
  have hgerm : (fun y => (u (ψ y),coordinateGradientPair g u u (ψ y))) =ᶠ[𝓝 x]
      (fun y => (threeCoupled threeCouplingRadius (4*m+1) (ψ y),
        coordinateGradientPair threeBackgroundMetric (threeCoupled threeCouplingRadius (4*m+1))
          (threeCoupled threeCouplingRadius (4*m+1)) (ψ y))) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact Prod.ext (hu _ hy.2) (three_exterior_profile_pair g he _ u hu hy.2)
  rw [hgerm.fderiv_eq]
  exact hrank

theorem three_pin_near
    (g : SmoothMetric ThreeModel ThreeManifold) {R b c : ℝ} (hR : 0<R)
    (hclean : ThreeCleanBall R) (hb0 : 0<b) (hbc : b<c) (hc : c<R/2)
    (hext : ThreeExterior g b) {m : ℕ} (hm : 1 ≤ m)
    (u : ThreeManifold → ℝ) (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ q, -laplaceBeltrami g u q=productFrequency (4*m+1)*u q)
    (hout : ∀ q∉threeNormalInv '' closedBall 0 b, u q=threeCoupled threeCouplingRadius (4*m+1) q)
    (U : Set (ThreeTensor R)) (hU : IsOpen U)
    (hgU : threeTensorOf R g (hext.mono (hbc.trans hc).le) ∈ U) :
    ∃ h : SmoothMetric ThreeModel ThreeManifold, ∃ he : ThreeExterior h c,
      threeTensorOf R h (he.mono hc.le) ∈ U ∧
      (∀ q, -laplaceBeltrami h u q=productFrequency (4*m+1)*u q) ∧
      ThreeSimple h u (productFrequency (4*m+1)) := by
  classical
  let I := (nonempty_metricIntegralAtlas (E:=ThreeModel) (M:=ThreeManifold)).some
  have hΛ : 0<productFrequency (4*m+1) := by unfold productFrequency; positivity
  obtain ⟨K,hKsimple⟩ := exists_three_simple_pinned_family I g hΛ (threeCollar_isOpen b c)
    ⟨u,hu⟩ hu0 hue (three_clean_collar_gradient g hR hclean hc hext _ (by omega) u hout)
    (three_collar_rank g hb0 hbc hext hm u hout)
  let qp (z : ℝ) := pinnedMetric g K.val K.property.1 z
  have heqp (z : ℝ) : ThreeExterior (qp z) c := by
    intro q hq
    have hn : q∉threeCollar b c := fun hh => hq (image_mono ball_subset_closedBall hh.1)
    exact (pinnedMetric_exterior g K z q hn).trans
      (hext q (fun hh => hq (image_mono (closedBall_subset_closedBall hbc.le) hh)))
  let eqp (z : ℝ) := threeExterior_support hc.le (heqp z)
  have hcont : Continuous (fun z => chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
      (three_chart_target threeProfileCenter) (qp z) (eqp z)) := by
    apply continuous_chartTensorOfMetric
    intro i j
    simpa only [three_chart_target] using pinnedMetric_continuousSmoothFamily g K threeProfileCenter i j
  have hzero : qp 0=g := pinnedMetric_at_zero g K.val K.property.1
  have hmem : ∀ᶠ z in 𝓝 (0:ℝ), chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
      (three_chart_target threeProfileCenter) (qp z) (eqp z)∈U :=
    hcont.continuousAt.eventually (hU.mem_nhds (by simpa only [hzero,threeTensorOf] using hgU))
  obtain ⟨z,hzU,hzs⟩ := ((hmem.filter_mono nhdsWithin_le_nhds).and hKsimple).exists
  exact ⟨qp z,heqp z,hzU,pinnedMetric_preserves_eigenfunction g K hu hue z,hzs⟩
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
def ThreeSignAbove (R : ℝ) (u : ThreeManifold → ℝ) (L : ℝ) : Prop :=
  ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆Metric.closedBall 0 (R/2) ∧
  ∃ partition : TaggedPrepartition I, partition.IsPartition ∧
    ∃ d : {J : Box (Fin 3) // J ∈ partition.boxes} → ℝ, (∀ j, 0 < d j) ∧
      ENNReal.ofReal L < SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv)
def ThreeLargeWitness (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold) (A B : ℝ) : Prop :=
  ∃ k : ℕ, 3  ≤  k ∧ ∃ e : ℝ, ∃ u : ThreeManifold → ℝ,
    B < e ∧ e < 4*(k:ℝ)^2 ∧ ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      (∀ x, -laplaceBeltrami g u x=e*u x) ∧ ThreeRegular u ∧ ThreeSignAbove R u (A*(k:ℝ))
lemma three_largeWitness_eventually (R : ℝ) {P : Type*} [TopologicalSpace P]
    (q : P → SmoothMetric ThreeModel ThreeManifold)
    (hq : ∀ r i j, ContinuousSmoothFamilyOn (fun a y => metricCoefficients (q a) r y i j)
      (chartAt ThreeModel r).target) (a₀ : P) (k : ℕ) (hk : 3 ≤ k)
    (e : ℝ) (he : 0<e) (u : ThreeManifold → ℝ)
    (hu : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u≠0)
    (hue : ∀ x, -laplaceBeltrami (q a₀) u x=e*u x)
    (hreg : ThreeRegular u) (hsimple : ThreeSimple (q a₀) u e)
    (A B : ℝ) (hB : B<e) (hD : e<4*(k:ℝ)^2) (hscore : ThreeSignAbove R u (A*(k:ℝ))) :
    ∀ᶠ a in 𝓝 a₀, ThreeLargeWitness R (q a) A B := by
  classical
  obtain ⟨I,hI,partition,hpart,d,hd,hscore⟩ := hscore
  have hev := three_simple_eigenpair_open q hq a₀ e he u hu hu0 hue hsimple hreg
    (fun j : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo j.val) d
    (threeNormalInv ∘ normalWaveEquiv)
    (threeNormalInv_continuous.comp normalWaveEquiv.continuous)
    (ENNReal.ofReal (A*(k:ℝ))) hscore hB hD
  filter_upwards [hev] with a ha
  obtain ⟨e,v,heb,hed,hv,hv0,hve,hvr,hvl⟩ := ha
  exact ⟨k,hk,e,v,heb,hed,hv,hv0,hve,hvr,I,hI,partition,hpart,d,hd,hvl⟩
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance threeStageFormNorm : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeStageFormSpace : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
lemma three_regular_nonzero (u : ThreeManifold → ℝ) (hreg : ThreeRegular u) : u≠0 := by
  intro hu
  have hh := hreg threeProfileCenter (by rw [hu]; rfl)
  apply hh
  simp only [hu,Function.comp_def,Pi.zero_apply]
  exact fderiv_const_apply 0

theorem exists_three_simple_stage :
    ∃ R : ℝ, 0<R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ r : ℝ, 0<r → ∀ hrR : r<R/2, (hext : ThreeExterior g r) →
      ∀ A : ℝ, 0 ≤ A → ∀ M : ℕ, ∀ U : Set (ThreeTensor R), IsOpen U →
      threeTensorOf R g (hext.mono hrR.le)∈U →
      ∃ k : ℕ, M ≤ k ∧ 3 ≤ k ∧ ∃ h : SmoothMetric ThreeModel ThreeManifold,
      ∃ c : ℝ, 0<c ∧ ∃ hcR : c<R/2, ∃ he : ThreeExterior h c,
      threeTensorOf R h (he.mono hcR.le)∈U ∧
      ∃ u : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u≠0 ∧
        (∀ q, -laplaceBeltrami h u q=productFrequency k*u q) ∧
        ThreeRegular u ∧ ThreeSimple h u (productFrequency k) ∧ ThreeSignAbove R u (A*(k:ℝ)) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hstage⟩ := exists_three_exact_stage
  refine ⟨R,hR,N,hN,h0N,?_⟩
  intro g hg r hr hrR hext A hA M U hU hgU
  let a := (2*r+R/2)/3
  let b := (r+2*(R/2))/3
  have hra : r<a := by dsimp [a]; linarith
  have hab : a<b := by dsimp [a,b]; linarith
  have hbR : b<R/2 := by dsimp [b]; linarith
  let eg := threeExterior_support hrR.le hext
  let V : Set (SmoothMetric ThreeModel ThreeManifold) := {h | ∀ eh,
    chartTensorOfMetric threeBackgroundMetric threeProfileCenter (threeTensorSupport R)
      (three_chart_target threeProfileCenter) h eh∈U}
  have hV : IsSmoothNeighborhood g V := chartTensorRepresentation_neighborhood threeBackgroundMetric
    threeProfileCenter (threeTensorSupport R) (three_chart_target threeProfileCenter) g eg U (hU.mem_nhds hgU)
  obtain ⟨e,hbe,heR,I,hIa,partition,hpart,ell,hell,ε,hε,hpacket⟩ :=
    hstage g hg a b (hr.trans hra) hab hbR (threeNormalInv '' closedBall 0 r)
      (threeNormalInv_closedBall_closed r) (image_mono (closedBall_subset_closedBall hra.le))
      (fun q hq v w => congrArg (fun T => T v w) (hext q hq)) A V hV
  have ht : Tendsto (fun m : ℕ => 4*m+1) atTop atTop :=
    tendsto_atTop_mono (fun m => show m ≤ 4*m+1 by omega) tendsto_id
  obtain ⟨m,⟨hm,hmM⟩,hm1⟩ := ((ht.eventually hpacket).and (eventually_ge_atTop M) |>.and (eventually_ge_atTop 1)).exists
  obtain ⟨ĝ,hĝN,u,hu,hue,hreg,hout,hscore⟩ := hm
  have heĝ : ThreeExterior ĝ e := by
    intro q hq
    ext v w
    exact ((hout q hq).1 v w).trans (congrArg (fun T => T v w)
      (hext q (fun hh => hq (image_mono (closedBall_subset_closedBall (hra.trans (hab.trans hbe)).le) hh))))
  let eĝ := threeExterior_support heR.le heĝ
  have hĝU := hĝN eĝ
  have hu0 : u≠0 := three_regular_nonzero u hreg
  let c := (e+R/2)/2
  have hec : e<c := by dsimp [c]; linarith
  have hcR : c<R/2 := by dsimp [c]; linarith
  obtain ⟨h,he,hhU,hhe,hsimple⟩ := three_pin_near ĝ hR hclean (hr.trans (hra.trans (hab.trans hbe)))
    hec hcR heĝ hm1 u hu hu0 hue (fun q hq => (hout q hq).2) U hU hĝU
  refine ⟨4*m+1,by omega,by omega,h,c,hr.trans (hra.trans (hab.trans (hbe.trans hec))),hcR,he,hhU,
    u,hu,hu0,hhe,hreg,hsimple,I,hIa.trans (closedBall_subset_closedBall (hab.trans hbR).le),
    partition,hpart,(fun j => ε/(productWaveFrequency (4*m+1)*ell j.val)),?_,?_⟩
  · intro j
    exact div_pos hε (mul_pos (lt_of_lt_of_le (by positivity : (0:ℝ)<(4*m+1:ℕ))
      (productWaveFrequency_bounds (k:=4*m+1) (by omega)).1) (hell j.val j.property))
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (productWaveFrequency_bounds (k:=4*m+1) (by omega)).1 hA)).trans_lt hscore
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
local instance threeFixedFormNorm : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeFixedFormSpace : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeFixedContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeFixedFormComplete : CompleteSpace (MetricForm ThreeModel) := by
  let : CompleteSpace (ThreeModel →L[ℝ] ℝ) := ContinuousLinearMap.instCompleteSpace
  exact ContinuousLinearMap.instCompleteSpace

theorem exists_three_fixed_witnesses :
    ∃ R : ℝ, 0<R ∧ ∃ g : SmoothMetric ThreeModel ThreeManifold,
      ∀ n : ℕ, ThreeLargeWitness R g ((n:ℝ)+1) ((n:ℝ)+1) := by
  classical
  obtain ⟨R,hR,N,hN,h0N,hstage⟩ := exists_three_simple_stage
  let : MetricSpace (ThreeTensor R) := compactSmoothMetricSpace (threeTensorSupport R)
  let : CompleteSpace (ThreeTensor R) := compactSmooth_complete (threeTensorSupport R)
  obtain ⟨O,hO,h0O,hON⟩ := exists_three_open_model R N hN
  let P : ℕ → Set (ThreeTensor R) := fun _ =>
    {H | ∃ g : SmoothMetric ThreeModel ThreeManifold, ∃ r : ℝ, 0<r ∧ ∃ hrR : r<R/2,
      ∃ he : ThreeExterior g r, H=threeTensorOf R g (he.mono hrR.le) ∧ H∈O}
  let W : ℕ → Set (ThreeTensor R) := fun n =>
    {H | ∃ hp : H∈threePositiveSet R,
      ThreeLargeWitness R (threeTensorMetric R ⟨H,hp⟩) ((n:ℝ)+1) ((n:ℝ)+1)}
  have hstep : ∀ n, ∀ H∈P n, ∀ U : Set (ThreeTensor R), IsOpen U → H∈U →
      ∃ K∈P (n+1), K∈U ∧ ∃ V : Set (ThreeTensor R), IsOpen V ∧ K∈V ∧ V⊆W n := by
    intro n H hH U hU hHU
    obtain ⟨g,r,hr,hrR,he,rfl,hgO⟩ := hH
    let e := he.mono hrR.le
    obtain ⟨hp,hgN⟩ := hON _ hgO
    have hmetric : threeTensorMetric R ⟨threeTensorOf R g e,hp⟩=g := threeTensorMetric_of R g e
    rw [hmetric] at hgN
    obtain ⟨k,hkM,hk3,h,c,hc,hcR,eh,hhU,u,hu,hu0,hue,hreg,hsimple,hscore⟩ :=
      hstage g hgN r hr hrR he ((n:ℝ)+1) (by positivity) (n+3)
        (U∩O) (hU.inter hO) ⟨hHU,hgO⟩
    let eh' := eh.mono hcR.le
    let K := threeTensorOf R h eh'
    let z : ThreePositiveTensor R := ⟨K,threeTensorOf_positive R h eh'⟩
    have hqz : threeTensorMetric R z=h := threeTensorMetric_of R h eh'
    have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hkreal : (n:ℝ)+3 ≤ k := by exact_mod_cast hkM
    have hk3real : (3:ℝ) ≤ k := by exact_mod_cast hk3
    have hepos : 0<productFrequency k := by dsimp [productFrequency]; positivity
    have heB : (n:ℝ)+1<productFrequency k := by dsimp [productFrequency]; nlinarith
    have heD : productFrequency k<4*(k:ℝ)^2 := by dsimp [productFrequency]; nlinarith
    have hev := three_largeWitness_eventually R (threeTensorMetric R)
      (threeTensorMetric_family R) z k hk3 (productFrequency k) hepos u hu hu0
      (by simpa only [hqz] using hue) hreg (by simpa only [hqz] using hsimple)
      ((n:ℝ)+1) ((n:ℝ)+1) heB heD hscore
    obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hev
    refine ⟨K,⟨h,c,hc,hcR,eh,rfl,hhU.2⟩,hhU.1,Subtype.val '' V,
      (threePositiveSet_isOpen R).isOpenMap_subtype_val V hVo,⟨z,hzV,rfl⟩,?_⟩
    rintro H ⟨v,hv,rfl⟩
    exact ⟨v.property,hV hv⟩
  have hzP : (0:ThreeTensor R)∈P 0 := by
    refine ⟨threeBackgroundMetric,R/4,by positivity,by linarith,(fun _ _ => rfl),?_,h0O⟩
    exact (threeTensorOf_zero R).symm
  obtain ⟨H,hHO,hHW⟩ := fixed_metric_diagonal P W hstep 0 hzP hO h0O
  obtain ⟨hp,hgN⟩ := hON H hHO
  refine ⟨R,hR,threeTensorMetric R ⟨H,hp⟩,?_⟩
  intro n
  exact (hHW n).choose_spec

end YauCounterexamples
end

end OAI
