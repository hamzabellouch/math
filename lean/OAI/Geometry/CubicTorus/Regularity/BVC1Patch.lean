import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVMovingTrappedDecay

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_lipschitz_graph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
        0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ g : Cover → ℝ, LipschitzWith ⟨2*ε, by positivity⟩ g ∧
        ∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          g (normalPlaneProjection n₀ x) = ⟪n₀,x⟫ := by
  obtain ⟨R₀,ρ,C,hR₀,hρ,hρs,hC,hiter⟩ := isMinimizerAt_uniform_tilt_iteration hV hE hmin hcenter
  obtain ⟨U,A,hU,hA,hupper⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨D,d,hD,hd,hdensity⟩ := isMinimizerAt_two_sided_density hV hE hmin
  let r₀ := min R₀ (min U (min D (1/8)))
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  refine ⟨r₀,hr₀,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δ₀,hδ₀,hiteration⟩ := hiter μ hμ N hN hp hu
  let K := (131072:ℝ)^2*(4*A)*(2/ρ^2+8*(4*A)*C^2)*4
  let T := (d^2*((ε/2)/8)^6)^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, K*t^2 < T :=
    (show ContinuousAt (fun t : ℝ ↦ K*t^2) 0 by fun_prop).tendsto.eventually
      (Iio_mem_nhds (by simpa using hT))
  obtain ⟨b,hb,hbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min (δ₀/2) (min (ε/(8*C)) (b/2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro c₀ hc₀ n₀ r e hn₀ hr hrr he heδ hratio htilt
  have hrR : r ≤ R₀ := hrr.trans (min_le_left _ _)
  have hrU : r ≤ U := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrD : r ≤ D := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrs : r ≤ 1/8 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heδ₀ : 2*e ≤ δ₀ := by have := heδ.trans (min_le_left _ _); linarith
  have heC : 4*C*e ≤ ε/2 := by
    have hh := heδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0 < 8*C)).mp hh
    nlinarith only [hh']
  have hesmall : K*e^2 < T := by
    apply hbound
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    have := heδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hratio' : (r/2)/(2*e)^2 ≤ δ₀ := by
    have hnn : 0 ≤ r/e^2 := by positivity
    have heq : (r/2)/(2*e)^2 = (r/e^2)/8 := by ring
    rw [heq]
    have hh := hratio.trans ((min_le_left _ _) : δ ≤ δ₀/2)
    linarith
  have hd' : ∀ a ∈ frontier (openRepresentative E), ∀ t : ℝ, 0 < t → t ≤ D →
      d*t^3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      d*t^3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t) := by
    rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact hdensity
  let S := quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)
  apply exists_lipschitz_height_of_cone S hn₀ hε.le hεhalf
  intro x hx y hy
  have hxc : ‖x-c₀‖ < r/128 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx.2
  have hyc : ‖y-c₀‖ < r/128 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy.2
  let a : InteriorCenter := ⟨y,by
    have hh := norm_sub_le_norm_sub_add_norm_sub y c₀ cubeCenter
    linarith⟩
  have ha : quotientMap (a : Cover) ∈ frontier (openRepresentative E) := hy.1
  have hya : dist (quotientMap y) (quotientMap c₀) ≤ r/128 := by
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans hyc.le
  have hsub : Metric.closedBall (quotientMap y) (17*(r/2)) ⊆
      Metric.closedBall (quotientMap c₀) (17*r) := by
    intro z hz
    have hz' : dist z (quotientMap y) ≤ 17*(r/2) := hz
    change dist z (quotientMap c₀) ≤ 17*r
    linarith [dist_triangle z (quotientMap y) (quotientMap c₀)]
  have htilt' : (∫ z in Metric.closedBall (quotientMap (a : Cover)) (17*(r/2)), ‖N z-n₀‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu n₀).integrableOn
    (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE).trans htilt
  have htilt'' : (∫ z in Metric.closedBall (quotientMap (a : Cover)) (17*(r/2)), ‖N z-n₀‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r/2)^2*(2*e)^2 := by
    nlinarith only [htilt']
  obtain ⟨n,ν,hnzero,hn,hν,hnt,ht,hclose⟩ := hiteration a ha n₀ (r/2) (2*e) hn₀
    (by positivity) (by linarith) (by positivity) heδ₀ hratio' htilt''
  have hmass : ∀ s : ℝ, 0 < s → s ≤ r/2 →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall (quotientMap y) s) ≤ (4*A)*s^2 := by
    intro s hs hsr
    have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : s < 2*s))).trans
      (hupper μ hμ (quotientMap y) (2*s) (by positivity) (by linarith))
    nlinarith only [hh]
  have hcone := iterated_tilt_boundary_cone hE hμ hN hp hu hd hd' ha hρ
    (by linarith : ρ < 1) (by positivity : 0 < r/2) (by positivity : 0 ≤ 2*e)
    (by positivity : 0 ≤ 4*A) hC.le n hν hmass ht hclose
    (R := r/64) (ε := ε/2) (by linarith) (by linarith) (by linarith)
    (by positivity) (by linarith) (by dsimp [K,T] at hesmall; nlinarith only [hesmall])
  have hclose0 : ‖n₀-ν‖ ≤ ε/2 := by
    have hh := hclose 0
    rw [hnzero,pow_zero,mul_one] at hh
    exact hh.trans (by nlinarith only [heC])
  have hcone' := cone_change_normal hcone hclose0
  have hxy : ‖x-y‖ < r/64 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub x c₀ y
    rw [norm_sub_rev c₀ y] at hh
    linarith
  have hlift : shortestLift (quotientMap x-quotientMap y) = x-y :=
    shortestLift_eq_of_lift (quotientMap_sub _ _) (by linarith)
  have hdist : dist (quotientMap x) (quotientMap y) = ‖x-y‖ := by
    rw [dist_eq_norm,← norm_shortestLift,hlift]
  have hh := hcone' (quotientMap x) hx.1 (by change dist (quotientMap x) (quotientMap y) ≤ r/64; rw [hdist]; exact hxy.le)
  change |⟪n₀,shortestLift (quotientMap x-quotientMap y)⟫| ≤ (ε/2+ε/2)*dist (quotientMap x) (quotientMap y) at hh
  simpa only [hlift,hdist,add_halves] using hh

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_tilt_oscillation_scale {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r e A q : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hq : 0 < q) (hq17 : q ≤ 17)
    (hm : (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a (q*r)) ≤ A*(q*r)^2)
    (ht : (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2) :
    (normalOscillation (spatialNormalMeasure μ) N a n (q*r))^2 ≤ A*(e^2/q^2) := by
  have ht' := (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _)
    (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hq17 hr.le)).eventuallyLE).trans ht
  have hexc : normalExcess (spatialNormalMeasure μ) N a n (q*r) ≤ e^2/q^2 := by
    dsimp only [normalExcess]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hq hr))).2
    have heq : e^2/q^2*(q*r)^2 = r^2*e^2 := by field_simp
    rw [heq]
    exact ht'
  exact (normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hu hn a
    (mul_pos hq hr) hm).trans (mul_le_mul_of_nonneg_left hexc hA)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneProjection_eq_embedding {n : Cover} (hn : ‖n‖ = 1) (v : Cover) :
    normalPlaneProjection n v = normalPlaneEmbedding n (normalPlaneCoordinates n v) := by
  have hh := normalPlaneCoordinates_reconstruct hn v
  dsimp [normalPlaneProjection]
  exact (eq_sub_iff_add_eq.mpr hh).symm

lemma normalPlaneProjection_add (n v w : Cover) :
    normalPlaneProjection n (v+w) = normalPlaneProjection n v+normalPlaneProjection n w := by
  simp only [normalPlaneProjection,inner_add_right,add_smul]
  abel

lemma exact_graph_of_trapped_height {U : Set Torus} (hU : IsOpen U)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {R r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1/2) (hrR : r/2 ≤ R) (hε : ε < 1/4)
    (htrap : normalCap (quotientMap a) n r (ε*r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε*r) ⊆ U)
    {G : Cover → ℝ} {K : ℝ≥0} (hG : LipschitzWith K G)
    (hheight : ∀ x ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball a R,
      G (normalPlaneProjection n x) = ⟪n,x⟫) :
    ∃ g : Plane → ℝ, LipschitzWith K g ∧
      (∀ y ∈ Metric.ball (0 : Plane) (r/4),
        quotientMap a+quotientMap (normalGraph n g y) ∈ frontier U ∧
        ‖normalGraph n g y‖ < r/2) ∧
      (∀ x ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball a R,
        normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a) := by
  let g : Plane → ℝ := fun y ↦ G (normalPlaneProjection n a+normalPlaneEmbedding n y)-⟪n,a⟫
  have hg : LipschitzWith K g := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hdist : dist (normalPlaneEmbedding n y) (normalPlaneEmbedding n z) = dist y z :=
      (normalPlaneLinearIsometry n).dist_map y z
    simpa only [g,dist_sub_right,dist_add_left,hdist] using
      hG.dist_le_mul (normalPlaneProjection n a+normalPlaneEmbedding n y)
        (normalPlaneProjection n a+normalPlaneEmbedding n z)
  have hrepr : ∀ x ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball a R,
      normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a := by
    intro x hx
    have hproj : normalPlaneProjection n a+
        normalPlaneEmbedding n (normalPlaneCoordinates n (x-a)) = normalPlaneProjection n x := by
      rw [← normalPlaneProjection_eq_embedding hn,normalPlaneProjection_sub]
      abel
    have hval : g (normalPlaneCoordinates n (x-a)) = ⟪n,x-a⟫ := by
      dsimp only [g]
      rw [hproj,hheight x hx,inner_sub_right]
    rw [normalGraph,hval]
    exact normalPlaneCoordinates_reconstruct hn (x-a)
  refine ⟨g,hg,?_,hrepr⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := trapped_boundary_projects_disk hU (quotientMap a) hn hr hrsmall hε htrap hy
  let v := shortestLift (x-quotientMap a)
  have hvq : quotientMap v = x-quotientMap a := quotientMap_shortestLift _
  have hxq : quotientMap (a+v) = x := by
    rw [quotientMap_add,hvq]
    abel
  have hvsmall : ‖v‖ < r/2 := by
    simpa only [v,norm_shortestLift,← dist_eq_norm,Metric.mem_ball] using hx.2
  have hav : a+v ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball a R := by
    refine ⟨by simpa only [mem_preimage,hxq] using hx.1,?_⟩
    change dist (a+v) a < R
    rw [dist_eq_norm,add_sub_cancel_left]
    exact hvsmall.trans_le hrR
  have heq := hrepr (a+v) hav
  rw [add_sub_cancel_left] at heq
  have hyv : normalPlaneCoordinates n v = y := hxy
  rw [hyv] at heq
  refine ⟨?_,by rwa [heq]⟩
  rw [heq,hvq]
  simpa only [add_sub_cancel] using hx.1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_hasFDerivWithinAt_of_flat {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : Set Torus} {S : Set Plane} {a : Torus} {x : Plane} {ν : Cover}
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) ν)
    (htrans : ⟪ν,n⟫ ≠ 0) :
    HasFDerivWithinAt g ((⟪ν,n⟫)⁻¹ •
      (-((innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap))) S x := by
  let L := (innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap
  have hz := hflat.hasFDerivWithinAt_inner_zero (normalGraph_lipschitz hn hg) hS
  have hl : HasFDerivWithinAt (fun y ↦ ⟪ν,normalPlaneEmbedding n y⟫) L S x :=
    L.hasFDerivAt.hasFDerivWithinAt
  have hh := (hz.sub hl).const_mul (⟪ν,n⟫)⁻¹
  simp only [Pi.sub_apply, normalGraph, inner_add_right, inner_smul_right,
    add_sub_cancel_left, zero_sub] at hh
  have heq : (fun y : Plane ↦ (⟪ν,n⟫)⁻¹ * (g y * ⟪ν,n⟫)) = g := by
    funext y
    field_simp
  rw [heq] at hh
  exact hh

lemma normalGraph_contDiffOn_one_of_continuous_normal {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : Set Torus} {S : Set Plane} (hSopen : IsOpen S) {a : Torus}
    (ν : Plane → Cover) (hν : ContinuousOn ν S)
    (hS : ∀ y ∈ S, a + quotientMap (normalGraph n g y) ∈ B)
    (hflat : ∀ x ∈ S, BoundaryFlatAt B (a + quotientMap (normalGraph n g x)) (ν x))
    (htrans : ∀ x ∈ S, ⟪ν x,n⟫ ≠ 0) :
    ContDiffOn ℝ 1 g S := by
  let D : Plane → Plane →L[ℝ] ℝ := fun x ↦ (⟪ν x,n⟫)⁻¹ •
    (-((innerSL ℝ (ν x)).comp (normalPlaneLinearIsometry n).toContinuousLinearMap))
  have hD : ContinuousOn D S := by
    have hs : ContinuousOn (fun x ↦ (⟪ν x,n⟫)⁻¹) S :=
      (hν.inner continuousOn_const).inv₀ htrans
    have hl : ContinuousOn (fun x ↦ -((innerSL ℝ (ν x)).comp
        (normalPlaneLinearIsometry n).toContinuousLinearMap)) S := by
      exact (((innerSL ℝ).continuous.comp_continuousOn hν).clm_comp continuousOn_const).neg
    exact hs.smul hl

  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hSopen.uniqueDiffOn]
  refine ⟨by simp, D, contDiffOn_zero.mpr hD, ?_⟩
  intro x hx
  exact normalGraph_hasFDerivWithinAt_of_flat hn hg hS (hflat x hx) (htrans x hx)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_C1_graph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 →
        quotientMap c₀ ∈ frontier (openRepresentative E) → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
        0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
        ContDiffOn ℝ 1 g (Metric.ball 0 (r/1024)) ∧
        (∀ y ∈ Metric.ball (0 : Plane) (r/1024),
          quotientMap c₀+quotientMap (normalGraph n₀ g y) ∈ frontier (openRepresentative E) ∧
          ‖normalGraph n₀ g y‖ < r/512) ∧
        (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          normalGraph n₀ g (normalPlaneCoordinates n₀ (x-c₀)) = x-c₀) := by
  obtain ⟨RN,C,hRN,hC,hns⟩ := isMinimizerAt_moving_normal_field hV hE hmin hcenter
  obtain ⟨RG,hRG,hgs⟩ := isMinimizerAt_moving_lipschitz_graph hV hE hmin hcenter
    (by norm_num : (0:ℝ) < 1/8) (by norm_num : (1/8:ℝ) ≤ 1/2)
  obtain ⟨RT,d,hRT,hd,htrap⟩ := isMinimizerAt_quantitative_trapping hV hE hmin
  obtain ⟨U,A,hU,hA,hupper⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  let r₀ := min RN (min RG (min RT (min U (1/8))))
  refine ⟨r₀,by dsimp [r₀]; positivity,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δN,hδN,hnormal⟩ := hns μ hμ N hN hp hu
  obtain ⟨δG,hδG,hgraph⟩ := hgs μ hμ N hN hp hu
  let K := (131072:ℝ)^2*4096*A
  let T := (d^2*((1/8:ℝ)/4)^6)^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, K*t^2 < T :=
    (show ContinuousAt (fun t : ℝ ↦ K*t^2) 0 by fun_prop).tendsto.eventually
      (Iio_mem_nhds (by simpa using hT))
  obtain ⟨b,hb,hbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min δN (min δG (min (1/(2*C)) (b/2)))
  refine ⟨δ,by dsimp [δ]; positivity,?_⟩
  intro c₀ hc₀ hbase n₀ r e hn₀ hr hrr he heδ hratio ht
  have hrN : r ≤ RN := hrr.trans (min_le_left _ _)
  have hrG : r ≤ RG := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrT : r ≤ RT := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrU : r ≤ U := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrs : r ≤ 1/8 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδn : δ ≤ δN := min_le_left _ _
  have hδg : δ ≤ δG := (min_le_right _ _).trans (min_le_left _ _)
  have hCe : C*e ≤ 1/2 := by
    have hh := heδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith only [hh']
  obtain ⟨ν,hνcont,hν⟩ := hnormal c₀ hc₀ n₀ r e hn₀ hr hrN he (heδ.trans hδn) (hratio.trans hδn) ht
  obtain ⟨G,hG,hheight⟩ := hgraph c₀ hc₀ n₀ r e hn₀ hr hrG he (heδ.trans hδg) (hratio.trans hδg) ht
  have hesmall : K*e^2 < T := by
    apply hbound
    rw [Real.dist_eq,sub_zero,abs_of_pos he]
    have hh := heδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have hm : (spatialNormalMeasure μ : Measure Torus).real
      (Metric.closedBall (quotientMap c₀) ((1/32)*r)) ≤ (4*A)*((1/32)*r)^2 := by
    have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : (1/32)*r < (1/16)*r))).trans
      (hupper μ hμ (quotientMap c₀) ((1/16)*r) (by positivity) (by linarith))
    nlinarith only [hh]
  have hos := polar_tilt_oscillation_scale hN hu (quotientMap c₀) hn₀ hr
    (by positivity : 0 ≤ 4*A) (by norm_num : (0:ℝ) < 1/32) (by norm_num : (1/32:ℝ) ≤ 17) hm ht
  have heq : (1/32:ℝ)*r = 8*(r/256) := by ring
  rw [heq] at hos
  have hos' : 131072*normalOscillation (spatialNormalMeasure μ) N (quotientMap c₀) n₀ (8*(r/256)) <
      d^2*((1/8:ℝ)/4)^6 := by
    dsimp [K,T] at hesmall
    norm_num at hos
    have hp : 0 < d^2*((1/8:ℝ)/4)^6 := by positivity
    nlinarith only [hos,hesmall,hp,sq_nonneg
      (131072*normalOscillation (spatialNormalMeasure μ) N (quotientMap c₀) n₀ (8*(r/256)))]
  have hcaps := htrap μ hμ N hN hp hu (quotientMap c₀) hbase n₀ hn₀
    (r/256) (1/8) (by positivity) (by linarith) (by norm_num) (by norm_num) hos'
  obtain ⟨g,hg,hinside,hrepr⟩ := exact_graph_of_trapped_height (isOpen_openRepresentative E)
    c₀ hn₀ (by positivity : 0 < r/256) (by linarith : r/256 < 1/2)
    (by linarith : (r/256)/2 ≤ r/128) (by norm_num : (1/8:ℝ) < 1/4) hcaps hG hheight
  have hg' : LipschitzWith (1/4) g := hg.weaken (by
    change (2*(1/8:ℝ)) ≤ ((1/4 : ℝ≥0) : ℝ)
    norm_num)
  have hid : (∀ y ∈ Metric.ball (0 : Plane) (r/1024),
      quotientMap c₀+quotientMap (normalGraph n₀ g y) ∈ frontier (openRepresentative E) ∧
      ‖normalGraph n₀ g y‖ < r/512) := by
    simpa only [show r/256/4 = r/1024 by ring,show r/256/2 = r/512 by ring] using hinside
  refine ⟨g,hg',?_,hid,hrepr⟩
  let f : Plane → Cover := fun y ↦ c₀+normalGraph n₀ g y
  have hf : Continuous f := continuous_const.add (normalGraph_lipschitz hn₀ hg').continuous
  have hmaps : MapsTo f (Metric.ball (0 : Plane) (r/1024))
      (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)) := by
    intro y hy
    refine ⟨?_,?_⟩
    · simpa only [mem_preimage,f,quotientMap_add] using (hid y hy).1
    · change dist (c₀+normalGraph n₀ g y) c₀ < r/128
      rw [dist_eq_norm,add_sub_cancel_left]
      exact (hid y hy).2.trans_le (by linarith)
  apply normalGraph_contDiffOn_one_of_continuous_normal hn₀ hg' Metric.isOpen_ball
    (fun y ↦ ν (f y)) (hνcont.comp hf.continuousOn hmaps) (fun y hy ↦ (hid y hy).1)
  · intro y hy
    have hh := (hν (f y) (hmaps hy)).2.2
    simpa only [f,quotientMap_add] using hh
  · intro y hy hzero
    have hh := (hν (f y) (hmaps hy)).2.1.trans hCe
    have hi := abs_real_inner_le_norm (n₀-ν (f y)) n₀
    rw [inner_sub_left,hzero,real_inner_self_eq_norm_sq,hn₀] at hi
    norm_num at hi
    linarith

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def BoundaryC1Patch (U : Set Torus) (a : Torus) (n : Cover) (g : Plane → ℝ) (R r : ℝ) : Prop :=
  ‖n‖ = 1 ∧ 0 < R ∧ 0 < r ∧ ContDiffOn ℝ 1 g (Metric.ball 0 R) ∧
  (∀ y ∈ Metric.ball (0 : Plane) R, ‖normalGraph n g y‖ < 1/4 ∧
    a+quotientMap (normalGraph n g y) ∈ frontier U) ∧
  frontier U ∩ Metric.ball a r ⊆
    (fun y ↦ a+quotientMap (normalGraph n g y)) '' Metric.ball 0 R

def C1RegularPoint (U : Set Torus) (x : Torus) : Prop :=
  ∃ a n g R r, BoundaryC1Patch U a n g R r ∧ x ∈ Metric.ball a r

lemma isOpen_c1RegularPoint (U : Set Torus) : IsOpen {x | C1RegularPoint U x} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨a,n,g,R,r,hp,hx⟩
  apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx)
  exact fun y hy ↦ ⟨a,n,g,R,r,hp,hy⟩

lemma c1Patch_of_exact_graph {U : Set Torus} (c : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {r : ℝ} (hr : 0 < r) (hrs : r ≤ 1/8)
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 (r/1024)))
    (hi : ∀ y ∈ Metric.ball (0 : Plane) (r/1024),
      quotientMap c+quotientMap (normalGraph n g y) ∈ frontier U ∧ ‖normalGraph n g y‖ < r/512)
    (hb : ∀ x ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball c (r/128),
      normalGraph n g (normalPlaneCoordinates n (x-c)) = x-c) :
    BoundaryC1Patch U (quotientMap c) n g (r/1024) (r/1024) := by
  refine ⟨hn,by positivity,by positivity,hg,?_,?_⟩
  · intro y hy
    exact ⟨(hi y hy).2.trans_le (by linarith),(hi y hy).1⟩
  · intro x hx
    let v := shortestLift (x-quotientMap c)
    have hvq : quotientMap v = x-quotientMap c := quotientMap_shortestLift _
    have hxq : quotientMap (c+v) = x := by rw [quotientMap_add,hvq]; abel
    have hvsmall : ‖v‖ < r/1024 := by
      simpa only [v,norm_shortestLift,← dist_eq_norm,Metric.mem_ball] using hx.2
    have hcv : c+v ∈ quotientMap ⁻¹' frontier U ∩ Metric.ball c (r/128) := by
      refine ⟨by simpa only [mem_preimage,hxq] using hx.1,?_⟩
      change dist (c+v) c < r/128
      rw [dist_eq_norm,add_sub_cancel_left]
      linarith
    have heq := hb (c+v) hcv
    rw [add_sub_cancel_left] at heq
    refine ⟨normalPlaneCoordinates n v,?_,?_⟩
    · have hh := (normalPlaneCoordinates_lipschitz n).norm_sub_le v 0
      simp only [map_zero,sub_zero,NNReal.coe_one,one_mul] at hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh.trans_lt hvsmall
    · change quotientMap c + quotientMap (normalGraph n g (normalPlaneCoordinates n v)) = x
      rw [heq,hvq]
      abel

lemma exists_radius_of_normalExcess_tendsto {μ : FiniteMeasure NormalBundle}
    (N : Torus → Cover) (a : Torus) (n : Cover)
    (hlim : Tendsto (normalExcess (spatialNormalMeasure μ) N a n) (𝓝[>] 0) (𝓝 0))
    {R δ e : ℝ} (hR : 0 < R) (hδ : 0 < δ) (he : 0 < e) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ r/e^2 ≤ δ ∧
      (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 := by
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), normalExcess (spatialNormalMeasure μ) N a n t < e^2/289 :=
    hlim.eventually (Iio_mem_nhds (by positivity))
  have hb' := eventually_nhdsGT_zero_mul_left (by norm_num : (0:ℝ) < 17) hb
  have hs : 0 < min R (δ*e^2) := by positivity
  have hp : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < min R (δ*e^2) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)
  obtain ⟨r,hr,hrs,hb⟩ := (hp.and (hsmall.and hb')).exists
  have hrpos : 0 < r := hr
  have hrs' : r < min R (δ*e^2) := hrs
  refine ⟨r,hrpos,(hrs'.le.trans (min_le_left _ _)),?_,?_⟩
  · exact (div_le_iff₀ (sq_pos_of_pos he)).2 (hrs'.le.trans (min_le_right _ _))
  · dsimp only [normalExcess] at hb
    have hh := (div_lt_iff₀ (sq_pos_of_pos (by positivity : 0 < 17*r))).mp hb
    calc
      _ ≤ (e^2/289)*(17*r)^2 := hh.le
      _ = r^2*e^2 := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_c1_regular_ae_local {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ a ∂(spatialNormalMeasure μ : Measure Torus),
      a ∈ frontier (openRepresentative E) ∩ Metric.ball (quotientMap cubeCenter) (1/32) →
      C1RegularPoint (openRepresentative E) a := by
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨R,hR,htheorem⟩ := isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨δ,hδ,hregular⟩ := htheorem μ hμ N hN hp hu
  have hae := isMinimizerAt_normal_excess_ae hV hE hmin hμ hN hu
  filter_upwards [hae] with a ha hlocal
  let c := cubeCenter+shortestLift (a-quotientMap cubeCenter)
  have hcq : quotientMap c = a := by
    dsimp only [c]
    rw [quotientMap_add,quotientMap_shortestLift]
    abel
  have hc : ‖c-cubeCenter‖ ≤ 1/16 := by
    dsimp only [c]
    rw [add_sub_cancel_left,norm_shortestLift,← dist_eq_norm]
    have hh : dist a (quotientMap cubeCenter) < 1/32 := hlocal.2
    linarith
  obtain ⟨r,hr,hrsmall,hratio,ht⟩ := exists_radius_of_normalExcess_tendsto N a (N a) ha.2
    (lt_min hR (by norm_num : (0:ℝ) < 1/8)) hδ (by positivity : 0 < δ/2)
  have ht' : (∫ x in Metric.closedBall (quotientMap c) (17*r), ‖N x-N a‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*(δ/2)^2 := by rwa [hcq]
  obtain ⟨g,hg,hgC,hinside,hboundary⟩ := hregular c hc (by rw [hcq]; exact hlocal.1) (N a) r (δ/2)
    ha.1 hr (hrsmall.trans (min_le_left _ _)) (by positivity) (by linarith) hratio ht'
  have hpatch := c1Patch_of_exact_graph c ha.1 hr (hrsmall.trans (min_le_right _ _)) hgC hinside hboundary
  refine ⟨quotientMap c,N a,g,r/1024,r/1024,hpatch,?_⟩
  rw [hcq]
  exact Metric.mem_ball_self (by positivity)

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma support_inter_open_subset_closure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) {O S : Set X} (hO : IsOpen O)
    (hS : ∀ᵐ x ∂μ, x ∈ μ.support ∩ O → x ∈ S) :
    μ.support ∩ O ⊆ closure (μ.support ∩ O ∩ S) := by
  have hclosed : IsClosed (Oᶜ ∪ closure (μ.support ∩ O ∩ S)) :=
    hO.isClosed_compl.union isClosed_closure
  have hfull : ∀ᵐ x ∂μ, x ∈ Oᶜ ∪ closure (μ.support ∩ O ∩ S) := by
    filter_upwards [μ.support_mem_ae,hS] with x hx hs
    by_cases ho : x ∈ O
    · exact Or.inr (subset_closure ⟨⟨hx,ho⟩,hs ⟨hx,ho⟩⟩)
    · exact Or.inl ho
  have hh := μ.support_subset_of_isClosed hclosed hfull
  intro x hx
  exact (hh hx.1).resolve_left (by simpa using hx.2)

theorem MovingCenter.isMinimizerAt_c1_regular_dense_local {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    frontier (openRepresentative E) ∩ Metric.ball (quotientMap cubeCenter) (1/32) ⊆
      closure (frontier (openRepresentative E) ∩ Metric.ball (quotientMap cubeCenter) (1/32) ∩
        {x | C1RegularPoint (openRepresentative E) x}) := by
  have hs := isMinimizerAt_perimeter_support hV hE hmin hμ
  have ha := MovingCenter.isMinimizerAt_c1_regular_ae_local hV hE hmin hcenter hμ
  rw [← hs] at ha ⊢
  exact support_inter_open_subset_closure (spatialNormalMeasure μ : Measure Torus)
    Metric.isOpen_ball ha

theorem MovingCenter.isMinimizerAt_c1_singular_null_local {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus)
      ((frontier (openRepresentative E) ∩ Metric.ball (quotientMap cubeCenter) (1/32)) \
        {x | C1RegularPoint (openRepresentative E) x}) = 0 := by
  have ha := MovingCenter.isMinimizerAt_c1_regular_ae_local hV hE hmin hcenter hμ
  convert (ae_iff.mp ha) using 2
  ext x
  simp only [Set.mem_sdiff,mem_ofPred_eq,Classical.not_imp]

lemma isCompact_c1SingularPart (U : Set Torus) (a : Torus) (r : ℝ) :
    IsCompact ((frontier U ∩ Metric.closedBall a r) \ {x | C1RegularPoint U x}) := by
  exact ((isClosed_frontier.inter Metric.isClosed_closedBall).inter
    (isOpen_c1RegularPoint U).isClosed_compl).isCompact

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothApprox_sub_eq_integral {g : Cover → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (n : ℕ) (x : Cover) :
    smoothApprox g n x-g x =
      ∫ y : Cover, (mollifier n).normed volume y*(g (x-y)-g x) := by
  have hi : Integrable (fun y : Cover ↦ (mollifier n).normed volume y*g (x-y)) := by
    apply (mollifier n).integrable_normed.mul_bdd
      (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    exact ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.sub_apply,id_eq] using hb (x-y)
  simp_rw [mul_sub]
  rw [integral_sub hi ((mollifier n).integrable_normed.mul_const _),
    integral_mul_const,(mollifier n).integral_normed,one_mul]
  rfl

theorem smoothApprox_error_local {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (htrans : ∀ y : Cover, ‖y‖ ≤ (mollifier n).rOut →
      (∫ x, |g (x-y)-g x| ∂η) ≤ ‖y‖*A) :
    (∫ x, |smoothApprox g n x-g x| ∂η) ≤ (mollifier n).rOut*A := by
  let φ : Cover → ℝ := (mollifier n).normed volume
  let d : Cover × Cover → ℝ := fun z ↦ |g (z.1-z.2)-g z.1|
  have hφ : Integrable φ volume := (mollifier n).integrable_normed
  have hd : Measurable d := ((hg.comp (measurable_fst.sub measurable_snd)).sub
    (hg.comp measurable_fst)).abs
  have hdb (z : Cover × Cover) : |d z| ≤ 2 := by
    simpa only [d,abs_abs] using (abs_sub _ _).trans (by linarith [hb (z.1-z.2),hb z.1])
  have hbase : Integrable (fun z : Cover × Cover ↦ φ z.2) (η.prod volume) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := η)).mul_prod hφ
  have hprod : Integrable (fun z : Cover × Cover ↦ φ z.2*d z) (η.prod volume) :=
    hbase.mul_bdd hd.aestronglyMeasurable (ae_of_all _ hdb)
  have hinside (x : Cover) : |smoothApprox g n x-g x| ≤ ∫ y : Cover, φ y*d (x,y) := by
    rw [smoothApprox_sub_eq_integral hg hb]
    calc
      _ ≤ ∫ y : Cover, ‖φ y*(g (x-y)-g x)‖ := norm_integral_le_integral_norm _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((mollifier n).nonneg_normed y),φ,d]
  have hm : Integrable (smoothApprox g n) η := Integrable.of_bound
    (smoothApprox_contDiff hg hb n).continuous.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using smoothApprox_bound hb n x)
  have hgint : Integrable g η := Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hkernel (y : Cover) : φ y*(∫ x, d (x,y) ∂η) ≤ φ y*((mollifier n).rOut*A) := by
    by_cases hy : φ y = 0
    · simp [hy]
    have hyr : ‖y‖ ≤ (mollifier n).rOut := by
      have hy' : y ∈ Metric.ball (0 : Cover) (mollifier n).rOut := by
        rw [← (mollifier n).support_normed_eq (μ := (volume : Measure Cover))]
        exact hy
      exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hy')
    exact mul_le_mul_of_nonneg_left ((htrans y hyr).trans (mul_le_mul_of_nonneg_right hyr hA))
      ((mollifier n).nonneg_normed y)
  calc
    _ ≤ ∫ x, ∫ y : Cover, φ y*d (x,y) ∂volume ∂η :=
      integral_mono (hm.sub hgint).abs hprod.integral_prod_left hinside
    _ = ∫ y : Cover, ∫ x, φ y*d (x,y) ∂η := integral_integral_swap hprod
    _ = ∫ y : Cover, φ y*(∫ x, d (x,y) ∂η) := by simp_rw [integral_const_mul]
    _ ≤ ∫ y : Cover, φ y*((mollifier n).rOut*A) := by
      apply integral_mono _ (hφ.mul_const _) hkernel
      simpa only [integral_const_mul] using hprod.integral_prod_right
    _ = _ := by rw [integral_mul_const,(mollifier n).integral_normed,one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_bounded_one {η : Measure Cover} [IsFiniteMeasure η]
    {g : Cover → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) : Integrable g η :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)

def boundedFunctionL1 (η : Measure Cover) [IsFiniteMeasure η]
    (g : Cover → ℝ) (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) : Lp ℝ 1 η :=
  (integrable_bounded_one hg hb).toL1 g

lemma boundedFunctionL1_dist {η : Measure Cover} [IsFiniteMeasure η]
    {f g : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hg : Measurable g) (hgb : ∀ x, |g x| ≤ 1) :
    dist (boundedFunctionL1 η f hf hfb) (boundedFunctionL1 η g hg hgb) =
      ∫ x, |f x-g x| ∂η := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [(integrable_bounded_one (η := η) hf hfb).coeFn_toL1,
    (integrable_bounded_one (η := η) hg hgb).coeFn_toL1] with x hx hy
  change dist ((integrable_bounded_one hf hfb).toL1 f x)
    ((integrable_bounded_one hg hgb).toL1 g x) = _
  rw [hx,hy,Real.dist_eq]

lemma totallyBounded_local_smoothApprox {ι : Type*} {η : Measure Cover}
    {K : Set Cover} (hK : IsCompact K) [IsFiniteMeasure (η.restrict K)]
    (g : ι → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hb : ∀ i x, |g i x| ≤ 1) (n : ℕ) :
    TotallyBounded (range fun i ↦ boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable (smoothApprox_bound (hb i) n)) := by
  let ν : Measure K := Measure.comap Subtype.val η
  have hv := measurePreserving_subtype_coe (μa := η) hK.measurableSet
  change MeasurePreserving ((↑) : K → Cover) ν (η.restrict K) at hv
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (Measure.map ((↑) : K → Cover) ν) := hv.map_eq.symm ▸ inferInstance
  let : IsFiniteMeasure ν := Measure.isFiniteMeasure_of_map hv.measurable.aemeasurable
  let F : ι → BoundedContinuousFunction K ℝ := fun i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ smoothApprox (g i) n x,
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.comp continuous_subtype_val⟩
  have hLip (i) : LipschitzWith (smoothApproxLip n) (F i) := by
    change LipschitzWith (smoothApproxLip n) (smoothApprox (g i) n ∘ (Subtype.val : K → Cover))
    simpa only [mul_one] using (smoothApprox_lipschitz (hg i) (hb i) n).comp
      (LipschitzWith.subtype_val K)
  have hequi : Equicontinuous ((↑) : range F → K → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (smoothApproxLip n)
    rintro ⟨_,i,rfl⟩
    exact hLip i
  have hbounded (f : BoundedContinuousFunction K ℝ) (x : K) (hf : f ∈ range F) :
      f x ∈ Icc (-1) 1 := by
    obtain ⟨i,rfl⟩ := hf
    exact abs_le.mp (smoothApprox_bound (hb i) n x)
  have hc := BoundedContinuousFunction.arzela_ascoli (Icc (-1 : ℝ) 1) isCompact_Icc
    (range F) hbounded hequi
  let B : BoundedContinuousFunction K ℝ →L[ℝ] Lp ℝ 1 ν :=
    BoundedContinuousFunction.toLp 1 ν ℝ
  have htb : TotallyBounded (B '' closure (range F)) := (hc.image B.continuous).totallyBounded
  let T := Lp.compMeasurePreserving ((↑) : K → Cover) hv (E := ℝ) (p := 1)
  apply (totallyBounded_preimage (Lp.isometry_compMeasurePreserving hv).isUniformInducing htb).subset
  rintro _ ⟨i,rfl⟩
  refine ⟨F i,subset_closure (mem_range_self i),?_⟩
  apply Lp.ext
  have hi := (integrable_bounded_one (η := η.restrict K)
    (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable (smoothApprox_bound (hb i) n)).coeFn_toL1
  have hi' : ∀ᵐ x : K ∂ν,
      boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
        (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
          (smoothApprox_bound (hb i) n) (x : Cover) = smoothApprox (g i) n x := by
    have hi'' : ∀ᵐ y ∂Measure.map ((↑) : K → Cover) ν,
        boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
          (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
            (smoothApprox_bound (hb i) n) y = smoothApprox (g i) n y := by
      rw [hv.map_eq]
      exact hi
    exact ae_of_ae_map hv.measurable.aemeasurable hi''
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
        (smoothApprox_bound (hb i) n)) hv,hi',
      BoundedContinuousFunction.coeFn_toLp 1 ν ℝ (F i)] with x hx hi hxF
  exact hxF.trans (hi.symm.trans hx.symm)

theorem totallyBounded_local_translation {ι : Type*} {η : Measure Cover}
    {K : Set Cover} (hK : IsCompact K) [IsFiniteMeasure (η.restrict K)]
    (g : ι → Cover → ℝ) (hg : ∀ i, Measurable (g i)) (hb : ∀ i x, |g i x| ≤ 1)
    {A ε₀ : ℝ} (hA : 0 ≤ A) (hε₀ : 0 < ε₀)
    (htrans : ∀ i y, ‖y‖ ≤ ε₀ →
      (∫ x in K, |g i (x-y)-g i x| ∂η) ≤ ‖y‖*A) :
    TotallyBounded (range fun i ↦ boundedFunctionL1 (η.restrict K) (g i) (hg i) (hb i)) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hconv : Tendsto (fun n ↦ (mollifier n).rOut*A) atTop (𝓝 0) := by
    simpa only [zero_mul] using mollifier_rOut_tendsto.mul_const A
  obtain ⟨n,hn,hns⟩ := ((hconv.eventually (gt_mem_nhds (half_pos hε))).and
    (mollifier_rOut_tendsto.eventually (gt_mem_nhds hε₀))).exists
  obtain ⟨t,ht,hcover⟩ := Metric.totallyBounded_iff.mp
    (totallyBounded_local_smoothApprox (η := η) hK g hg hb n) (ε/2) (half_pos hε)
  refine ⟨t,ht,?_⟩
  rintro _ ⟨i,rfl⟩
  obtain ⟨y,hy,hiy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨y,hy,?_⟩
  have hdist : dist (boundedFunctionL1 (η.restrict K) (g i) (hg i) (hb i))
      (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
        (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
          (smoothApprox_bound (hb i) n)) < ε/2 := by
    rw [dist_comm,boundedFunctionL1_dist]
    exact (smoothApprox_error_local (hg i) (hb i) hA n
      (fun y hy ↦ htrans i y (hy.trans hns.le))).trans_lt hn
  have hiy' : dist (boundedFunctionL1 (η.restrict K) (smoothApprox (g i) n)
      (smoothApprox_contDiff (hg i) (hb i) n).continuous.measurable
        (smoothApprox_bound (hb i) n)) y < ε/2 := hiy
  exact (dist_triangle _ _ _).trans_lt (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_ball_affine_scaling (f : Cover → ℝ) (a : Cover) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    (∫ x in Metric.ball a (r*R), f x) =
      r^3 * ∫ y in Metric.ball (0 : Cover) R, f (a+r • y) := by
  have h := integral_cover_affine_scaling ((Metric.ball a (r*R)).indicator f) a hr
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at h
  rw [h, ← integral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hm : r • x+a ∈ Metric.ball a (r*R) ↔ x ∈ Metric.ball (0 : Cover) R := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero,
      norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_iff_right₀ hr
  change (Metric.ball a (r*R)).indicator f (r • x+a) =
    (Metric.ball (0 : Cover) R).indicator (fun y ↦ f (a+r • y)) x
  by_cases hx : x ∈ Metric.ball (0 : Cover) R
  · rw [indicator_of_mem (hm.mpr hx),indicator_of_mem hx,add_comm]
  · rw [indicator_of_notMem ((not_congr hm).mpr hx),indicator_of_notMem hx]

lemma fundamentalCube_inter_ball_preimage (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    fundamentalCube ∩ quotientMap ⁻¹' Metric.ball (quotientMap c) r = Metric.ball c r := by
  ext x
  constructor
  · rintro ⟨hx,hq⟩
    rw [← quotientMap_image_ball c r] at hq
    obtain ⟨y,hy,he⟩ := hq
    have he' := quotientMap_injective_open_closed_cell
      (fun i ↦ ⟨(hx i).1,(hx i).2.le⟩) (hc hy) he.symm
    rwa [he']
  · intro hx
    refine ⟨fun i ↦ ⟨(hc hx i).1.le,(hc hx i).2⟩,?_⟩
    rw [mem_preimage, ← quotientMap_image_ball c r]
    exact mem_image_of_mem _ hx

lemma integral_quotient_ball (f : Torus → ℝ) (hf : Measurable f)
    (c : Cover) (r : ℝ)
    (hc : Metric.ball c r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap c) r, f x ∂torusVolume) =
      ∫ x in Metric.ball c r, f (quotientMap x) := by
  rw [setIntegral_lift_measurable hf Metric.isOpen_ball.measurableSet,
    fundamentalCube_inter_ball_preimage c r hc]

def blowupCharacteristic (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) : ℝ :=
  characteristic E (quotientMap (c+r • x))

lemma measurable_blowupCharacteristic {E : Set Torus} (hE : MeasurableSet E)
    (c : Cover) (r : ℝ) : Measurable (blowupCharacteristic E c r) :=
  (measurable_characteristic hE).comp (measurable_quotientMap.comp
    (measurable_const.add (measurable_id.const_smul r)))

lemma blowupCharacteristic_bound (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) :
    |blowupCharacteristic E c r x| ≤ 1 := characteristic_bound _ _

lemma blowupCharacteristic_translation_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ) {s : ℝ} (hs : 0 < s)
    (hc : Metric.ball c (r*R) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (y : Cover) :
    (∫ x in Metric.ball (0 : Cover) R,
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x|) ≤
      r⁻¹^3 * ‖quotientMap (r • y)‖ *
        (spatialNormalMeasure μ : Measure Torus).real
          (Metric.ball (quotientMap c) (r*R+s+‖quotientMap (r • y)‖)) := by
  let f : Torus → ℝ := fun x ↦
    |characteristic E (x-quotientMap (r • y))-characteristic E x|
  have hf : Measurable f := (((measurable_characteristic hE).comp
    (measurable_id.sub_const _)).sub (measurable_characteristic hE)).abs
  have h := characteristic_translation_bound_local hE hμ (quotientMap c) hs
    (r := r*R) (quotientMap (r • y))
  rw [integral_quotient_ball f hf c (r*R) hc,
    integral_ball_affine_scaling (fun x ↦ f (quotientMap x)) c hr R] at h
  have heq (x : Cover) : f (quotientMap (c+r • x)) =
      |blowupCharacteristic E c r (x-y)-blowupCharacteristic E c r x| := by
    simp only [f,blowupCharacteristic, ← quotientMap_sub, smul_sub]
    congr 3
    abel_nf
  simp_rw [heq] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hr.le 3))
  simpa [mul_assoc,hr.ne'] using hh

end CubicTorus

end
end

end

end OAI
