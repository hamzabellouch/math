import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVBlowupRigidCovariance

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma planarSlope_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun y : Plane ↦ (planarWedgeCoordinates y).2) volume volume :=
  (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    planarWedgeCoordinates_quasiMeasurePreserving

theorem moving_product_angular_boundary_subsingleton
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b w : ℝ}
    (hB : MeasurableSet B) (hη : 0 < η) (hb : 0 < b) (hw : 0 < w)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {D : Set ℝ} (hD : MeasurableSet D)
    (hfin : (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite)
    (hmodel : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < w → (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x) :
    (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton := by
  have hno : ∀ l v : ℝ, l ∈ Ioo (-(w/4)) (w/4) → v ∈ Ioo (-(w/4)) (w/4) →
      l ∈ angularEssentialBoundary D → v ∈ angularEssentialBoundary D → l < v → False := by
    intro l v hl hv hlb hvb hlv
    obtain ⟨u,hlu,huv,hub,hadj⟩ := finite_angular_next_transition hfin hl hv hlv hvb
    have hu : u ∈ Ioo (-(w/4)) (w/4) := ⟨hl.1.trans hlu,huv.trans_lt hv.2⟩
    obtain ⟨δ,hδ,hgap,hphase⟩ := adjacent_angular_sector_model hD hfin hl hu hlu hlb hub hadj
    have hwide {t : ℝ} (ht : t ∈ Ioo (l-δ) (u+δ)) : |t| < w := by
      apply lt_trans ?_ (half_lt_self hw)
      apply abs_lt.mpr
      constructor <;> linarith [hl.1,hl.2,hu.1,hu.2,ht.1,ht.2]
    apply no_moving_product_angular_sector hB hη hb hδ hgap hmin hprod R ?_ heq hflux
    rcases hphase with hi|hi
    · apply Or.inl
      filter_upwards [hmodel,planarSlope_quasiMeasurePreserving.ae hi] with y hm hi hr hs
      exact (hm hr (hwide hs)).trans (hi hs)
    · apply Or.inr
      filter_upwards [hmodel,planarSlope_quasiMeasurePreserving.ae hi] with y hm hi hr hs
      exact (not_congr (hm hr (hwide hs))).trans (hi hs)
  intro l hl u hu
  rcases lt_trichotomy l u with hlt|he|hgt
  · exact (hno l u hl.1 hu.1 hl.2 hu.2 hlt).elim
  · exact he
  · exact (hno u l hu.1 hl.1 hu.2 hl.2 hgt).elim

theorem minimizing_planar_chart_single_transition
    {B : Set Cover} {C : Set Plane} {n : Cover} {η : ℝ}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hη : 0 < η)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x)
    (R : Plane ≃ₗᵢ[ℝ] Plane) {w : ℝ} (hw : 0 < w) :
    ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
      (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
      ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
        |(planarWedgeCoordinates y).2| < w →
        (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  obtain ⟨b,D,hb,hD,hfin,hmodel⟩ := planar_cone_wide_vertex_section hC hc hK hbv R hw
  exact ⟨b,D,hb,hD,moving_product_angular_boundary_subsingleton hB hη hb hw hmin hprod R hD
    hfin hmodel heq hflux,hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarEssentialBoundary (C : Set Plane) : Set Plane :=
  (volume.restrict C).support ∩ (volume.restrict Cᶜ).support

lemma planarEssentialBoundary_compl (C : Set Plane) :
    planarEssentialBoundary Cᶜ = planarEssentialBoundary C := by
  rw [planarEssentialBoundary,compl_compl,inter_comm]
  rfl

lemma mem_planarEssentialBoundary_iff {C : Set Plane} {p : Plane} :
    p ∈ planarEssentialBoundary C ↔ ∀ δ : ℝ, 0 < δ →
      0 < volume (C ∩ Metric.ball p δ) ∧ 0 < volume (Cᶜ ∩ Metric.ball p δ) := by
  simp only [planarEssentialBoundary,Set.mem_inter_iff,Metric.nhds_basis_ball.mem_measureSupport,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet,inter_comm,forall_and]

lemma measureSupport_local_ae_mono {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {A B O : Set X} {p : X}
    (hO : O ∈ 𝓝 p) (hae : ∀ᵐ x ∂μ, x ∈ O → x ∈ A → x ∈ B)
    (hp : p ∈ (μ.restrict A).support) : p ∈ (μ.restrict B).support := by
  obtain ⟨W,hWO,hW,hpW⟩ := mem_nhds_iff.mp hO
  rw [(nhds_basis_opens p).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  have hpos := (Measure.mem_support_iff_forall p).mp hp (U ∩ W)
    (inter_mem (hU.mem_nhds hpU) (hW.mem_nhds hpW))
  rw [Measure.restrict_apply (hU.inter hW).measurableSet] at hpos
  rw [Measure.restrict_apply hU.measurableSet]
  apply hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hae] with x hx hxx
  exact ⟨hxx.1.1,hx (hWO hxx.1.2) hxx.2⟩

lemma planar_boundary_local_ae {C D O : Set Plane} {p : Plane}
    (hO : O ∈ 𝓝 p) (hae : ∀ᵐ y : Plane ∂volume, y ∈ O → (y ∈ C ↔ y ∈ D))
    (hp : p ∈ planarEssentialBoundary C) : p ∈ planarEssentialBoundary D := by
  exact ⟨measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (h ho).mp)) hp.1,
    measureSupport_local_ae_mono hO (hae.mono (fun _ h ho ↦ (not_congr (h ho)).mp)) hp.2⟩

lemma measureSupport_preimage_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {D : Set Y} {p : X}
    (hq : Measure.QuasiMeasurePreserving f μ ν) (hf : ContinuousAt f p)
    (hp : p ∈ (μ.restrict (f ⁻¹' D)).support) : f p ∈ (ν.restrict D).support := by
  rw [(nhds_basis_opens (f p)).mem_measureSupport]
  rintro U ⟨hpU,hU⟩
  rw [Measure.restrict_apply hU.measurableSet]
  by_contra h
  have hzero : ν (U ∩ D) = 0 := (not_lt.mp h).antisymm bot_le
  have hz := hq.preimage_null hzero
  have hpos := (Measure.mem_support_iff_forall p).mp hp (f ⁻¹' U)
    (hf (hU.mem_nhds hpU))
  rw [Measure.restrict_apply (hU.measurableSet.preimage hq.measurable)] at hpos
  exact (ne_of_gt hpos) hz

lemma planar_boundary_preimage_image {C : Set Plane} {f : Plane → Plane} {p : Plane}
    (hq : Measure.QuasiMeasurePreserving f volume volume) (hf : ContinuousAt f p)
    (hp : p ∈ planarEssentialBoundary (f ⁻¹' C)) : f p ∈ planarEssentialBoundary C := by
  exact ⟨measureSupport_preimage_image hq hf hp.1,measureSupport_preimage_image hq hf hp.2⟩

lemma planar_boundary_isometry {C : Set Plane} (R : Plane ≃ₗᵢ[ℝ] Plane) {p : Plane}
    (hp : p ∈ planarEssentialBoundary C) : R.symm p ∈ planarEssentialBoundary (R ⁻¹' C) := by
  apply planar_boundary_preimage_image R.symm.measurePreserving.quasiMeasurePreserving R.symm.continuous.continuousAt
  convert! hp using 1
  congr 1
  ext x
  simp only [Set.mem_preimage,R.apply_symm_apply]

lemma continuousAt_planarWedgeCoordinates {p : Plane} (hp : (planeProductCoordinates p).1 ≠ 0) :
    ContinuousAt planarWedgeCoordinates p := by
  exact (planeProductCoordinates.continuous.fst.continuousAt).prodMk
    (((planeProductCoordinates.continuous.fst.continuousAt).inv₀ hp).mul
      planeProductCoordinates.continuous.snd.continuousAt)

lemma planar_boundary_angular_transition {C : Set Plane} {D : Set ℝ} {b w : ℝ}
    (hmodel : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < w → (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p : Plane} (hp : p ∈ planarEssentialBoundary C)
    (hpr : (planarWedgeCoordinates p).1 ∈ Ioo 0 b)
    (hps : |(planarWedgeCoordinates p).2| < w) :
    (planarWedgeCoordinates p).2 ∈ angularEssentialBoundary D := by
  let f : Plane → ℝ := fun y ↦ (planarWedgeCoordinates y).2
  have hc := continuousAt_planarWedgeCoordinates (show (planeProductCoordinates p).1 ≠ 0 from hpr.1.ne')
  have hO : {y : Plane | (planarWedgeCoordinates y).1 ∈ Ioo 0 b ∧
      |(planarWedgeCoordinates y).2| < w} ∈ 𝓝 p := by
    exact inter_mem (hc.fst (isOpen_Ioo.mem_nhds hpr))
      ((hc.snd.abs) (Iio_mem_nhds hps))
  have hp' : p ∈ planarEssentialBoundary (f ⁻¹' D) :=
    planar_boundary_local_ae hO (hmodel.mono (fun _ h hy ↦ h hy.1 hy.2)) hp
  rw [angularEssentialBoundary_eq_support]
  exact ⟨measureSupport_preimage_image (f := f) (p := p) planarSlope_quasiMeasurePreserving hc.snd hp'.1,
    measureSupport_preimage_image (f := f) (p := p) planarSlope_quasiMeasurePreserving hc.snd hp'.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_cone_boundary_contract {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {p : Plane} (hp : p ∈ planarEssentialBoundary C) (hpball : p ∈ Metric.ball (0 : Plane) (1/16))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) : c • p ∈ planarEssentialBoundary C := by
  have hca := hc c⁻¹ ((one_le_inv₀ hc0).mpr hc1)
  simp only [inv_inv] at hca
  have hp' : p ∈ planarEssentialBoundary ((fun y : Plane ↦ c • y) ⁻¹' C) :=
    planar_boundary_local_ae (Metric.isOpen_ball.mem_nhds hpball)
      (hca.mono (fun _ h hy ↦ (h hy).symm)) hp
  exact planar_boundary_preimage_image (Measure.quasiMeasurePreserving_smul volume hc0.ne')
    (continuous_const_smul c).continuousAt hp'

theorem planar_cone_boundary_chart_unique_slope {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p q : Plane} (hp : p ∈ planarEssentialBoundary C) (hq : q ∈ planarEssentialBoundary C)
    (hpb : p ∈ Metric.ball (0 : Plane) (1/16)) (hqb : q ∈ Metric.ball (0 : Plane) (1/16))
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hpr : 0 < (planarWedgeCoordinates (R.symm p)).1)
    (hqr : 0 < (planarWedgeCoordinates (R.symm q)).1) :
    (planarWedgeCoordinates (R.symm p)).2 = (planarWedgeCoordinates (R.symm q)).2 := by
  let s := (planarWedgeCoordinates (R.symm p)).2
  let t := (planarWedgeCoordinates (R.symm q)).2
  let a := (planarWedgeCoordinates (R.symm p)).1
  let d := (planarWedgeCoordinates (R.symm q)).1
  let w : ℝ := 4*(|s|+|t|+1)
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨b,D,hb,hD,hsub,hmodel⟩ := hcharts R w hw
  let c : ℝ := min (1/2) (b/(2*(a+d+1)))
  have had : 0 < a+d+1 := by change 0 < (planarWedgeCoordinates (R.symm p)).1 + (planarWedgeCoordinates (R.symm q)).1 + 1; linarith
  have hc0 : 0 < c := lt_min (by norm_num) (div_pos hb (by positivity))
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hcb := (le_div_iff₀ (show 0 < 2*(a+d+1) by positivity)).mp (min_le_right (1/2) (b/(2*(a+d+1))))
  have hcpa : c*a < b := by
    have ha0 : 0 < a := hpr
    have hd0 : 0 < d := hqr
    nlinarith [mul_pos hc0 hd0]
  have hcqd : c*d < b := by
    have ha0 : 0 < a := hpr
    have hd0 : 0 < d := hqr
    nlinarith [mul_pos hc0 ha0]
  have hsi : s ∈ Ioo (-(w/4)) (w/4) := by dsimp [w]; constructor <;> linarith [neg_abs_le s,le_abs_self s,abs_nonneg t]
  have hti : t ∈ Ioo (-(w/4)) (w/4) := by dsimp [w]; constructor <;> linarith [neg_abs_le t,le_abs_self t,abs_nonneg s]
  have hsw : |s| < w := by dsimp [w]; linarith [abs_nonneg s,abs_nonneg t]
  have htw : |t| < w := by dsimp [w]; linarith [abs_nonneg s,abs_nonneg t]
  have heP : planarWedgeCoordinates (R.symm (c • p)) = (c*a,s) := by
    rw [map_smul,planarWedgeCoordinates_smul hc0.ne']
  have heQ : planarWedgeCoordinates (R.symm (c • q)) = (c*d,t) := by
    rw [map_smul,planarWedgeCoordinates_smul hc0.ne']
  have hps := planar_boundary_angular_transition hmodel
    (planar_boundary_isometry R (planar_cone_boundary_contract hc hp hpb hc0 hc1))
    (by rw [heP]; exact ⟨mul_pos hc0 hpr,hcpa⟩) (by rwa [heP])
  have hqs := planar_boundary_angular_transition hmodel
    (planar_boundary_isometry R (planar_cone_boundary_contract hc hq hqb hc0 hc1))
    (by rw [heQ]; exact ⟨mul_pos hc0 hqr,hcqd⟩) (by rwa [heQ])
  rw [heP] at hps
  rw [heQ] at hqs
  exact hsub ⟨hsi,hps⟩ ⟨hti,hqs⟩

lemma planar_equal_positive_slopes_collinear {p q : Plane}
    (hp : 0 < (planarWedgeCoordinates p).1) (hq : 0 < (planarWedgeCoordinates q).1)
    (hsl : (planarWedgeCoordinates p).2 = (planarWedgeCoordinates q).2) :
    ∃ t : ℝ, 0 < t ∧ q = t • p := by
  let t : ℝ := (planeProductCoordinates q).1 / (planeProductCoordinates p).1
  refine ⟨t,div_pos hq hp,?_⟩
  apply planeProductCoordinates.injective
  rw [map_smul]
  ext
  · change (planeProductCoordinates q).1 = t*(planeProductCoordinates p).1
    dsimp [t]
    have hp0 : (planeProductCoordinates p).1 ≠ 0 := hp.ne'
    field_simp
  · change (planeProductCoordinates q).2 = t*(planeProductCoordinates p).2
    change (planeProductCoordinates p).1⁻¹*(planeProductCoordinates p).2 =
      (planeProductCoordinates q).1⁻¹*(planeProductCoordinates q).2 at hsl
    have hp0 : (planeProductCoordinates p).1 ≠ 0 := hp.ne'
    have hq0 : (planeProductCoordinates q).1 ≠ 0 := hq.ne'
    dsimp [t]
    field_simp at hsl ⊢
    nlinarith [hsl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarNormalRotation (n : Plane) : Plane ≃ₗᵢ[ℝ] Plane :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.single 0 1 - n))ᗮ

lemma planarNormalRotation_axis {n : Plane} (hn : ‖n‖ = 1) :
    planarNormalRotation n (EuclideanSpace.single 0 1) = n := by
  apply Submodule.reflection_sub
  simpa using hn.symm

lemma planarNormalRotation_radial {n : Plane} (hn : ‖n‖ = 1) (p : Plane) :
    (planarWedgeCoordinates ((planarNormalRotation n).symm p)).1 = ⟪n,p⟫ := by
  change (planeProductCoordinates ((planarNormalRotation n).symm p)).1 = _
  rw [planeProductCoordinates_apply]
  conv_rhs => lhs; rw [← planarNormalRotation_axis hn]
  conv_rhs => rhs; rw [← (planarNormalRotation n).apply_symm_apply p]
  rw [(planarNormalRotation n).inner_map_map]
  simp [EuclideanSpace.inner_single_left]

lemma planar_common_hemisphere_or_collinear {p q : Plane} (hp : p ≠ 0) (hq : q ≠ 0) :
    (∃ t : ℝ, q = t • p) ∨ ∃ n : Plane, ‖n‖ = 1 ∧ 0 < ⟪n,p⟫ ∧ 0 < ⟪n,q⟫ := by
  let u : Plane := ‖p‖⁻¹ • p
  let v : Plane := ‖q‖⁻¹ • q
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)), inv_mul_cancel₀ hpn.ne']
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg q)), inv_mul_cancel₀ hqn.ne']
  have hpu : p = ‖p‖ • u := by dsimp [u]; rw [smul_smul,mul_inv_cancel₀ hpn.ne',one_smul]
  have hqv : q = ‖q‖ • v := by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hqn.ne',one_smul]
  by_cases hz : u+v=0
  · left
    refine ⟨-‖q‖*‖p‖⁻¹,?_⟩
    have hvu : v = -u := eq_neg_of_add_eq_zero_right hz
    calc
      q = ‖q‖ • v := hqv
      _ = -‖q‖ • u := by rw [hvu,smul_neg,neg_smul]
      _ = (-‖q‖*‖p‖⁻¹) • p := by dsimp [u]; rw [smul_smul]
  · right
    let n : Plane := ‖u+v‖⁻¹ • (u+v)
    have hw : 0 < ‖u+v‖ := norm_pos_iff.mpr hz
    have hinner : 0 < 1+⟪u,v⟫ := by
      have he := norm_add_sq_real u v
      rw [hu,hv] at he
      nlinarith [sq_pos_of_pos hw]
    refine ⟨n,?_,?_,?_⟩
    · dsimp [n]
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hw.ne']
    · rw [hpu]
      dsimp [n]
      rw [real_inner_smul_left,inner_smul_right,inner_add_left,real_inner_self_eq_norm_sq,real_inner_comm u v,hu]
      exact mul_pos (inv_pos.mpr hw) (mul_pos hpn (by simpa using hinner))
    · rw [hqv]
      dsimp [n]
      rw [real_inner_smul_left,inner_smul_right,inner_add_left,real_inner_self_eq_norm_sq,hv]
      exact mul_pos (inv_pos.mpr hw) (mul_pos hqn (by simpa [add_comm] using hinner))

theorem planar_cone_boundary_collinear {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    {p q : Plane} (hp : p ∈ planarEssentialBoundary C) (hq : q ∈ planarEssentialBoundary C)
    (hpb : p ∈ Metric.ball (0 : Plane) (1/16)) (hqb : q ∈ Metric.ball (0 : Plane) (1/16))
    (hp0 : p ≠ 0) : ∃ t : ℝ, q = t • p := by
  by_cases hq0 : q = 0
  · exact ⟨0,by simp [hq0]⟩
  rcases planar_common_hemisphere_or_collinear hp0 hq0 with hh|⟨n,hn,hpn,hqn⟩
  · exact hh
  let R := planarNormalRotation n
  have hpr : 0 < (planarWedgeCoordinates (R.symm p)).1 := by
    rw [planarNormalRotation_radial hn]; exact hpn
  have hqr : 0 < (planarWedgeCoordinates (R.symm q)).1 := by
    rw [planarNormalRotation_radial hn]; exact hqn
  obtain ⟨t,_,he⟩ := planar_equal_positive_slopes_collinear hpr hqr
    (planar_cone_boundary_chart_unique_slope hc hcharts hp hq hpb hqb R hpr hqr)
  refine ⟨t,?_⟩
  have he' := congrArg R he
  simpa only [R.apply_symm_apply,map_smul] using he'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem connected_planar_phase {D s : Set Plane} (hD : MeasurableSet D)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (planarEssentialBoundary D)) :
    volume (s ∩ D) = 0 ∨ volume (s ∩ Dᶜ) = 0 := by
  let U := (volume.restrict D).supportᶜ
  let W := (volume.restrict Dᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict D).support ∪ (volume.restrict Dᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hD,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict D).supportᶜ ∩ (volume.restrict Dᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    have hx' : x ∉ planarEssentialBoundary D := fun hb ↦ Set.disjoint_left.mp hd hx hb
    rw [planarEssentialBoundary] at hx'
    exact not_and_or.mp hx'
  have hnullD (h : s ⊆ U) : volume (s ∩ D) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Dᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullD (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

lemma planar_punctured_ball_preconnected {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball (0 : Plane) r \ {0}) := by
  let f := OpenPartialHomeomorph.univBall (0 : Plane) r
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane]
  have hc := (isConnected_compl_singleton_of_one_lt_rank hrank (0 : Plane)).isPreconnected
  have hi : f '' ({0}ᶜ : Set Plane) = Metric.ball (0 : Plane) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target (0 : Plane) hr]
        exact f.map_source (by simp [f])
      · intro he
        have he0 : f x = 0 := he
        have hh := congrArg f.symm he0
        rw [f.left_inv (by simp [f]),OpenPartialHomeomorph.univBall_symm_apply_center] at hh
        exact hx hh
    · rintro ⟨hy,hy0⟩
      have hyt : y ∈ f.target := by rwa [OpenPartialHomeomorph.univBall_target _ hr]
      refine ⟨f.symm y,?_,f.right_inv hyt⟩
      intro hz
      have hz' : f.symm y = 0 := hz
      have hh := congrArg f hz'
      rw [f.right_inv hyt,OpenPartialHomeomorph.univBall_apply_zero] at hh
      exact hy0 hh
  rw [← hi]
  exact hc.image f (OpenPartialHomeomorph.continuous_univBall (0 : Plane) r).continuousOn

theorem planar_boundary_nonzero {C : Set Plane} (hC : MeasurableSet C)
    {r : ℝ} (hr : 0 < r)
    (hpos : 0 < volume (Metric.ball (0 : Plane) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) r ∩ Cᶜ)) :
    ∃ p : Plane, p ∈ Metric.ball (0 : Plane) r ∧ p ≠ 0 ∧ p ∈ planarEssentialBoundary C := by
  by_contra he
  have hd : Disjoint (Metric.ball (0 : Plane) r \ {0}) (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro x hx hb
    exact he ⟨x,hx.1,hx.2,hb⟩
  have hnull (A : Set Plane) (h : volume ((Metric.ball (0 : Plane) r \ {0}) ∩ A) = 0) :
      volume (Metric.ball (0 : Plane) r ∩ A) = 0 := by
    apply measure_mono_null (t := ((Metric.ball (0 : Plane) r \ {0}) ∩ A) ∪ {0}) ?_
      (measure_union_null h (measure_singleton 0))
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inr hx0
    · exact Or.inl ⟨⟨hx.1,hx0⟩,hx.2⟩
  rcases connected_planar_phase hC (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0))
    (planar_punctured_ball_preconnected hr) hd with hh|hh
  · exact (ne_of_gt hpos) (hnull C hh)
  · exact (ne_of_gt hneg) (hnull Cᶜ hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_hyperplane_volume_zero {n : Plane} (hn : n ≠ 0) :
    volume {y : Plane | ⟪n,y⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n,n⟫ = 0 at hm
  exact hn (inner_self_eq_zero.mp hm)

lemma planar_halfballs_null {A : Set Plane} {n : Plane} (hn : n ≠ 0) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) = 0)
    (hr : volume ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) = 0) :
    volume (Metric.ball (0 : Plane) r ∩ A) = 0 := by
  apply measure_mono_null (t := ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) ∪
    ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) ∪ {y | ⟪n,y⟫ = 0}) ?_
    (measure_union_null (measure_union_null hl hr) (planar_hyperplane_volume_zero hn))
  intro y hy
  rcases lt_trichotomy ⟪n,y⟫ 0 with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨hy.1,hh⟩,hy.2⟩)
  · exact Or.inr hh
  · exact Or.inl (Or.inr ⟨⟨hy.1,hh⟩,hy.2⟩)

lemma planar_opposite_halfballs_model {C : Set Plane} {n : Plane} (hn : n ≠ 0) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) = 0)
    (hr : volume ((Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) = 0) :
    ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) r → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  have hal : ∀ᵐ y : Plane ∂volume, ¬(y ∈ (Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hl
  have har : ∀ᵐ y : Plane ∂volume, ¬(y ∈ (Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hr
  have han : ∀ᵐ y : Plane ∂volume, ⟪n,y⟫ ≠ 0 := by
    simpa only [ae_iff,not_not] using planar_hyperplane_volume_zero hn
  filter_upwards [hal,har,han] with y hl hr hne hy
  constructor
  · intro hc
    by_contra hpos
    exact hl ⟨⟨hy,lt_of_le_of_ne (not_lt.mp hpos) hne⟩,hc⟩
  · intro hpos
    by_contra hnc
    exact hr ⟨⟨hy,hpos⟩,hnc⟩

theorem planar_boundary_line_halfplane {C : Set Plane} (hC : MeasurableSet C)
    {r : ℝ} {n : Plane} (hn : n ≠ 0)
    (hbd : ∀ y : Plane, y ∈ Metric.ball (0 : Plane) r → y ∈ planarEssentialBoundary C → ⟪n,y⟫ = 0)
    (hpos : 0 < volume (Metric.ball (0 : Plane) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) r ∩ Cᶜ)) :
    ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) r → (y ∈ C ↔ 0 < ⟪m,y⟫) := by
  let U := Metric.ball (0 : Plane) r ∩ {y | ⟪n,y⟫ < 0}
  let W := Metric.ball (0 : Plane) r ∩ {y | 0 < ⟪n,y⟫}
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet
  have hW : MeasurableSet W := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt continuous_const (innerSL ℝ n).continuous).measurableSet
  have hcU : IsPreconnected U := ((convex_ball (0 : Plane) r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hcW : IsPreconnected W := ((convex_ball (0 : Plane) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hdU : Disjoint U (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_lt hy.2) (hbd y hy.1 he)
  have hdW : Disjoint W (planarEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_gt hy.2) (hbd y hy.1 he)
  rcases connected_planar_phase hC hU hcU hdU with hu|hu <;>
    rcases connected_planar_phase hC hW hcW hdW with hw|hw
  · exact ((ne_of_gt hpos) (planar_halfballs_null hn hu hw)).elim
  · exact ⟨n,hn,planar_opposite_halfballs_model hn hu hw⟩
  · refine ⟨-n,neg_ne_zero.mpr hn,?_⟩
    apply planar_opposite_halfballs_model (neg_ne_zero.mpr hn)
    · simpa only [inner_neg_left,neg_lt_zero] using hw
    · simpa only [inner_neg_left,neg_pos] using hu
  · exact ((ne_of_gt hneg) (planar_halfballs_null hn hu hw)).elim

lemma exists_planar_perpendicular {p : Plane} (hp : p ≠ 0) :
    ∃ n : Plane, n ≠ 0 ∧ ⟪n,p⟫ = 0 := by
  let n : Plane := EuclideanSpace.single 0 (-p 1) + EuclideanSpace.single 1 (p 0)
  refine ⟨n,?_,?_⟩
  · intro hn
    have h0 := congrArg (fun y : Plane ↦ y 0) hn
    have h1 := congrArg (fun y : Plane ↦ y 1) hn
    simp [n] at h0 h1
    apply hp
    ext i
    fin_cases i <;> simp_all
  · dsimp [n]
    rw [inner_add_left,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_left]
    simp only [starRingEnd_apply,star_trivial]
    ring

theorem planar_cone_halfplane_of_single_transition {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hcharts : ∀ (R : Plane ≃ₗᵢ[ℝ] Plane) (w : ℝ), 0 < w →
      ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
        (Ioo (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Subsingleton ∧
        ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
          |(planarWedgeCoordinates y).2| < w →
          (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D))
    (hpos : 0 < volume (Metric.ball (0 : Plane) (1/16) ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Plane) (1/16) ∩ Cᶜ)) :
    ∃ n : Plane, n ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  obtain ⟨p,hpb,hp0,hp⟩ := planar_boundary_nonzero hC (by norm_num : (0 : ℝ)<1/16) hpos hneg
  obtain ⟨n,hn,hnp⟩ := exists_planar_perpendicular hp0
  apply planar_boundary_line_halfplane hC hn ?_ hpos hneg
  intro y hy hb
  obtain ⟨t,rfl⟩ := planar_cone_boundary_collinear hc hcharts hp hb hpb hy hp0
  rw [inner_smul_right,hnp,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_volumeSupport_in_ball {E : Set Torus} {a : Torus} {r : ℝ}
    (hpos : 0 < torusVolume.real (E ∩ Metric.ball a r)) :
    ∃ b ∈ Metric.ball a r, b ∈ volumeSupport E := by
  have hm : (torusVolume.restrict E) (Metric.ball a r) ≠ 0 := by
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet,inter_comm]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hpos).1
  exact Measure.exists_mem_of_measure_ne_zero_of_ae hm
    (ae_restrict_of_ae (Measure.support_mem_ae (μ := torusVolume.restrict E)))

lemma isMinimizerAt_positive_ball_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ R b : ℝ, 0 < R ∧ 0 < b ∧ ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      0 < torusVolume.real (E ∩ Metric.ball a (r/2)) →
      b*r^3 ≤ torusVolume.real (E ∩ Metric.ball a r) := by
  obtain ⟨R,c,hR,hc,hden⟩ := isMinimizerAt_volume_density hV hE hmin
  refine ⟨R,c/8,hR,by positivity,?_⟩
  intro a r hr hrR hp
  obtain ⟨z,hz,hzs⟩ := exists_volumeSupport_in_ball hp
  have hb : Metric.ball z (r/2) ⊆ Metric.ball a r := by
    intro x hx
    have htri := dist_triangle x z a
    have hh : dist z a < r/2 := hz
    have hx' : dist x z < r/2 := hx
    change dist x a < r
    linarith
  have hd := hden z (r/2) (half_pos hr) (by linarith) ((mem_volumeSupport_iff E z).mp hzs)
  have hm := measureReal_mono (μ := torusVolume) (inter_subset_inter_left E hb)
  calc
    (c/8)*r^3 = c*(r/2)^3 := by ring
    _ ≤ torusVolume.real (E ∩ Metric.ball z (r/2)) := hd
    _ ≤ _ := by simpa only [inter_comm] using hm

lemma integral_indicator_ball_real (A : Set Cover) (hA : MeasurableSet A) (ρ : ℝ) :
    (∫ x in Metric.ball (0 : Cover) ρ, A.indicator (fun _ ↦ (1 : ℝ)) x) =
      volume.real (A ∩ Metric.ball (0 : Cover) ρ) := by
  rw [integral_indicator hA, Measure.restrict_restrict hA,integral_const,
    smul_eq_mul,mul_one,Measure.real_def,Measure.restrict_apply_univ]
  rfl

theorem isMinimizerAt_moving_limit_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ b : ℝ, 0 < b ∧ ∀ c : ℕ → MovingCenter.InteriorCenter,
      ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ R : ℝ, ∀ A : Set Cover, MeasurableSet A →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
        0 < volume.real (A ∩ Metric.ball (0 : Cover) (ρ/2)) →
        b*ρ^3 ≤ volume.real (A ∩ Metric.ball (0 : Cover) ρ) := by
  obtain ⟨S,b,hS,hb,hd⟩ := isMinimizerAt_positive_ball_density hV hE hmin
  refine ⟨b,hb,?_⟩
  intro c r hr hrlim R A hA hconv ρ hρ hρR hpos
  have hint := localL1_ball_integral_tendsto hρR
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv
  have hint2 := localL1_ball_integral_tendsto (show ρ/2 ≤ R by linarith)
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv
  rw [integral_indicator_ball_real A hA ρ] at hint
  rw [integral_indicator_ball_real A hA (ρ/2)] at hint2
  have he : ∀ᶠ i in atTop, r i*ρ < min S (1/4) := by
    have hh := hrlim.mul_const ρ
    rw [zero_mul] at hh
    exact hh.eventually (gt_mem_nhds (lt_min hS (by norm_num)))
  have hpe : ∀ᶠ i in atTop,
      0 < ∫ x in Metric.ball (0 : Cover) (ρ/2), blowupCharacteristic E (c i) (r i) x :=
    hint2.eventually (lt_mem_nhds hpos)
  apply ge_of_tendsto hint
  filter_upwards [he,hpe] with i hi hip
  have hc : Metric.ball (c i : Cover) (r i*ρ) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior
      (by linarith [hi.trans_le (min_le_right S (1/4))] : r i*ρ < 3/8))
  have hc2 : Metric.ball (c i : Cover) (r i*(ρ/2)) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.ball_subset_ball (by nlinarith [hr i])).trans hc
  have hp : 0 < torusVolume.real (E ∩ Metric.ball (quotientMap (c i)) ((r i*ρ)/2)) := by
    rw [show (r i*ρ)/2 = r i*(ρ/2) by ring,
      integral_blowupCharacteristic_ball hE (c i) (hr i) (ρ/2) hc2]
    exact mul_pos (pow_pos (hr i) 3) hip
  have hh := hd (quotientMap (c i)) (r i*ρ) (mul_pos (hr i) hρ)
    (hi.trans_le (min_le_left _ _)).le hp
  rw [integral_blowupCharacteristic_ball hE (c i) (hr i) ρ hc] at hh
  apply (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp
  calc
    _ = b*(r i*ρ)^3 := by ring
    _ ≤ _ := hh
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_real_translate_ball {A : Set Cover} (hA : MeasurableSet A) (p : Cover) (ρ : ℝ) :
    volume.real (((fun x ↦ p+x) ⁻¹' A) ∩ Metric.ball (0 : Cover) ρ) =
      volume.real (A ∩ Metric.ball p ρ) := by
  have he (D : Set Cover) (hD : MeasurableSet D) (a : Cover) :
      (∫ x in Metric.ball a ρ, D.indicator (fun _ ↦ (1 : ℝ)) x) =
        volume.real (D ∩ Metric.ball a ρ) := by
    rw [integral_indicator hD,Measure.restrict_restrict hD,integral_const,smul_eq_mul,mul_one,
      Measure.real_def,Measure.restrict_apply_univ]
    rfl
  have hD : MeasurableSet ((fun x : Cover ↦ p+x) ⁻¹' A) :=
    hA.preimage (measurable_const.add measurable_id)
  rw [← he A hA p,← he _ hD 0]
  have hh := integral_ball_affine_scaling (A.indicator (fun _ ↦ (1 : ℝ))) p (by norm_num : (0 : ℝ)<1) ρ
  simp only [one_mul,one_pow,one_smul] at hh
  rw [hh]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  classical
  by_cases hx : p+x ∈ A <;> simp [hx]

theorem isMinimizerAt_primary_limit_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ p : Cover, ‖p‖ < 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        0 < volume.real (A ∩ Metric.ball p (ρ/2)) →
        b*ρ^3 ≤ volume.real (A ∩ Metric.ball p ρ) := by
  obtain ⟨b,hb,hd⟩ := isMinimizerAt_moving_limit_density hV hE hmin
  refine ⟨b,hb,?_⟩
  intro r hr hrlim A hA hconv p hp ρ hρ hρ1 hpos
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/8)))
  let c : ℕ → MovingCenter.InteriorCenter := fun i ↦ ⟨cubeCenter+r (i+k) • p,by
    simp only [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := hk (i+k) (by omega)
    nlinarith [hr (i+k)]⟩
  let D : Set Cover := (fun x ↦ p+x) ⁻¹' A
  have hD : MeasurableSet D := hA.preimage (measurable_const.add measurable_id)
  have hsub : Metric.closedBall p (1*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm,one_mul] using hx
    have hh := norm_add_le (x-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 2)
  have hshift := localL1_affine_tendsto
    (fun i ↦ measurable_blowupCharacteristic hE cubeCenter (r i))
    (fun i ↦ blowupCharacteristic_bound E cubeCenter (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv p
    (by norm_num : (0 : ℝ)<1) hsub
  have hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r (i+k)) x-D.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
    have hh := hshift.comp (tendsto_add_atTop_nat k)
    convert hh using 2
    rename_i i
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change |blowupCharacteristic E (cubeCenter+r (i+k) • p) (r (i+k)) x-
      D.indicator (fun _ ↦ (1 : ℝ)) x| =
      |blowupCharacteristic E cubeCenter (r (i+k)) (p+1 • x)-A.indicator (fun _ ↦ (1 : ℝ)) (p+1 • x)|
    rw [blowupCharacteristic_affine]
    simp only [mul_one,one_smul]
    congr 2
  have hpD : 0 < volume.real (D ∩ Metric.ball (0 : Cover) (ρ/2)) := by
    rwa [volume_real_translate_ball hA]
  have hh := hd c (fun i ↦ r (i+k)) (fun i ↦ hr _) (hrlim.comp (tendsto_add_atTop_nat k))
    1 D hD hlim ρ hρ hρ1 hpD
  rwa [volume_real_translate_ball hA] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_indicator_compl (A : Set Cover) (x : Cover) :
    Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x = 1-A.indicator (fun _ ↦ (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ A <;> simp [hx]

lemma blowupCharacteristic_compl (E : Set Torus) (c : Cover) (r : ℝ) (x : Cover) :
    blowupCharacteristic Eᶜ c r x = 1-blowupCharacteristic E c r x := by
  classical
  by_cases hx : quotientMap (c+r • x) ∈ E <;> simp [blowupCharacteristic,characteristic,hx]

lemma complement_blowup_error (E : Set Torus) (A : Set Cover) (c x : Cover) (r : ℝ) :
    |blowupCharacteristic Eᶜ c r x-Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x| =
      |blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x| := by
  rw [blowupCharacteristic_compl,cover_indicator_compl]
  rw [show 1-blowupCharacteristic E c r x-(1-A.indicator (fun _ ↦ (1 : ℝ)) x) =
    -(blowupCharacteristic E c r x-A.indicator (fun _ ↦ (1 : ℝ)) x) by ring,abs_neg]

lemma complement_cover_error (A B : Set Cover) (x y : Cover) :
    |Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x-Bᶜ.indicator (fun _ ↦ (1 : ℝ)) y| =
      |A.indicator (fun _ ↦ (1 : ℝ)) x-B.indicator (fun _ ↦ (1 : ℝ)) y| := by
  rw [cover_indicator_compl,cover_indicator_compl]
  rw [show 1-A.indicator (fun _ ↦ (1 : ℝ)) x-(1-B.indicator (fun _ ↦ (1 : ℝ)) y) =
    -(A.indicator (fun _ ↦ (1 : ℝ)) x-B.indicator (fun _ ↦ (1 : ℝ)) y) by ring,abs_neg]

theorem secondary_limit_volume_density {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (p : Cover) {b : ℝ}
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → b*ρ^3 ≤ volume.real (A ∩ Metric.ball p ρ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) := by
  have hint := localL1_ball_integral_tendsto hρ1
    (fun i x ↦ A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x))
    (fun i ↦ (measurable_const.indicator hA).comp (measurable_const.add (measurable_const_smul (r i))))
    (fun i x ↦ cover_indicator_bound A _)
    (measurable_const.indicator hB) (cover_indicator_bound B) hconv
  rw [integral_indicator_ball_real B hB ρ] at hint
  have he : ∀ᶠ i in atTop, r i*ρ ≤ 1 := by
    have hh := hrlim.mul_const ρ
    rw [zero_mul] at hh
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))).mono (fun _ hi ↦ hi.le)
  apply ge_of_tendsto hint
  filter_upwards [he] with i hi
  have hh := hden (r i*ρ) (mul_pos (hr i) hρ) hi
  have hv : volume.real (A ∩ Metric.ball p (r i*ρ)) =
      (r i)^3*∫ x in Metric.ball (0 : Cover) ρ,
        A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x) := by
    rw [← integral_ball_affine_scaling _ p (hr i) ρ,
      integral_indicator hA,Measure.restrict_restrict hA,integral_const,smul_eq_mul,mul_one,
      Measure.real_def]
    simp only [Measure.real_def,Measure.restrict_apply_univ]
  rw [hv] at hh
  apply (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp
  calc
    _ = b*(r i*ρ)^3 := by ring
    _ ≤ _ := hh
    _ = _ := by ring

theorem isMinimizerAt_secondary_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ p : Cover, ‖p‖ < 1 →
      (∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
        0 < volume.real (Aᶜ ∩ Metric.ball p δ)) →
      ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) →
      ∀ B : Set Cover, MeasurableSet B →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
        b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ) := by
  obtain ⟨b,hb,hd⟩ := isMinimizerAt_primary_limit_density hV hE hmin
  have hVc : 1-V ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  obtain ⟨d,hdpos,hden⟩ := isMinimizerAt_primary_limit_density hVc hE.compl
    ((isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin)
  refine ⟨min b d,lt_min hb hdpos,?_⟩
  intro r hr hrlim A hA hconv p hp hsupport s hs hslim B hB hconvB ρ hρ hρ1
  have hconvAc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic Eᶜ cubeCenter (r i) x-Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
    simpa only [complement_blowup_error] using hconv
  have hconvBc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |Aᶜ.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-Bᶜ.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
    simpa only [complement_cover_error] using hconvB
  have hbd := secondary_limit_volume_density hA hB p
    (fun δ hδ hδ1 ↦ hd r hr hrlim A hA hconv p hp δ hδ hδ1 (hsupport (δ/2) (half_pos hδ)).1)
    s hs hslim hconvB ρ hρ hρ1
  have hdd := secondary_limit_volume_density hA.compl hB.compl p
    (fun δ hδ hδ1 ↦ hden r hr hrlim Aᶜ hA.compl hconvAc p hp δ hδ hδ1 (hsupport (δ/2) (half_pos hδ)).2)
    s hs hslim hconvBc ρ hρ hρ1
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hρ.le 3)).trans hbd,
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hρ.le 3)).trans hdd⟩

end CubicTorus

end
end

end

end OAI
