import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVPlanarAngularChart

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma planar_cone_rotation {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ R ⁻¹' C ↔ y ∈ R ⁻¹' C) := by
  intro t ht
  filter_upwards [R.measurePreserving.quasiMeasurePreserving.ae (hc t ht)] with y hy hyb
  have hRy : R y ∈ Metric.ball (0 : Plane) (1/16) := by
    simpa only [Metric.mem_ball,dist_zero_right,R.norm_map] using hyb
  simpa only [Set.mem_preimage,R.map_smul] using hy hRy

lemma planar_directional_bv_rotation {C : Set Plane} {K : ℝ}
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in R ⁻¹' C, fderiv ℝ φ y u| ≤ K := by
  intro φ hφ hs hb u hu
  let ψ : Plane → ℝ := φ ∘ R.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp R.symm.toContinuousLinearEquiv.contDiff
  have hsψ : tsupport ψ ⊆ Metric.closedBall (0 : Plane) (1/32) := by
    rw [show ψ = φ ∘ R.symm.toHomeomorph from rfl,tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simp only [Metric.mem_closedBall,dist_zero_right] at hh
    change ‖R.symm y‖ ≤ 1/32 at hh
    simpa only [Metric.mem_closedBall,dist_zero_right,R.symm.norm_map] using hh
  have hd (y : Plane) : fderiv ℝ ψ (R y) (R u) = fderiv ℝ φ y u := by
    have he := ((hφ.differentiable (by simp)) (R.symm (R y))).hasFDerivAt.comp (R y)
      R.symm.toContinuousLinearEquiv.hasFDerivAt
    have h := congrArg (fun A : Plane →L[ℝ] ℝ ↦ A (R u)) he.fderiv
    change fderiv ℝ ψ (R y) (R u) = fderiv ℝ φ (R.symm (R y)) (R.symm (R u)) at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  have he := R.measurePreserving.setIntegral_preimage_emb R.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y ↦ fderiv ℝ ψ y (R u)) C
  simp_rw [hd] at he
  rw [he]
  exact hbv ψ hψ hsψ (fun y ↦ hb _) (R u) (by simpa using hu)

theorem planar_cone_finite_angular_transitions_rotated {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∃ (a b : ℝ) (D : Set ℝ), 0 < a ∧ a < b ∧ MeasurableSet D ∧
      (∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
        (R (planarWedgeChart z) ∈ C ↔ z.2 ∈ D)) ∧
      (Icc (-(1/4 : ℝ)) (1/4) ∩ angularEssentialBoundary D).Finite :=
  planar_cone_finite_angular_transitions (hC.preimage R.continuous.measurable)
    (planar_cone_rotation hc R) hK (planar_directional_bv_rotation hbv R)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma ae_not_phase_of_inter_null {A D : Set ℝ} (h : volume (A ∩ D) = 0) :
    ∀ᵐ t : ℝ ∂volume, t ∈ A → t ∉ D :=
  (measure_eq_zero_iff_ae_notMem.mp h).mono (fun _ ht ha hd ↦ ht ⟨ha,hd⟩)

lemma ae_phase_of_inter_compl_null {A D : Set ℝ} (h : volume (A ∩ Dᶜ) = 0) :
    ∀ᵐ t : ℝ ∂volume, t ∈ A → t ∈ D := by
  filter_upwards [ae_not_phase_of_inter_null h] with t ht ha
  exact not_not.mp (ht ha)

theorem angular_finite_local_model {D : Set ℝ} (hD : MeasurableSet D)
    (hfin : (Icc (-(1/4 : ℝ)) (1/4) ∩ angularEssentialBoundary D).Finite) :
    ∃ (δ : ℝ) (S : Set ℝ), 0 < δ ∧ δ ≤ 1 ∧
      (S = ∅ ∨ S = univ ∨ S = Ioi (0 : ℝ) ∨ S = Iio (0 : ℝ)) ∧
      ∀ᵐ t : ℝ ∂volume, |t| < δ → (t ∈ D ↔ t ∈ S) := by
  have shrink {δ : ℝ} (hδ : 0 < δ) (S : Set ℝ)
      (hS : S = ∅ ∨ S = univ ∨ S = Ioi (0 : ℝ) ∨ S = Iio (0 : ℝ))
      (h : ∀ᵐ t : ℝ ∂volume, |t| < δ → (t ∈ D ↔ t ∈ S)) :
      ∃ (δ : ℝ) (S : Set ℝ), 0 < δ ∧ δ ≤ 1 ∧
        (S = ∅ ∨ S = univ ∨ S = Ioi (0 : ℝ) ∨ S = Iio (0 : ℝ)) ∧
        ∀ᵐ t : ℝ ∂volume, |t| < δ → (t ∈ D ↔ t ∈ S) := by
    exact ⟨min δ 1,S,lt_min hδ (by norm_num),min_le_right _ _,hS,
      h.mono (fun _ ht hb ↦ ht (hb.trans_le (min_le_left _ _)))⟩
  by_cases hx : (0 : ℝ) ∈ angularEssentialBoundary D
  · obtain ⟨δ,hδ,he⟩ := finite_angular_transition_is_jump hD hfin
      (show (0 : ℝ) ∈ Ioo (-(1/4 : ℝ)) (1/4) by constructor <;> norm_num) hx
    have hn : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by rw [ae_iff]; simp
    rcases he with he|he
    · apply shrink hδ (Ioi 0) (Or.inr (Or.inr (Or.inl rfl)))
      filter_upwards [ae_not_phase_of_inter_null he.1,ae_phase_of_inter_compl_null he.2,hn]
        with t hL hR ht hb
      have hl := (abs_lt.mp hb).1
      have hr := (abs_lt.mp hb).2
      rcases lt_or_gt_of_ne ht with ht|ht
      · have hh := hL (show t ∈ Ioo (0-δ) 0 by constructor <;> linarith)
        simp only [Set.mem_Ioi]
        exact iff_of_false hh (not_lt_of_ge ht.le)
      · have hh := hR (show t ∈ Ioo 0 (0+δ) by constructor <;> linarith)
        exact iff_of_true hh ht
    · apply shrink hδ (Iio 0) (Or.inr (Or.inr (Or.inr rfl)))
      filter_upwards [ae_phase_of_inter_compl_null he.1,ae_not_phase_of_inter_null he.2,hn]
        with t hL hR ht hb
      have hl := (abs_lt.mp hb).1
      have hr := (abs_lt.mp hb).2
      rcases lt_or_gt_of_ne ht with ht|ht
      · have hh := hL (show t ∈ Ioo (0-δ) 0 by constructor <;> linarith)
        exact iff_of_true hh ht
      · have hh := hR (show t ∈ Ioo 0 (0+δ) by constructor <;> linarith)
        simp only [Set.mem_Iio]
        exact iff_of_false hh (not_lt_of_ge ht.le)
  · change ¬ ∀ δ : ℝ, 0 < δ → 0 < volume (D ∩ Metric.ball 0 δ) ∧
      0 < volume (Dᶜ ∩ Metric.ball 0 δ) at hx
    push Not at hx
    obtain ⟨δ,hδ,hnull⟩ := hx
    by_cases hfirst : volume (D ∩ Metric.ball (0 : ℝ) δ) = 0
    · apply shrink hδ ∅ (Or.inl rfl)
      have he : volume (Metric.ball (0 : ℝ) δ ∩ D) = 0 := by
        rw [inter_comm]; exact hfirst
      filter_upwards [ae_not_phase_of_inter_null he] with t ht hb
      exact iff_of_false (ht (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hb))
        (Set.notMem_empty t)
    · have hnull := hnull (lt_of_le_of_ne bot_le (Ne.symm hfirst))
      apply shrink hδ univ (Or.inr (Or.inl rfl))
      have he : volume (Metric.ball (0 : ℝ) δ ∩ Dᶜ) = 0 := by
        rw [inter_comm]; exact le_antisymm hnull bot_le
      filter_upwards [ae_phase_of_inter_compl_null he] with t ht hb
      exact iff_of_true (ht (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hb))
        (Set.mem_univ t)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma triangular_inv_mul_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ (z.1,z.1⁻¹*z.2)) volume volume := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ (z.1,z.1⁻¹*z.2)) :=
    measurable_fst.prodMk (measurable_fst.inv.mul measurable_snd)
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun S hS hS0 ↦ ?_)⟩
  rw [Measure.map_apply hm hS,Measure.volume_eq_prod,Measure.prod_apply (hm hS)]
  have hnull : ∀ᵐ x : ℝ ∂volume, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0 := by
    apply (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).mp
    simpa only [← Measure.prod_apply hS,← Measure.volume_eq_prod] using hS0
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  change (∫⁻ x : ℝ, (volume : Measure ℝ) ((fun y : ℝ ↦ (x,x⁻¹*y)) ⁻¹' S)) = 0
  rw [lintegral_congr_ae (show (fun x : ℝ ↦ (volume : Measure ℝ)
      ((fun y : ℝ ↦ (x,x⁻¹*y)) ⁻¹' S)) =ᵐ[volume] 0 from ?_)]
  · simp
  filter_upwards [hnull,hn] with x hx hx0
  exact (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hx0)).preimage_null hx

def planarWedgeCoordinates (y : Plane) : ℝ × ℝ :=
  ((planeProductCoordinates y).1,(planeProductCoordinates y).1⁻¹*(planeProductCoordinates y).2)

lemma planarWedgeCoordinates_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving planarWedgeCoordinates volume volume :=
  triangular_inv_mul_quasiMeasurePreserving.comp
    planeProductCoordinates_measurePreserving.quasiMeasurePreserving

lemma planarWedgeChart_coordinates {y : Plane} (hy : (planeProductCoordinates y).1 ≠ 0) :
    planarWedgeChart (planarWedgeCoordinates y) = y := by
  unfold planarWedgeCoordinates planarWedgeChart
  simp only [mul_inv_cancel_left₀ hy,Prod.mk.eta,ContinuousLinearEquiv.symm_apply_apply]

lemma planarWedgeCoordinates_chart {s t : ℝ} (hs : s ≠ 0) :
    planarWedgeCoordinates (planarWedgeChart (s,t)) = (s,t) := by
  simp only [planarWedgeCoordinates,planarWedgeChart,ContinuousLinearEquiv.apply_symm_apply,
    inv_mul_cancel_left₀ hs]

theorem planar_cone_local_slope_model {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∃ (a b δ : ℝ) (S : Set ℝ), 0 < a ∧ a < b ∧ 0 < δ ∧ δ ≤ 1 ∧
      (S = ∅ ∨ S = univ ∨ S = Ioi (0 : ℝ) ∨ S = Iio (0 : ℝ)) ∧
      ∀ᵐ y : Plane ∂volume,
        (planarWedgeCoordinates (R.symm y)).1 ∈ Ioo a b →
        |(planarWedgeCoordinates (R.symm y)).2| < δ →
        (y ∈ C ↔ (planarWedgeCoordinates (R.symm y)).2 ∈ S) := by
  obtain ⟨a,b,D,ha,hab,hD,hprod,hfin⟩ :=
    planar_cone_finite_angular_transitions_rotated hC hc hK hbv R
  obtain ⟨δ,S,hδ,hδ1,hS,hmodel⟩ := angular_finite_local_model hD hfin
  have hmodP : ∀ᵐ z : ℝ × ℝ ∂volume, |z.2| < δ → (z.2 ∈ D ↔ z.2 ∈ S) := by
    simpa only [Measure.volume_eq_prod] using
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).ae hmodel
  have hboth : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → |z.2| < δ →
      (R (planarWedgeChart z) ∈ C ↔ z.2 ∈ S) := by
    filter_upwards [hprod,hmodP] with z hz hm hz1 hz2
    have hz2' : z.2 ∈ Ioo (-1 : ℝ) 1 := by
      have hh := abs_lt.mp hz2
      constructor <;> linarith [hh.1,hh.2]
    exact (hz hz1 hz2').trans (hm hz2)
  have hq := planarWedgeCoordinates_quasiMeasurePreserving.comp
    R.symm.measurePreserving.quasiMeasurePreserving
  refine ⟨a,b,δ,S,ha,hab,hδ,hδ1,hS,?_⟩
  filter_upwards [hq.ae hboth] with y hy hy1 hy2
  have hnot : (planeProductCoordinates (R.symm y)).1 ≠ 0 :=
    ne_of_gt (ha.trans hy1.1)
  have he : R (planarWedgeChart (planarWedgeCoordinates (R.symm y))) = y := by
    rw [planarWedgeChart_coordinates hnot,R.apply_symm_apply]
  have hh := hy hy1 hy2
  simp only [Function.comp_apply] at hh
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_apply (y : Plane) : planeProductCoordinates y = (y 0,y 1) := by
  simp [planeProductCoordinates,Complex.orthonormalBasisOneI]

lemma planeProductCoordinates_symm_apply (z : ℝ × ℝ) :
    planeProductCoordinates.symm z = WithLp.toLp 2 ![z.1,z.2] := by
  apply planeProductCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,planeProductCoordinates_apply]
  rfl

def coverPlaneCoordinates : Cover ≃L[ℝ] ℝ × Plane :=
  coverPrismCoordinates.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr planeProductCoordinates.symm)

lemma coverPlaneCoordinates_apply (x : Cover) :
    coverPlaneCoordinates x = (x 0,WithLp.toLp 2 ![x 1,x 2]) := by
  simp [coverPlaneCoordinates,coverPrismCoordinates_apply,planeProductCoordinates_symm_apply]

lemma coverPlaneCoordinates_norm_sq (x : Cover) :
    ‖x‖^2 = (coverPlaneCoordinates x).1^2 + ‖(coverPlaneCoordinates x).2‖^2 := by
  rw [coverPlaneCoordinates_apply,EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

def coverPlaneRotationCLE (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃L[ℝ] Cover :=
  (coverPlaneCoordinates.trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr R.toContinuousLinearEquiv)).trans coverPlaneCoordinates.symm

lemma coverPlaneRotationCLE_coordinates (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Cover) :
    coverPlaneCoordinates (coverPlaneRotationCLE R x) =
      ((coverPlaneCoordinates x).1,R (coverPlaneCoordinates x).2) := by
  simp [coverPlaneRotationCLE]

def coverPlaneRotation (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃ₗᵢ[ℝ] Cover :=
  { (coverPlaneRotationCLE R).toLinearEquiv with
    norm_map' := by
      intro x
      change ‖coverPlaneRotationCLE R x‖ = ‖x‖
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [coverPlaneCoordinates_norm_sq,coverPlaneCoordinates_norm_sq,
        coverPlaneRotationCLE_coordinates,R.norm_map] }

def swapPrismPlane : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1 : Fin 3) 2)

lemma swapPrismPlane_apply (x : Cover) :
    swapPrismPlane x = WithLp.toLp 2 ![x 0,x 2,x 1] := by
  ext i
  fin_cases i <;> norm_num [swapPrismPlane,LinearIsometryEquiv.piLpCongrLeft,Equiv.swap_apply_def,Fin.ext_iff]

def prismFrame (n : Cover) (R : Plane ≃ₗᵢ[ℝ] Plane) : Cover ≃ₗᵢ[ℝ] Cover :=
  (swapPrismPlane.trans (coverPlaneRotation R)).trans (normalRotation n)

lemma normalColumnChart_zero_coordinates (n : Cover) (x : Cover) :
    normalColumnChart 0 n (coverPlaneCoordinates x) = normalRotation n x := by
  rw [coverPlaneCoordinates_apply]
  change 0 + normalProductChart n (x 0,WithLp.ofLp (WithLp.toLp 2 ![x 1,x 2])) = _
  rw [zero_add,normalProductChart_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma prismFrame_apply (n : Cover) (R : Plane ≃ₗᵢ[ℝ] Plane) (x : Cover) :
    prismFrame n R x = normalColumnChart 0 n
      (x 0,R (planeProductCoordinates.symm (x 2,x 1))) := by
  change normalRotation n (coverPlaneRotationCLE R (swapPrismPlane x)) = _
  rw [← normalColumnChart_zero_coordinates,coverPlaneRotationCLE_coordinates,
    swapPrismPlane_apply,coverPlaneCoordinates_apply,planeProductCoordinates_symm_apply]
  rfl

lemma prismColumnCoordinates_measurePreserving :
    MeasurePreserving (fun x : Cover ↦ (x 0,planeProductCoordinates.symm (x 2,x 1))) volume volume := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod
    ((planeProductCoordinates_measurePreserving.symm
      planeProductCoordinates.toHomeomorph.toMeasurableEquiv).comp
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))))
  have hh := hp.comp coverPrismCoordinates_measurePreserving
  convert! hh using 1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma finiteMeasure_real_open_le_of_eventually_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [HasOuterApproxClosed X] [OpensMeasurableSpace X]
    {l : Filter ℕ} [NeBot l] {μ : ℕ → FiniteMeasure X} {ν : FiniteMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {s : Set X} (hs : IsOpen s)
    {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u l (𝓝 L))
    (hb : ∀ᶠ i in l, (μ i : Measure X).real s ≤ u i) :
    (ν : Measure X).real s ≤ L := by
  have hm : Tendsto (fun i ↦ (μ i : Measure X).real univ) l
      (𝓝 ((ν : Measure X).real univ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (FiniteMeasure.continuous_mass.tendsto ν |>.comp hlim)
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hm.sub hu)
  have hbd : ∀ᶠ i in l, ENNReal.ofReal ((μ i : Measure X).real univ-u i) ≤
      (μ i : Measure X) sᶜ := by
    filter_upwards [hb] with i hi
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ i : Measure X) sᶜ)]
    apply ENNReal.ofReal_le_ofReal
    change _ ≤ (μ i : Measure X).real sᶜ
    rw [measureReal_compl hs.measurableSet]
    linarith
  have hh : ENNReal.ofReal ((ν : Measure X).real univ-L) ≤ (ν : Measure X) sᶜ := by
    rw [← he.limsup_eq]
    exact (limsup_le_limsup hbd).trans
      (FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hs.isClosed_compl)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure X) sᶜ)] at hh
  have hreal := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hh
  change _ ≤ (ν : Measure X).real sᶜ at hreal
  rw [measureReal_compl hs.measurableSet] at hreal
  linarith

theorem moving_blowup_normal_mass_le_competitor {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    {a b L : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hL : 0 ≤ L)
    (hper : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) a} ≤ L := by
  obtain ⟨η,C,hη,_,hcomp⟩ := MovingCenter.isMinimizerAt_scaled_set_replacement hV hE hmin hμ
  obtain ⟨K,_,hK⟩ := smoothTransition_exists_deriv_bound
  let D : ℕ → ℝ := fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
    |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|
  have hsmall : ∀ᶠ i in l, r i < 3/8 ∧ r i*b < 1/4 ∧ (r i*b)^3*(Real.pi*8/3) < η := by
    have hs1 : Tendsto (fun i ↦ r i*b) l (𝓝 0) := by simpa using hrlim.mul_const b
    have hs2 : Tendsto (fun i ↦ (r i*b)^3*(Real.pi*8/3)) l (𝓝 0) := by
      simpa using (hs1.pow 3).mul_const (Real.pi*8/3)
    exact (hrlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<3/8))).and
      ((hs1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))).and
        (hs2.eventually (gt_mem_nhds hη)))
  have hlim : Tendsto (fun i ↦ L+2*K*b*(D i+r i)/(b^2-a^2)+C*r i*b^3) l (𝓝 L) := by
    have hh := ((tendsto_const_nhds (x := L)).add
      (((tendsto_const_nhds (x := 2*K*b)).mul (hconv.add hrlim)).div_const (b^2-a^2))).add
        (((tendsto_const_nhds (x := C)).mul hrlim).mul_const (b^3))
    simpa only [zero_add,mul_zero,zero_mul,zero_div,add_zero] using hh
  apply finiteMeasure_real_open_le_of_eventually_le hν
    (Metric.isOpen_ball.preimage continuous_fst) hlim
  filter_upwards [hsmall] with i hi
  change (blowupNormalMeasure μ (c i) (r i) 2 : Measure BlowupNormalBundle).real
    {z | z.1 ∈ Metric.ball (0 : Cover) a} ≤ _
  rw [blowupNormalMeasure_ball μ (c i) (hr i) (by linarith : a ≤ 2),
    cellBallMass_eq_spatialNormalMeasure μ (c i) (r i*a)
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by nlinarith [hr i]))).trans
        (MovingCenter.closedBall_interior hi.1))]
  have herr : (∫ x in Metric.ball (0 : Cover) b,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < D i+r i := by
    have hm := setIntegral_mono_set (blowup_error_integrable hE hA (c i) (r i) 1)
      (ae_of_all _ fun x ↦ abs_nonneg _)
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hb1)).eventuallyLE)
    exact lt_of_le_of_lt hm (lt_add_of_pos_right _ (hr i))
  have hh := hcomp (c i) A B hA hB a b L K (r i) (D i+r i) ha hab (hr i)
    hi.2.1 hi.2.2 hL hK hper hAB herr
  calc
    _ ≤ (r i)⁻¹^2*( (r i)^2*(L+2*K*b*(D i+r i)/(b^2-a^2))+C*(r i*b)^3) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by field_simp [(hr i).ne']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMeasure_ball_le_of_smaller {ν : Measure BlowupNormalBundle} {b : ℝ}
    (hb : 0 < b) {P : ℝ≥0∞}
    (h : ∀ a : ℝ, 0 < a → a < b → ν {z | z.1 ∈ Metric.ball (0 : Cover) a} ≤ P) :
    ν {z | z.1 ∈ Metric.ball (0 : Cover) b} ≤ P := by
  let q : ℕ → ℝ := fun i ↦ b-b/((i : ℝ)+1)
  let S : ℕ → Set BlowupNormalBundle := fun i ↦ {z | z.1 ∈ Metric.ball (0 : Cover) (q i)}
  have hq : Monotone q := by
    intro i j hij
    dsimp [q]
    have hh : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left hb.le (by positivity) (by linarith)
  have hS : Monotone S := fun i j hij z hz ↦ Metric.ball_subset_ball (hq hij) hz
  have hlim : Tendsto q atTop (𝓝 b) := by
    simpa [q,div_eq_mul_inv] using (tendsto_const_nhds (x := b)).sub
      ((tendsto_const_nhds (x := b)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
  have he : (⋃ i, S i) = {z | z.1 ∈ Metric.ball (0 : Cover) b} := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      apply Metric.ball_subset_ball (show q i ≤ b from ?_) hi
      dsimp [q]
      exact sub_le_self _ (by positivity)
    · intro hz
      have hh : ‖z.1‖ < b := by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hz
      obtain ⟨i,hi⟩ := (hlim.eventually (lt_mem_nhds hh)).exists
      exact mem_iUnion.mpr ⟨i,by simpa only [S,mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hi⟩
  rw [← he,hS.measure_iUnion]
  apply iSup_le
  intro i
  by_cases hi : 0 < q i
  · exact h (q i) hi (by dsimp [q]; exact sub_lt_self _ (by positivity))
  · have hz : S i = ∅ := by
      ext z
      simp only [S,Metric.mem_ball,dist_zero_right,mem_ofPred_eq,mem_empty_iff_false,iff_false]
      exact not_lt.mpr ((not_lt.mp hi).trans (norm_nonneg _))
    rw [hz,measure_empty]
    exact bot_le

theorem moving_blowup_perimeter_eq_normal_ball {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    coverLocalPerimeter A (Metric.ball (0 : Cover) b) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) b} := by
  have hup := coverLocalPerimeter_le_normal Metric.isOpen_ball.measurableSet
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hb1)) hflux
  have hfin : coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top (ν : Measure BlowupNormalBundle) _) hup
  let L : ℝ := (coverLocalPerimeter A (Metric.ball (0 : Cover) b)).toReal
  have hL := ENNReal.ofReal_toReal hfin
  apply le_antisymm hup
  apply normalMeasure_ball_le_of_smaller hb
  intro a ha hab
  let d : ℝ := (a+b)/2
  have had : a < d := by dsimp [d]; linarith
  have hdb : d < b := by dsimp [d]; linarith
  have hper : coverLocalPerimeter A (Metric.closedBall (0 : Cover) d) ≤ ENNReal.ofReal L := by
    rw [hL]
    exact coverLocalPerimeter_mono A (Metric.closedBall_subset_ball hdb)
  have hh := moving_blowup_normal_mass_le_competitor hV hE hmin hμ c r hr hrlim hA hA
    hconv hν ha had (hdb.le.trans hb1) ENNReal.toReal_nonneg hper (by simp)
  have hh' := ENNReal.ofReal_le_ofReal hh
  rw [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (ν : Measure BlowupNormalBundle) _)] at hh'
  exact hh'.trans_eq hL

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

theorem blowupNormal_weighted_saturation {A O : Set Cover}
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {w : BlowupNormalBundle → ℝ}
    (hiw : Integrable w ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}))
    {C : ℝ} (hC : 0 < C) (hwC : ∀ z, w z ≤ C)
    {L : ℝ}
    (hL : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z*⟪(z.2 : Cover),F z.1⟫
        ∂(ν : Measure BlowupNormalBundle)) ≤ L) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z
      ∂(ν : Measure BlowupNormalBundle)) ≤ L := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let P : ℝ := (coverLocalPerimeter A O).toReal
  let I : ℝ := ∫ z, w z ∂μ
  let B : ℝ := P+(L-I)/C
  have hmass : (∫ _ : BlowupNormalBundle, (1 : ℝ) ∂μ) = P := by
    simp only [integral_const,smul_eq_mul,mul_one,μ,P,heq,Measure.real,Measure.restrict_apply_univ]
  have hbound (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (hn : ∀ x, ‖F x‖ ≤ 1) :
      (∫ x in A, divergence F x) ≤ B := by
    let T : BlowupNormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F z.1⟫
    have hTc : Continuous T := (continuous_subtype_val.comp continuous_snd).inner
      (hF.continuous.comp continuous_fst)
    have hTb (z : BlowupNormalBundle) : |T z| ≤ 1 := blowup_test_inner_bound hn z
    have hiT : Integrable T μ := Integrable.of_bound hTc.aestronglyMeasurable 1
      (ae_of_all μ hTb)
    have hiwT : Integrable (fun z ↦ w z*T z) μ := by
      simpa only [mul_comm] using hiw.bdd_mul hTc.aestronglyMeasurable (ae_of_all μ hTb)
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) (fun z ↦ show
        w z-w z*T z ≤ C*(1-T z) from by
          have ht : 0 ≤ 1-T z := by linarith [(le_abs_self (T z)).trans (hTb z)]
          nlinarith [mul_le_mul_of_nonneg_right (hwC z) ht])
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT,integral_const_mul,integral_sub (integrable_const 1) hiT,hmass] at hh
    have hf : (∫ z, T z ∂μ) = ∫ x in A, divergence F x := by
      rw [show (∫ z, T z ∂μ) = ∫ z, T z ∂(ν : Measure BlowupNormalBundle) from ?_]
      · exact hflux F hF hs hO hn
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzF : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz (hO hh))
      simp only [T,hzF,inner_zero_right]
    rw [hf] at hh
    have hl := hL F hF hs hO hn
    change (∫ z, w z*T z ∂μ) ≤ L at hl
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul,div_mul_cancel₀ _ hC.ne']
    dsimp only [I]
    nlinarith
  have hB : 0 ≤ B := by
    have hh := hbound (fun _ ↦ 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa only [divergence_zero,integral_zero] using hh
  have hper : coverLocalPerimeter A O ≤ ENNReal.ofReal B := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hn
    exact ENNReal.ofReal_le_ofReal (hbound F hF hs hO hn)
  have hPB : P ≤ B := by
    simpa only [P,ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hper
  have hnon : 0 ≤ (L-I)/C := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hnon hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

lemma coverLocalPerimeter_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B)) :
    coverLocalPerimeter A O = coverLocalPerimeter B O := by
  unfold coverLocalPerimeter
  apply iSup_congr; intro F
  apply iSup_congr; intro _
  apply iSup_congr; intro _
  apply iSup_congr; intro hs
  apply iSup_congr; intro _
  rw [setIntegral_divergence_congr_local hA hB hAB hs]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverHalfspace (n : Cover) : Set Cover := {x | ⟪n,x⟫ < 0}

lemma measurableSet_coverHalfspace (n : Cover) : MeasurableSet (coverHalfspace n) :=
  measurableSet_lt (by fun_prop) measurable_const

lemma halfspace_indicator_eq (n : Cover) :
    (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) = halfspaceIndicator n := rfl

lemma setIntegral_coverHalfspace_divergence {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, ⟪n,F (normalPlaneEmbedding n y)⟫ := by
  have hh := integral_halfspace_divergence 0 hn hF hs
  simp only [sub_zero,zero_add] at hh
  rw [← hh,← halfspace_indicator_eq]
  simp only [← indicator_mul_left,one_mul,integral_indicator (measurableSet_coverHalfspace n)]

lemma coverHalfspace_flux_le {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {b : ℝ} (hb : 0 ≤ b) (hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b)
    (hbound : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in coverHalfspace n, divergence F x) ≤ Real.pi*b^2 := by
  rw [setIntegral_coverHalfspace_divergence hn hF hs]
  have hc : Continuous (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hh := (normalColumnChart_plane_isometry 0 hn 0).continuous
    simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] at hh
    exact continuous_const.inner (hF.continuous.comp hh)
  have hsc : HasCompactSupport (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hss := hs.comp_isClosedEmbedding (normalColumnChart_plane_isometry 0 hn 0).isClosedEmbedding
    have hh := hss.comp_left (show ⟪n,(0 : Cover)⟫ = 0 by simp)
    simpa only [Function.comp_def,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] using hh
  have hi : Integrable (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := hc.integrable_of_hasCompactSupport hsc
  have hbint : Integrable ((Metric.closedBall (0 : Plane) b).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hh := integral_mono hi hbint (fun y ↦ ?_)
  · have hv : (volume : Measure Plane).real (Metric.closedBall 0 b) = Real.pi*b^2 := by
      simp only [Measure.real,EuclideanSpace.volume_closedBall_fin_two,ENNReal.toReal_mul,
        ENNReal.toReal_pow,ENNReal.toReal_ofReal hb,ENNReal.toReal_ofReal Real.pi_pos.le]
      ring
    rw [integral_indicator Metric.isClosed_closedBall.measurableSet,integral_const,
      smul_eq_mul,mul_one,measureReal_restrict_apply_univ,hv] at hh
    exact hh
  · by_cases hy : y ∈ Metric.closedBall (0 : Plane) b
    · rw [indicator_of_mem hy]
      exact (real_inner_le_norm _ _).trans (by rw [hn,one_mul]; exact hbound _)
    · rw [indicator_of_notMem hy]
      have hz : F (normalPlaneEmbedding n y) = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (by
        simpa only [Metric.mem_closedBall,dist_zero_right,normalPlaneEmbedding_norm] using hFb hh))
      simp [hz]

lemma coverLocalPerimeter_halfspace_le {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 ≤ b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) ≤
      ENNReal.ofReal (Real.pi*b^2) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro hbF
  apply iSup_le; intro hbound
  exact ENNReal.ofReal_le_ofReal (coverHalfspace_flux_le hn hF hs hb hbF hbound)

theorem coverLocalPerimeter_halfspace {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm (coverLocalPerimeter_halfspace_le hn hb.le)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (integral_radialDensityWeight_plane_tendsto n hb)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
  have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
  have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
    (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
      (radialDensityWeight_tsupport hb.le hε)
  have hbound (x : Cover) : ‖F x‖ ≤ 1 := by
    change ‖radialDensityWeight 0 b ε x • n‖ ≤ 1
    rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  have he : (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    rw [setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  dsimp only [Function.comp_apply]
  rw [← he]
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le hFb (le_iSup_of_le hbound le_rfl))))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_scalar_trace_integrable {n : Cover} (hn : ‖n‖ = 1)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun y : Plane ↦ φ (normalPlaneEmbedding n y)) := by
  have he : (fun y : Plane ↦ normalColumnChart 0 n (0,y)) = normalPlaneEmbedding n := by
    funext y
    simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add]
  have hi := (normalColumnChart_plane_isometry 0 hn 0)
  have hc : Continuous (normalPlaneEmbedding n) := he ▸ hi.continuous
  have hh : Topology.IsClosedEmbedding (normalPlaneEmbedding n) := he ▸ hi.isClosedEmbedding
  exact (hφ.comp hc).integrable_of_hasCompactSupport (hs.comp_isClosedEmbedding hh)

theorem blowup_flat_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (normalPlaneEmbedding n y)*⟪n,F (normalPlaneEmbedding n y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHU : tsupport H ⊆ U := (tsupport_smul_subset_left _ _).trans hφU
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA (measurableSet_coverHalfspace n) hflat hHU,
    setIntegral_coverHalfspace_divergence hn hH hsH] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

theorem blowup_flat_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (normalPlaneEmbedding n y) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiplane := plane_scalar_trace_integrable hn hφ.continuous hsφ
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤ ∫ y : Plane, φ (normalPlaneEmbedding n y) := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_flat_patch_weighted_flux hA hn hflat hflux hφ hsφ hφU hφO hφb hF hnF]
    have hc : Continuous (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
      have hh := (normalColumnChart_plane_isometry 0 hn 0).continuous
      simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] at hh
      exact continuous_const.inner (hF.continuous.comp hh)
    have hb (y : Plane) : |⟪n,F (normalPlaneEmbedding n y)⟫| ≤ 1 :=
      by
      have hh : |⟪n,F (normalPlaneEmbedding n y)⟫| ≤ ‖n‖*‖F (normalPlaneEmbedding n y)‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) n (F (normalPlaneEmbedding n y))
      exact hh.trans (by rw [hn,one_mul]; exact hnF _)
    have hi := hiplane.bdd_mul hc.aestronglyMeasurable (ae_of_all volume hb)
    apply integral_mono (by simpa only [mul_comm] using hi) hiplane
    intro y
    exact mul_le_of_le_one_right (hφb _).1 ((le_abs_self _).trans (hb y))
  refine le_antisymm ?_ ?_
  · exact blowupNormal_weighted_saturation heq hflux hiφ (by norm_num : (0 : ℝ)<1)
      (fun z ↦ (hφb z.1).2) (fun F hF _ _ hnF ↦ hfield F hF hnF)
  · have he := blowup_flat_patch_weighted_flux hA hn hflat hflux hφ hsφ hφU hφO hφb
      (F := fun _ ↦ n) contDiff_const (fun _ ↦ hn.le)
    simp only [real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at he
    rw [← he]
    have hiinner : Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),n⟫) μ := by
      simpa only [mul_comm] using hiφ.bdd_mul
        (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable
        (ae_of_all μ fun z ↦ blowup_test_inner_bound (F := fun _ ↦ n) (fun _ ↦ hn.le) z)
    apply integral_mono hiinner hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) n).trans_eq (by rw [z.2.property,hn,one_mul])

theorem blowup_flat_patch_normal {A O U : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover) = n := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiinner : Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),n⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound (F := fun _ ↦ n) (fun _ ↦ hn.le) z)
  have hm := blowup_flat_patch_weighted_mass hA hn hflat heq hflux hφ hsφ hφU hφO hφb
  have hf := blowup_flat_patch_weighted_flux hA hn hflat hflux hφ hsφ hφU hφO hφb
    (F := fun _ ↦ n) contDiff_const (fun _ ↦ hn.le)
  simp only [real_inner_self_eq_norm_sq,hn,one_pow,mul_one] at hf
  have hz : (∫ z, (φ z.1-φ z.1*⟪(z.2 : Cover),n⟫) ∂μ) = 0 := by
    rw [integral_sub hiφ hiinner,hm,hf,sub_self]
  have hnon (z : BlowupNormalBundle) : 0 ≤ φ z.1-φ z.1*⟪(z.2 : Cover),n⟫ := by
    have hh := (real_inner_le_norm (z.2 : Cover) n)
    rw [z.2.property,hn,one_mul] at hh
    nlinarith [(hφb z.1).1,mul_nonneg (hφb z.1).1 (sub_nonneg.mpr hh)]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hnon) (hiφ.sub hiinner)).mp hz
  filter_upwards [hae] with z hz hp
  change φ z.1-φ z.1*⟪(z.2 : Cover),n⟫ = 0 at hz
  have hh : ⟪(z.2 : Cover),n⟫ = 1 := by nlinarith
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hs : ‖(z.2 : Cover)-n‖^2 = 0 := by rw [norm_sub_sq_real,z.2.property,hn,hh]; norm_num
  exact sq_eq_zero_iff.mp hs

end CubicTorus

end
end

end

end OAI
