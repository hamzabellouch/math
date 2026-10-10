import Mathlib
import OAI.Geometry.CubicTorus.Compactness.GraphMollifier

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def normalCoverMap (z : NormalBundle) : BlowupNormalBundle := ((z.1 : Cover),z.2)

lemma continuous_normalCoverMap : Continuous normalCoverMap := by
  exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

def normalCoverMeasure (μ : FiniteMeasure NormalBundle) : FiniteMeasure BlowupNormalBundle :=
  μ.map normalCoverMap

lemma normalCoverMeasure_integral {μ : FiniteMeasure NormalBundle} {f : BlowupNormalBundle → ℝ}
    (hf : Continuous f) :
    (∫ z, f z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, f (normalCoverMap z) ∂(μ : Measure NormalBundle) := by
  rw [normalCoverMeasure,FiniteMeasure.toMeasure_map,
    integral_map continuous_normalCoverMap.measurable.aemeasurable hf.aestronglyMeasurable]

def HasCutoffSaturation (ν : FiniteMeasure BlowupNormalBundle) (O : Set Cover) : Prop :=
  ∀ (φ : Cover → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ O → (∀ x, φ x ∈ Icc 0 1) → ∀ C : ℝ,
    (∀ (F : Cover → Cover), ContDiff ℝ (⊤ : ℕ∞) F → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
        ∂(ν : Measure BlowupNormalBundle)) ≤ C) →
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(ν : Measure BlowupNormalBundle)) ≤ C

lemma normalMeasure_cutoff_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (O : Set Cover) : HasCutoffSaturation (normalCoverMeasure μ) O := by
  intro φ hφ hsφ hs hb C hC
  have hemass : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, φ (z.1 : Cover) ∂(μ : Measure NormalBundle) := by
    have hz : ∀ z : BlowupNormalBundle, z ∉ {z : BlowupNormalBundle | z.1 ∈ O} → φ z.1=0 :=
      fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact normalCoverMeasure_integral (hφ.continuous.comp continuous_fst)
  rw [hemass]
  apply normalMeasure_weighted_saturation hμ
    ⟨fun z ↦ φ (z.1 : Cover),hφ.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  intro F hF
  have hFc : Continuous F := hF.1.continuous
  have heflux : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun (z : BlowupNormalBundle) hz ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h)),zero_mul])]
    exact normalCoverMeasure_integral (by fun_prop)
  change (∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ C
  rw [← heflux]
  exact hC F hF.1 hF.2.2

lemma normalCoverMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ x in quotientMap ⁻¹' E, divergence F x := by
  rw [normalCoverMeasure_integral (by fun_prop)]
  change (∫ z : NormalBundle, ⟪(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
  rw [normalMeasure_local_flux hE hμ hF hc hs,← integral_indicator (hE.preimage measurable_quotientMap)]
  congr 1
  funext x
  classical
  by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]

lemma normalCoverMeasure_CMC {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D=H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      H*(∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) := by
  rw [normalCoverMeasure_integral (continuous_blowupTangentTest hF),normalCoverMeasure_integral (by fun_prop)]
  exact weakCMC_local_identity hμ hH hF hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiArea := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hiF (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound hnF z)
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤
        ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
      (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous hF.continuous).continuousAt)) hiArea
    intro y
    apply mul_le_mul_of_nonneg_left _ (hφb _).1
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnF _))
  refine le_antisymm ?_ ?_
  · exact hsat φ hφ hsφ hφO hφb _ hfield
  · apply le_of_tendsto (graph_area_trace_mollified_normal_tendsto a hn hg hc
      hφ.continuous hsφ hφR (fun x ↦ (hφb x).1))
    apply Eventually.of_forall
    intro i
    let F := graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
    have hnF (x : Cover) : ‖F x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
    rw [← blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (hiF F hF hnF) hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) (F z.1)).trans (by rw [z.2.property,one_mul]; exact hnF _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_normal_ae {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let F : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let f : ℕ → BlowupNormalBundle → ℝ := fun i z ↦ φ z.1*⟪(z.2 : Cover),F i z.1⟫
  let f₀ : BlowupNormalBundle → ℝ := fun z ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hFn (i) (x) : ‖F i x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
  have hf (i) : AEStronglyMeasurable (f i) μ :=
    (show Continuous (f i) from (hφ.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd |>.inner ((hF i).continuous.comp continuous_fst))).aestronglyMeasurable
  have ht : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 (f₀ z)) :=
    ae_of_all μ (graph_weighted_normal_tendsto a hn hg hc hφR)
  have hb (i) (z : BlowupNormalBundle) : ‖f i z‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound (hFn i) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb₀ (z : BlowupNormalBundle) : ‖f₀ z‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound
      (fun x ↦ (graphUnitNormalExtension_unit a hn _ x).le) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hi₀ : Integrable f₀ μ := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hf ht) 1 (ae_of_all μ hb₀)
  have hilim : Tendsto (fun i ↦ ∫ z, f i z ∂μ) atTop (𝓝 (∫ z, f₀ z ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hf
      (integrable_const 1) (fun i ↦ ae_of_all μ (hb i)) ht
  have heint : (∫ z, f₀ z ∂μ) = ∫ z, φ z.1 ∂μ := by
    apply tendsto_nhds_unique hilim
    rw [show (∫ z, φ z.1 ∂μ) = _ from
      cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb]
    have hh := graph_area_trace_mollified_normal_tendsto a hn hg hc hφ.continuous hsφ hφR
      (fun x ↦ (hφb x).1)
    convert hh using 1
    funext i
    exact blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb (hF i) (hFn i)
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hinon (z : BlowupNormalBundle) : 0 ≤ φ z.1-f₀ z := by
    have hh : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ ≤ 1 := by
      exact (real_inner_le_norm _ _).trans_eq (by rw [z.2.property,graphUnitNormalExtension_unit a hn,one_mul])
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hφb _).1 hh)
  have hezero : (∫ z, (φ z.1-f₀ z) ∂μ)=0 := by rw [integral_sub hiφ hi₀,heint,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hinon) (hiφ.sub hi₀)).mp hezero
  filter_upwards [hae] with z hz
  intro hzφ
  have hi : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ = 1 := by
    have hh : φ z.1*(1-⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)=0 := by
      simpa only [mul_sub,mul_one,f₀,Pi.zero_apply] using hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hzφ.ne')).symm
  exact (inner_eq_one_iff_of_norm_eq_one z.2.property (graphUnitNormalExtension_unit a hn g z.1)).mp hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_signed_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfb : ∀ x, |f x| ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let ψ : Cover → ℝ := fun x ↦ φ x*((1+f x)/2)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.mul ((contDiff_const.add hf).div_const 2)
  have hsψ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_left
  have hψb (x : Cover) : ψ x ∈ Icc 0 1 := by
    have hx := abs_le.mp (hfb x)
    have hhalf : (1+f x)/2 ∈ Icc 0 1 := ⟨by linarith,by linarith⟩
    exact ⟨mul_nonneg (hφb x).1 hhalf.1,
      (mul_le_mul (hφb x).2 hhalf.2 hhalf.1 zero_le_one).trans_eq (one_mul 1)⟩
  have hsψ' : HasCompactSupport ψ := hsφ.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hmψ := cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hψ hsψ'
    (hsψ.trans hφU) (hsψ.trans hφO) (hsψ.trans hφR) hψb
  have hmφ := cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb
  have hI (w : Cover → ℝ) (hw : Continuous w) (hb : ∀ x, w x ∈ Icc 0 1) :
      Integrable (fun z : BlowupNormalBundle ↦ w z.1) μ :=
    Integrable.of_bound (hw.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb _).1]; exact (hb _).2)
  have hGφ := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hGψ := graph_weighted_integrable a hn hg.continuous hψ.continuous hsψ' (hsψ.trans hφR)
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  calc
    (∫ z, φ z.1*f z.1 ∂μ) = ∫ z, (2*ψ z.1-φ z.1) ∂μ := by
      congr 1; funext z; dsimp only [ψ]; ring
    _ = 2*(∫ z, ψ z.1 ∂μ)-(∫ z, φ z.1 ∂μ) := by
      rw [integral_sub ((hI ψ hψ.continuous hψb).const_mul 2) (hI φ hφ.continuous hφb),integral_const_mul]
    _ = 2*(∫ y : Plane, ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by rw [hmψ,hmφ]
    _ = ∫ y : Plane, (2*(ψ (a+normalGraph n g y)*‖graphAreaVector n g y‖)-
        φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) := by
      rw [integral_sub (hGψ.const_mul 2) hGφ,integral_const_mul]
    _ = _ := by congr 1; funext y; dsimp only [ψ]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_limit_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {f : ℕ → Cover → ℝ} {f₀ : Cover → ℝ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (hfb : ∀ i x, |f i x| ≤ 1)
    (hlim : ∀ x ∈ tsupport φ, Tendsto (fun i ↦ f i x) atTop (𝓝 (f₀ x))) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*f₀ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hleft : Tendsto (fun i ↦ ∫ z, φ z.1*f i z.1 ∂μ) atTop (𝓝 (∫ z, φ z.1*f₀ z.1 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ))
    · intro i
      exact ((hφ.continuous.mul (hf i).continuous).comp continuous_fst).aestronglyMeasurable
    · exact integrable_const 1
    · intro i
      filter_upwards [] with z
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs]
      exact (mul_le_mul (hφb _).2 (hfb i _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · exact ae_of_all μ fun z ↦ weighted_tendsto_on_tsupport hlim z.1
  have hright : Tendsto (fun i ↦ ∫ y : Plane,
      φ (a+normalGraph n g y)*f i (a+normalGraph n g y)*‖graphAreaVector n g y‖) atTop
      (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)
    · intro i
      have hh := graph_weighted_continuous a hn hg.continuous hφ.continuous hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
      have hmeas : AEStronglyMeasurable (fun y : Plane ↦
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)*f i (a+normalGraph n g y))
          (volume : Measure Plane) :=
        (hh.mul (graph_trace_continuous a n hg.continuous (hf i).continuous)).aestronglyMeasurable
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hmeas
    · exact graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
        (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
    · intro i
      filter_upwards [] with y
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1,Real.norm_eq_abs,
        norm_norm]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (hφb _).1 (hfb i _)) (norm_nonneg _)
    · filter_upwards [] with y
      exact (weighted_tendsto_on_tsupport hlim _).mul_const _
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext i
  exact cutoff_graph_patch_signed_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb (hf i) (hfb i)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_C1graph_firstVariation {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsF : HasCompactSupport F)
    (hφF : ∀ x ∈ tsupport F, φ x = 1) :
    (∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
      (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖) =
      ∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let M : ℝ := ‖blowupTangentTest hF hsF‖+1
  have hM : 0 < M := by dsimp only [M]; positivity
  let N : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let N₀ := graphUnitNormalExtension a n g
  let f : ℕ → Cover → ℝ := fun i x ↦ M⁻¹*tangentialDivergence F x (N i x)
  let f₀ : Cover → ℝ := fun x ↦ M⁻¹*tangentialDivergence F x (N₀ x)
  have hN (i) : ContDiff ℝ (⊤ : ℕ∞) (N i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hf (i) : ContDiff ℝ (⊤ : ℕ∞) (f i) :=
    contDiff_const.mul (contDiff_tangentialDivergence_normal hF (hN i))
  have hfb (i) (x) : |f i x| ≤ 1 := by
    have hh := (blowupTangentTest hF hsF).norm_coe_le_norm
      (x,⟨N i x,graphUnitNormalExtension_unit a hn _ x⟩)
    change ‖tangentialDivergence F x (N i x)‖ ≤ ‖blowupTangentTest hF hsF‖ at hh
    dsimp only [f]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hM)]
    apply (mul_le_mul_of_nonneg_left (hh.trans (le_add_of_nonneg_right zero_le_one)) (inv_nonneg.mpr hM.le)).trans_eq
    exact inv_mul_cancel₀ hM.ne'
  have hlim (x : Cover) (hx : x ∈ tsupport φ) : Tendsto (fun i ↦ f i x) atTop (𝓝 (f₀ x)) := by
    have hcoord : normalPlaneCoordinates n (x-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hx)
    exact (((continuous_tangentialDivergence_normal F x).tendsto _).comp
      (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul M⁻¹
  have he := cutoff_graph_patch_limit_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb hf hfb hlim
  have hae := cutoff_graph_patch_normal_ae hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb
  have hw (x v) : φ x*tangentialDivergence F x v=tangentialDivergence F x v := by
    by_cases hx : x ∈ tsupport F
    · rw [hφF x hx,one_mul]
    · rw [tangentialDivergence_zero_of_notMem_tsupport hx,mul_zero]
  have hFO : tsupport F ⊆ O := by
    intro x hx
    apply hφO
    exact subset_tsupport _ (by rw [Function.mem_support,hφF x hx]; exact one_ne_zero)
  have hleft : (∫ z, φ z.1*f₀ z.1 ∂μ)=M⁻¹*(∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) := by
    calc
      (∫ z, φ z.1*f₀ z.1 ∂μ) = ∫ z, M⁻¹*tangentialDivergence F z.1 z.2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hae] with z hz
        by_cases hzφ : 0 < φ z.1
        · dsimp only [f₀,N₀]
          rw [← hz hzφ,← mul_assoc,mul_comm (φ z.1) M⁻¹,mul_assoc,hw]
        · have hφz : φ z.1=0 := le_antisymm (le_of_not_gt hzφ) (hφb _).1
          dsimp only [f₀]
          rw [hφz,zero_mul,← hw z.1 (z.2 : Cover),hφz,zero_mul,mul_zero]
      _ = M⁻¹*(∫ z, tangentialDivergence F z.1 z.2 ∂μ) := integral_const_mul _ _
      _ = M⁻¹*(∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) := by
        congr 1
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        exact tangentialDivergence_zero_of_notMem_tsupport (fun h ↦ hz (hFO h)) _
  have hright : (∫ y : Plane, φ (a+normalGraph n g y)*f₀ (a+normalGraph n g y)*‖graphAreaVector n g y‖) =
      M⁻¹*(∫ y : Plane, tangentialDivergence F (a+normalGraph n g y)
        (graphSlopeNormal n (gradient g y))*‖graphAreaVector n g y‖) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    dsimp only [f₀,N₀]
    rw [graphUnitNormalExtension_graph a hn,← mul_assoc (φ _) M⁻¹,mul_comm (φ _) M⁻¹,mul_assoc M⁻¹,hw]
    ring
  rw [hright,hleft] at he
  exact (mul_left_cancel₀ (inv_ne_zero hM.ne') he).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_strict_C1_cone_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ),
      MeasurableSet A ∧ 0 < θ ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      (∀ b : ℝ, 0 < b → b < 2 →
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) b} = θ*b^2) ∧
      (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
        ⟪(z.2 : Cover),z.1⟫ = 0) ∧
      (∀ p : Cover, ‖p‖ < 1 → p ≠ 0 → p ∈ coverEssentialBoundary A → CoverC1BoundaryAt A p) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) := by
  have hc := cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ) < 1/2)
  obtain ⟨θ',hθ'0,hdens⟩ := exists_density_of_cmc_monotone (by norm_num : (0 : ℝ) < 1/4)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH cubeCenter hc)
  obtain ⟨A,ν,θ,φ,U,hA,hθ0,hφ,hU,hconv,hν,hm,hflux,hrad⟩ :=
    isMinimizerAt_paired_blowup hV hE hmin hμ hH cubeCenter
      (by norm_num : (0 : ℝ) < 1/4) hc r hr hrlim
  have hrl : Tendsto (fun i ↦ r (φ i)) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have heθ : θ'=θ := by
    have hh := blowup_limit_ball_mass cubeCenter (fun i ↦ r (φ i)) (fun i ↦ hr _)
      (hrl.mono_left hU) hdens hν (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    have hh' := hm 1 (by norm_num) (by norm_num)
    norm_num at hh hh'
    exact hh.symm.trans hh'
  subst θ'
  have hsp : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ) := by
    apply hdens.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with t ht
    change cellBallMass μ cubeCenter t / t^2 = _
    rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter t
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ht.le)).trans hc)]
  have heq (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) := isMinimizerAt_blowup_perimeter_eq
    hV hE hmin hμ hθ0 hsp (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hm
    (fun F hF hs ↦ (hflux F hF hs).2) hb hb1
  have hcone (t : ℝ) (ht : 1 ≤ t) : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A) :=
    radial_flux_cone_ae hA (fun ψ hψ hs ↦
      limit_set_radial_flux (fun F hF hFs ↦ (hflux F hF hFs).2) hrad hψ hs) ht
  have hC1 (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0) (hbd : p ∈ coverEssentialBoundary A) :=
    actual_primary_offvertex_C1 hV hE hmin hcenter hμ hH (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hconv hcone hflux p hp hp0 hbd
  refine ⟨A,ν,θ,φ,hA,isMinimizerAt_density_pos hV hE hmin hμ hcenter hsp,hφ,hconv,heq,?_,hcone,hm,hrad,hC1,hflux⟩
  · intro B hB a b ha hab hb1 hAB
    exact isMinimizerAt_blowup_local_minimal hV hE hmin hμ hsp (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hB hconv ha hab (by linarith : b ≤ 2)
      (heq b (ha.trans hab) hb1) hAB

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverEssentialBoundary_eq_support (A : Set Cover) :
    coverEssentialBoundary A = (volume.restrict A).support ∩ (volume.restrict Aᶜ).support := by
  ext p
  simp only [coverEssentialBoundary,Set.mem_ofPred_eq,Set.mem_inter_iff,
    Metric.nhds_basis_ball.mem_measureSupport,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet,inter_comm,forall_and]
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨fun r hr ↦ (ENNReal.toReal_pos_iff).mp (ha r hr) |>.1,
      fun r hr ↦ (ENNReal.toReal_pos_iff).mp (hc r hr) |>.1⟩
  · rintro ⟨ha,hc⟩
    refine ⟨fun r hr ↦ ?_,fun r hr ↦ ?_⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨ha r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩
    · exact ENNReal.toReal_pos_iff.mpr ⟨hc r hr,
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top⟩

lemma coverEssentialBoundary_compl (A : Set Cover) :
    coverEssentialBoundary Aᶜ = coverEssentialBoundary A := by
  simp only [coverEssentialBoundary_eq_support,compl_compl,inter_comm]

lemma cover_boundary_local_ae {A B U : Set Cover} {p : Cover}
    (hU : U ∈ 𝓝 p) (hae : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ x ∈ B))
    (hp : p ∈ coverEssentialBoundary A) : p ∈ coverEssentialBoundary B := by
  rw [coverEssentialBoundary_eq_support] at hp ⊢
  exact ⟨measureSupport_local_ae_mono hU (hae.mono (fun _ h hu ↦ (h hu).mp)) hp.1,
    measureSupport_local_ae_mono hU (hae.mono (fun _ h hu ↦ (not_congr (h hu)).mp)) hp.2⟩

lemma cover_boundary_preimage_image {A : Set Cover} {f : Cover → Cover} {p : Cover}
    (hq : Measure.QuasiMeasurePreserving f volume volume) (hf : ContinuousAt f p)
    (hp : p ∈ coverEssentialBoundary (f ⁻¹' A)) : f p ∈ coverEssentialBoundary A := by
  rw [coverEssentialBoundary_eq_support] at hp ⊢
  exact ⟨measureSupport_preimage_image hq hf hp.1,measureSupport_preimage_image hq hf hp.2⟩

lemma cover_boundary_measurePreserving_homeomorph {A : Set Cover} (f : Cover ≃ₜ Cover)
    (hq : MeasurePreserving f) (p : Cover) :
    p ∈ coverEssentialBoundary (f ⁻¹' A) ↔ f p ∈ coverEssentialBoundary A := by
  constructor
  · exact cover_boundary_preimage_image hq.quasiMeasurePreserving f.continuous.continuousAt
  · intro hp
    have hi : MeasurePreserving f.symm := MeasurePreserving.symm f.toMeasurableEquiv hq
    have hh := cover_boundary_preimage_image hi.quasiMeasurePreserving f.symm.continuous.continuousAt
      (A := f ⁻¹' A) (p := f p)
    have he : f.symm ⁻¹' (f ⁻¹' A) = A := by ext x; simp
    rw [he] at hh
    simpa only [f.symm_apply_apply] using hh hp

theorem connected_cover_phase {A s : Set Cover} (hA : MeasurableSet A)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (coverEssentialBoundary A)) :
    volume (s ∩ A) = 0 ∨ volume (s ∩ Aᶜ) = 0 := by
  rw [coverEssentialBoundary_eq_support] at hd
  let U := (volume.restrict A).supportᶜ
  let W := (volume.restrict Aᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict A).support ∪ (volume.restrict Aᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hA,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict A).supportᶜ ∩ (volume.restrict Aᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    exact not_and_or.mp (fun hb ↦ Set.disjoint_left.mp hd hx hb)
  have hnullA (h : s ⊆ U) : volume (s ∩ A) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Aᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullA (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_halfballs_null {A : Set Cover} {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) = 0)
    (hr : volume ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) = 0) :
    volume (Metric.ball (0 : Cover) r ∩ A) = 0 := by
  apply measure_mono_null (t := ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ A) ∪
    ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ A) ∪ {y | ⟪n,y⟫ = 0}) ?_
    (measure_union_null (measure_union_null hl hr) (hyperplane_volume_zero hn))
  intro y hy
  rcases lt_trichotomy ⟪n,y⟫ 0 with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨hy.1,hh⟩,hy.2⟩)
  · exact Or.inr hh
  · exact Or.inl (Or.inr ⟨⟨hy.1,hh⟩,hy.2⟩)

lemma cover_opposite_halfballs_model {C : Set Cover} {n : Cover} (hn : ‖n‖ = 1) {r : ℝ}
    (hl : volume ((Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) = 0)
    (hr : volume ((Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) = 0) :
    ∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ 0 < ⟪n,y⟫) := by
  have hal : ∀ᵐ y : Cover ∂volume, ¬(y ∈ (Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}) ∩ C) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hl
  have har : ∀ᵐ y : Cover ∂volume, ¬(y ∈ (Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}) ∩ Cᶜ) := by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hr
  have han : ∀ᵐ y : Cover ∂volume, ⟪n,y⟫ ≠ 0 := by
    simpa only [ae_iff,not_not] using hyperplane_volume_zero hn
  filter_upwards [hal,har,han] with y hl hr hne hy
  constructor
  · intro hc
    by_contra hpos
    exact hl ⟨⟨hy,lt_of_le_of_ne (not_lt.mp hpos) hne⟩,hc⟩
  · intro hpos
    by_contra hnc
    exact hr ⟨⟨hy,hpos⟩,hnc⟩

theorem cover_boundary_plane_phases {C : Set Cover} (hC : MeasurableSet C)
    {r : ℝ} {n : Cover} (hn : ‖n‖ = 1)
    (hbd : ∀ y : Cover, y ∈ Metric.ball (0 : Cover) r → y ∈ coverEssentialBoundary C → ⟪n,y⟫ = 0)
    (hpos : 0 < volume (Metric.ball (0 : Cover) r ∩ C))
    (hneg : 0 < volume (Metric.ball (0 : Cover) r ∩ Cᶜ)) :
    (∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ 0 < ⟪n,y⟫)) ∨
    (∀ᵐ y : Cover ∂volume, y ∈ Metric.ball (0 : Cover) r → (y ∈ C ↔ ⟪n,y⟫ < 0)) := by
  let U := Metric.ball (0 : Cover) r ∩ {y | ⟪n,y⟫ < 0}
  let W := Metric.ball (0 : Cover) r ∩ {y | 0 < ⟪n,y⟫}
  have hU : MeasurableSet U := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet
  have hW : MeasurableSet W := Metric.isOpen_ball.measurableSet.inter
    (isOpen_lt continuous_const (innerSL ℝ n).continuous).measurableSet
  have hcU : IsPreconnected U := ((convex_ball (0 : Cover) r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hcW : IsPreconnected W := ((convex_ball (0 : Cover) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (innerSL ℝ n).toLinearMap)).isPreconnected
  have hdU : Disjoint U (coverEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_lt hy.2) (hbd y hy.1 he)
  have hdW : Disjoint W (coverEssentialBoundary C) := by
    rw [Set.disjoint_left]
    intro y hy he
    exact (ne_of_gt hy.2) (hbd y hy.1 he)
  rcases connected_cover_phase hC hU hcU hdU with hu|hu <;>
    rcases connected_cover_phase hC hW hcW hdW with hw|hw
  · exact ((ne_of_gt hpos) (cover_halfballs_null hn hu hw)).elim
  · exact Or.inl (cover_opposite_halfballs_model hn hu hw)
  · apply Or.inr
    have hneg : ‖-n‖ = 1 := by simpa using hn
    have hh := cover_opposite_halfballs_model hneg
      (by simpa only [inner_neg_left,neg_lt_zero] using hw)
      (by simpa only [inner_neg_left,neg_pos] using hu)
    simpa only [inner_neg_left,neg_pos] using hh
  · exact ((ne_of_gt hneg) (cover_halfballs_null hn hu hw)).elim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cover_flattened_boundary_phases {A U : Set Cover} (hA : MeasurableSet A)
    (f : Cover ≃ₜ Cover) (hmp : MeasurePreserving f) {n : Cover} (hn : ‖n‖ = 1)
    (hU : U ∈ 𝓝 (f 0)) (hp : f 0 ∈ coverEssentialBoundary A)
    (hbd : ∀ x : Cover, f x ∈ U → f x ∈ coverEssentialBoundary A → ⟪n,x⟫ = 0) :
    ∃ W : Set Cover, IsOpen W ∧ f 0 ∈ W ∧ W ⊆ U ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ 0 < ⟪n,f.symm x⟫)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ ⟪n,f.symm x⟫ < 0))) := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (f.continuous.continuousAt.preimage_mem_nhds hU)
  let C := f ⁻¹' A
  have hC : MeasurableSet C := hA.preimage f.continuous.measurable
  have h0 : (0 : Cover) ∈ coverEssentialBoundary C := (cover_boundary_measurePreserving_homeomorph f hmp 0).mpr hp
  have hh := h0 r hr
  have hpos : 0 < volume (Metric.ball (0 : Cover) r ∩ C) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hh.1).1
  have hneg : 0 < volume (Metric.ball (0 : Cover) r ∩ Cᶜ) := by
    rw [inter_comm]
    exact (ENNReal.toReal_pos_iff.mp hh.2).1
  have hplanes : ∀ x : Cover, x ∈ Metric.ball (0 : Cover) r → x ∈ coverEssentialBoundary C → ⟪n,x⟫=0 :=
    fun x hx hb ↦ hbd x (hsub hx) ((cover_boundary_measurePreserving_homeomorph f hmp x).mp hb)
  have hinv := (MeasurePreserving.symm f.toMeasurableEquiv hmp).quasiMeasurePreserving
  refine ⟨f '' Metric.ball (0 : Cover) r, f.isOpenMap _ Metric.isOpen_ball,
    ⟨0,by simpa using hr,rfl⟩,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact hsub hy
  · rcases cover_boundary_plane_phases hC hn hplanes hpos hneg with h|h
    · left
      filter_upwards [hinv.ae h] with x hx
      intro hW
      obtain ⟨y,hy,rfl⟩ := hW
      change f.symm (f y) ∈ Metric.ball (0 : Cover) r → (f.symm (f y) ∈ C ↔ 0 < ⟪n,f.symm (f y)⟫) at hx
      have hh := hx (by simpa using hy)
      change (f.symm (f y) ∈ C ↔ _) at hh
      simpa only [f.symm_apply_apply,C,Set.mem_preimage] using hh
    · right
      filter_upwards [hinv.ae h] with x hx
      intro hW
      obtain ⟨y,hy,rfl⟩ := hW
      change f.symm (f y) ∈ Metric.ball (0 : Cover) r → (f.symm (f y) ∈ C ↔ ⟪n,f.symm (f y)⟫ < 0) at hx
      have hh := hx (by simpa using hy)
      change (f.symm (f y) ∈ C ↔ _) at hh
      simpa only [f.symm_apply_apply,C,Set.mem_preimage] using hh

def graphSignedHeight (a n : Cover) (g : Plane → ℝ) (x : Cover) : ℝ :=
  ⟪n,x-a⟫-graphHeightExtension a n g x

lemma graphSignedHeight_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSignedHeight a n g (graphShear a n g x) = ⟪n,x-a⟫ := by
  unfold graphSignedHeight graphHeightExtension
  rw [graphShear_projection a hn]
  simp only [graphShear,normalMove,graphHeightExtension,add_sub_right_comm,
    inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  ring

lemma graphSignedHeight_graph {a n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ)
    {x : Cover} (hx : normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    graphSignedHeight a n g x = 0 := by
  have hh := congrArg (fun z : Cover ↦ ⟪n,z⟫) hx
  rw [normalGraph_inner hn] at hh
  exact sub_eq_zero.mpr hh.symm

theorem cover_graph_boundary_phases {A U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {p : Cover} (hU : U ∈ 𝓝 p) (hp : p ∈ coverEssentialBoundary A)
    (hbd : ∀ x ∈ U, x ∈ coverEssentialBoundary A →
      normalGraph n g (normalPlaneCoordinates n (x-a))=x-a) :
    ∃ W : Set Cover, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      ((∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ 0 < graphSignedHeight a n g x)) ∨
       (∀ᵐ x : Cover ∂volume, x ∈ W → (x ∈ A ↔ graphSignedHeight a n g x < 0))) := by
  let h := graphShearHomeomorph a hn hg
  let q := h.symm p
  let f := (Homeomorph.addLeft q).trans h
  have hf0 : f 0 = p := by simp [f,q]
  have hmp : MeasurePreserving f :=
    (graphShear_measurePreserving a hn hg.measurable).comp (measurePreserving_add_left volume q)
  have hq : ⟪n,q-a⟫ = 0 := by
    have hh := graphSignedHeight_graph hn g (hbd p (mem_of_mem_nhds hU) hp)
    have he := graphSignedHeight_shear a hn g q
    change graphSignedHeight a n g (h q) = _ at he
    rw [show h q = p from h.apply_symm_apply p] at he
    exact he.symm.trans hh
  have he (x : Cover) : graphSignedHeight a n g (f x) = ⟪n,x⟫ := by
    change graphSignedHeight a n g (graphShear a n g (q+x)) = _
    rw [graphSignedHeight_shear a hn,add_sub_right_comm,inner_add_right,hq,zero_add]
  have hbd' (x : Cover) (hx : f x ∈ U) (hb : f x ∈ coverEssentialBoundary A) : ⟪n,x⟫=0 := by
    rw [← he]
    exact graphSignedHeight_graph hn g (hbd _ hx hb)
  obtain ⟨W,hW,hpW,hWU,hph⟩ := cover_flattened_boundary_phases hA f hmp hn
    (by simpa only [hf0] using hU) (by simpa only [hf0] using hp) hbd'
  refine ⟨W,hW,by simpa only [hf0] using hpW,hWU,?_⟩
  have hei (x : Cover) : ⟪n,f.symm x⟫ = graphSignedHeight a n g x := by
    rw [← he,f.apply_symm_apply]
  simpa only [hei] using hph

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def dilatedGraph (s : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ := s*g (s⁻¹ • y)

lemma normalGraph_dilated (n : Cover) (g : Plane → ℝ) {s : ℝ} (hs : s ≠ 0) (y : Plane) :
    normalGraph n (dilatedGraph s g) y = s • normalGraph n g (s⁻¹ • y) := by
  unfold normalGraph dilatedGraph
  simp only [smul_add,smul_smul]
  change normalPlaneLinearIsometry n y+_ = s • normalPlaneLinearIsometry n (s⁻¹ • y)+_
  rw [map_smul,smul_smul,mul_inv_cancel₀ hs,one_smul]

lemma dilatedGraph_lipschitz {g : Plane → ℝ} (hg : LipschitzWith (1/4) g)
    {s : ℝ} (hs : 0 < s) : LipschitzWith (1/4) (dilatedGraph s g) := by
  change LipschitzWith (1/4) (fun y : Plane ↦ s*g (s⁻¹ • y))
  convert rescaled_lipschitz_graph hg (inv_pos.mpr hs) using 1
  simp only [inv_inv]

lemma dilatedGraph_contDiffAt {g : Plane → ℝ} {s : ℝ} {y : Plane}
    (hg : ContDiffAt ℝ 1 g (s⁻¹ • y)) : ContDiffAt ℝ 1 (dilatedGraph s g) y :=
  contDiffAt_const.mul (hg.comp y (contDiffAt_id.const_smul s⁻¹))

end CubicTorus
end
end
end

end OAI
