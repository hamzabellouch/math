import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoordinateGradientPairScalarCorrection

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def chartGradientField (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    (i : CoordIndex E) (y : E) : ℝ :=
  coordinateFlux (Module.finBasis ℝ E) (fun z => (metricCoefficients g p z)⁻¹)
    (u ∘ (chartAt E p).symm) i y

lemma chartGradientField_smooth {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    (i : CoordIndex E) :
    ContDiffOn ℝ ∞ (chartGradientField g u p i) (chartAt E p).target := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  unfold chartGradientField coordinateFlux
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).mul
    (((contDiffAt_inChart hu p hy).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const)

lemma coordinateDivergence_chartGradient (g : SmoothMetric E M) (u : M → ℝ) (p : M) :
    coordinateDivergence (Module.finBasis ℝ E)
      (fun y => Real.sqrt (metricCoefficients g p y).det) (chartGradientField g u p) =
      localLaplacian g u p := rfl

lemma scalarCorrectionDenominator_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionD g n u ((chartAt E p).symm y) =
      scalarCorrectionDenominator (Module.finBasis ℝ E) n
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionD
  rw [coordinateGradientPair_inChart hu hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  rfl

lemma scalarCorrectionRatio_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionF g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionRatio (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionF scalarCorrectionRatio
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy, scalarCorrectionDenominator_inChart hu g n p hy]
  rfl

lemma weightedLaplacian_chartGradient {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    weightedLaplacian g f u ((chartAt E p).symm y) =
      coordinateDivergence (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det)
        (fun i z => f ((chartAt E p).symm z)*chartGradientField g u p i z) y := by
  have hρ := (contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)
  have hρp := Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)
  rw [coordinateDivergence_mul (Module.finBasis ℝ E)
    (fun z => Real.sqrt (metricCoefficients g p z).det)
    (fun z => f ((chartAt E p).symm z)) (chartGradientField g u p) y
    (hρ.differentiableAt (by simp)) ((contDiffAt_inChart hf p hy).differentiableAt (by simp))
    (fun i => ((chartGradientField_smooth hu g p i).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)) hρp.ne']
  rw [weightedLaplacian_expansion
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    coordinateGradientPair_inChart hf hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  rfl

lemma scalarCorrectionB_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionB g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionB (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  unfold intrinsicCorrectionB scalarCorrectionB
  rw [scalarCorrectionRatio_inChart hu g n Λ p hy]
  rfl

lemma scalarCorrectionS_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    intrinsicCorrectionS g n Λ u ((chartAt E p).symm y) =
      scalarCorrectionS (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) y := by
  have he : (fun z => intrinsicCorrectionF g n Λ u ((chartAt E p).symm z)) =ᶠ[𝓝 y]
      scalarCorrectionRatio (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) n Λ
        (u ∘ (chartAt E p).symm) (chartGradientField g u p) := by
    filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
    exact scalarCorrectionRatio_inChart hu g n Λ p hz
  have hed := coordinateDivergence_eventuallyEq (Module.finBasis ℝ E)
    (Filter.EventuallyEq.refl (𝓝 y) (fun z => Real.sqrt (metricCoefficients g p z).det))
    (fun i => he.mul (Filter.EventuallyEq.refl _ (chartGradientField g u p i)))
  unfold intrinsicCorrectionS scalarCorrectionS
  rw [weightedLaplacian_chartGradient (contMDiff_intrinsicCorrectionF hu g n Λ hD) hu g p hy]
  erw [hed.eq_of_nhds]
  rw [scalarCorrectionRatio_inChart hu g n Λ p hy]
  rfl

lemma coordinateGradientPair_nonneg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    0 ≤ coordinateGradientPair g u u x := by
  have hp := (metricCoefficients_posDef g x
    ((chartAt E x).map_source (mem_chart_source E x))).inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i))
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hp
  convert hp using 1; try rfl
  unfold coordinateGradientPair
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma intrinsicCorrectionD_lower (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    {n W : ℝ} {B : ℕ} (hn : 0 < n) (hW : 0 < W)
    (hjet : W/n^B ≤ |u x| + Real.sqrt (coordinateGradientPair g u u x)/n) :
    n^2*W^2/(2*n^(2*B)) ≤ intrinsicCorrectionD g n u x :=
  scalar_denominator_lower hn hW (coordinateGradientPair_nonneg g u x) hjet

lemma intrinsicCorrectionD_pos (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    {n W : ℝ} {B : ℕ} (hn : 0 < n) (hW : 0 < W)
    (hjet : W/n^B ≤ |u x| + Real.sqrt (coordinateGradientPair g u u x)/n) :
    0 < intrinsicCorrectionD g n u x :=
  (by positivity : 0 < n^2*W^2/(2*n^(2*B))).trans_le
    (intrinsicCorrectionD_lower g u x hn hW hjet)

lemma compact_derivative_bound_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact hK hO hKO hf
  obtain ⟨C,hC,hFC⟩ := compact_derivative_bound hK hF N
  refine ⟨C,hC,fun j hj x hx => ?_⟩
  have hex := he.filter_mono (nhds_le_nhdsSet hx)
  rw [(hex.iteratedFDeriv ℝ j).self_of_nhds]
  exact hFC j hj x hx

lemma geometric_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G R S : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*R^j)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*S^j) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ F*G*(R+S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hx hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hx hg
  have hb := geometric_product_jet_bound hf' hg' x h hF hG hR hS
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  change ‖iteratedFDeriv ℝ h (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hb

lemma norm_iteratedFDeriv_scalar_direction_on {O : Set E} (hO : IsOpen O)
    {x : E} (hx : x ∈ O) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (v : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) f x‖ := by
  obtain ⟨F,hF,he⟩ := smooth_extension_at hO hx hf
  have hd : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ F y v) :=
    (he.fderiv (𝕜:=ℝ)).mono (fun y hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy)
  rw [(hd.iteratedFDeriv ℝ k).self_of_nhds, (he.iteratedFDeriv ℝ (k+1)).self_of_nhds]
  exact norm_iteratedFDeriv_scalar_direction hF v k x

lemma chartGradientField_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^(k+4)*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^(k+5)*W := by
  let U := u ∘ (chartAt E p).symm
  have hU : ContDiffOn ℝ ∞ U (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hdi (j : CoordIndex E) : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  intro i k hk
  have hprod (j : CoordIndex E) :
      ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j *
        fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
      (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by
    have hder (l : ℕ) (hl : l ≤ k) :
        ‖iteratedFDeriv ℝ l (fun z => fderiv ℝ U z (Module.finBasis ℝ E j)) y‖ ≤
          ‖Module.finBasis ℝ E j‖*C*n^5*W*n^l := by
      calc
        _ ≤ ‖Module.finBasis ℝ E j‖*‖iteratedFDeriv ℝ (l+1) U y‖ :=
          norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
        _ ≤ ‖Module.finBasis ℝ E j‖*(C*n^((l+1)+4)*W) :=
          mul_le_mul_of_nonneg_left (huj (l+1) (by omega)) (norm_nonneg _)
        _ = _ := by rw [show l+1+4=5+l by omega,pow_add]; ring
    apply (geometric_product_jet_bound_on (chartAt E p).open_target hy
      (contDiffOn_metricInverse g p i j) (hdi j) k hA
      (show 0 ≤ ‖Module.finBasis ℝ E j‖*C*n^5*W by positivity) hn0 hn0
      (fun l hl => (haj i j l (hl.trans hk)).trans (by
        exact le_mul_of_one_le_right hA (one_le_pow₀ hn))) hder).trans
    rw [show n+n=2*n by ring,mul_pow]
    calc
      A*(‖Module.finBasis ℝ E j‖*C*n^5*W)*(2^k*n^k) =
          (2^k*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W := by rw [pow_add]; ring
      _ ≤ _ := by gcongr; norm_num
  unfold chartGradientField coordinateFlux
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    (((contDiffOn_metricInverse g p i j).mul (hdi j)).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, (2^h*A*C*‖Module.finBasis ℝ E j‖)*n^(k+5)*W :=
      Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_mul]

lemma compact_metric_scalar_coefficient_bounds (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧
      (∀ i j, ∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A) ∧
      (∀ k ≤ h+1, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => Real.sqrt (metricCoefficients g p z).det) y‖ ≤ A) ∧
      (∀ k ≤ h, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ k (fun z => (Real.sqrt (metricCoefficients g p z).det)⁻¹) y‖ ≤ A) := by
  classical
  choose a ha haj using fun i j => compact_derivative_bound_on hK
    (chartAt E p).open_target hKt (contDiffOn_metricInverse g p i j) (h+1)
  obtain ⟨b,hb,hbj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    (contDiffOn_metricDensity g p) (h+1)
  obtain ⟨c,hc,hcj⟩ := compact_derivative_bound_on hK (chartAt E p).open_target hKt
    ((contDiffOn_metricDensity g p).inv (fun z hz =>
      (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hz)).ne')) h
  let A := 1+b+c+∑ i, ∑ j, a i j
  have ha0 (i j : CoordIndex E) : 0 ≤ a i j := zero_le_one.trans (ha i j)
  have hs0 : 0 ≤ ∑ i, ∑ j, a i j := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => ha0 i j))
  refine ⟨A,by dsimp only [A]; linarith,?_,?_,?_⟩
  · intro i j k hk y hy
    apply (haj i j k hk y hy).trans
    have hai : a i j ≤ ∑ j, a i j :=
      Finset.single_le_sum (fun j _ => ha0 i j) (Finset.mem_univ j)
    have haj' : (∑ j, a i j) ≤ ∑ i, ∑ j, a i j :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => ha0 i j)) (Finset.mem_univ i)
    dsimp only [A]
    linarith
  · intro k hk y hy
    exact (hbj k hk y hy).trans (by dsimp only [A]; linarith)
  · intro k hk y hy
    exact (hcj k hk y hy).trans (by dsimp only [A]; linarith)

theorem quantitative_intrinsic_correction_on_compact_chart
    (g : SmoothMetric E M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target)
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ L > 0, ∀ n : ℝ, 1 ≤ n → ∀ D : ℕ, ∀ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u → ∀ W : M → ℝ,
      (∀ x, 0 < W x) →
      (∀ x, W x/n^B ≤ |u x|+Real.sqrt (coordinateGradientPair g u u x)/n) →
      (∀ y ∈ K, ∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) y‖ ≤
        C*n^(j+4)*W ((chartAt E p).symm y)) →
      (∀ y ∈ K, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
        ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E p).symm) y‖ ≤
        C*n^4/(n^D)*W ((chartAt E p).symm y)) →
      ∀ y ∈ K, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j
          ((fun x => intrinsicCorrectionB g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) y‖+
        ‖iteratedFDeriv ℝ j
          ((fun x => intrinsicCorrectionS g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) y‖ ≤
        L*n^((2*B+21)*(h+2)+10)/(n^D) := by
  obtain ⟨A,hA,haj,hρj,hρij⟩ := compact_metric_scalar_coefficient_bounds g p hK hKt h
  let CX : ℝ := 2^(h+1)*A*C*(∑ j, ‖Module.finBasis ℝ E j‖)
  have hCX : 0 ≤ CX := by dsimp only [CX]; positivity
  let C' := C+A+CX+1
  have hC' : 0 < C' := by dsimp only [C']; linarith
  have hCC : C ≤ C' := by dsimp only [C']; linarith
  have hAC : A ≤ C' := by dsimp only [C']; linarith
  have hXC : CX ≤ C' := by dsimp only [C']; linarith
  obtain ⟨L,hL,hLj⟩ := quantitative_scalar_correction_jets_on (Module.finBasis ℝ E)
    (fun z => Real.sqrt (metricCoefficients g p z).det) (chartAt E p).open_target
    (contDiffOn_metricDensity g p) (fun z hz => Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hz)) h B hC'
  refine ⟨L,hL,?_⟩
  intro n hn D u hu W hW hnc huj hRj y hy j hj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hWy : 0 ≤ W ((chartAt E p).symm y) := (hW _).le
  have hD (x : M) : intrinsicCorrectionD g n u x ≠ 0 :=
    (intrinsicCorrectionD_pos g u x hn0 (hW x) (hnc x)).ne'
  have hU : ContDiffOn ℝ ∞ (u ∘ (chartAt E p).symm) (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hb := hLj n hn D (u ∘ (chartAt E p).symm) (chartGradientField g u p) hU
    (chartGradientField_smooth hu g p)
    (fun z hz => (scalarCorrectionDenominator_inChart hu g n p hz) ▸ hD ((chartAt E p).symm z))
    y (hKt hy) (W ((chartAt E p).symm y)) (hW _) ?_ ?_ ?_ ?_
    (fun k hk => (hρj k hk y hy).trans hAC) (fun k hk => (hρij k hk y hy).trans hAC) j hj
  · have heB : ((fun x => intrinsicCorrectionB g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) =ᶠ[𝓝 y]
        (fun z => scalarCorrectionB (Module.finBasis ℝ E)
          (fun z => Real.sqrt (metricCoefficients g p z).det) n (n*(n+2))
          (u ∘ (chartAt E p).symm) (chartGradientField g u p) z-1) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      exact congrArg (fun t : ℝ => t-1) (scalarCorrectionB_inChart hu g n (n*(n+2)) p hz)
    have heS : ((fun x => intrinsicCorrectionS g n (n*(n+2)) u x-1) ∘ (chartAt E p).symm) =ᶠ[𝓝 y]
        (fun z => scalarCorrectionS (Module.finBasis ℝ E)
          (fun z => Real.sqrt (metricCoefficients g p z).det) n (n*(n+2))
          (u ∘ (chartAt E p).symm) (chartGradientField g u p) z-1) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      exact congrArg (fun t : ℝ => t-1) (scalarCorrectionS_inChart hu g n (n*(n+2)) hD p hz)
    rw [(heB.iteratedFDeriv ℝ j).self_of_nhds,(heS.iteratedFDeriv ℝ j).self_of_nhds]
    exact hb
  · rw [← scalarCorrectionDenominator_inChart hu g n p (hKt hy)]
    apply le_trans ?_ (intrinsicCorrectionD_lower g u ((chartAt E p).symm y) hn0 (hW _) (hnc _))
    calc
      _ = 1*(W ((chartAt E p).symm y))^2/(2*n^(2*B)) := by ring
      _ ≤ _ := by gcongr; exact one_le_pow₀ hn
  · intro k hk
    exact (huj y hy k hk).trans (by gcongr)
  · intro i k hk
    exact (chartGradientField_jet_bound hu g p (hKt hy) (h+1) hn (hW _) hC.le
      (zero_le_one.trans hA) (fun i j k hk => haj i j k hk y hy)
      (fun k hk => huj y hy k (by omega)) i k hk).trans (by change CX*_ * _ ≤ _; gcongr)
  · intro k hk
    have he : (fun z => coordinateDivergence (Module.finBasis ℝ E)
        (fun z => Real.sqrt (metricCoefficients g p z).det) (chartGradientField g u p) z+
        n*(n+2)*(u ∘ (chartAt E p).symm) z) =ᶠ[𝓝 y]
        ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E p).symm) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds (hKt hy)] with z hz
      dsimp only [Function.comp_apply]
      rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hz), (chartAt E p).right_inv hz]
      rfl
    rw [(he.iteratedFDeriv ℝ k).self_of_nhds]
    exact (hRj y hy k hk).trans (by gcongr)


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

def scalarChartSupport (i : A.t) : Set E :=
  (chartAt E (A.p i)) '' tsupport (A.η i)

omit [T2Space M] in
lemma scalarChartSupport_compact (i : A.t) : IsCompact (A.scalarChartSupport i) :=
  isCompact_chartSupport (E:=E) (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i)

omit [T2Space M] [CompactSpace M] in
lemma scalarChartSupport_target (i : A.t) :
    A.scalarChartSupport i ⊆ (chartAt E (A.p i)).target :=
  image_subset_iff.mpr (fun _x hx => (chartAt E (A.p i)).map_source (A.chart_η i hx))

omit [T2Space M] in
theorem quantitative_intrinsic_correction_jets
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ L > 0, ∀ n : ℝ, 1 ≤ n → ∀ D : ℕ, ∀ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u → ∀ W : M → ℝ,
      (∀ x, 0 < W x) →
      (∀ x, W x/n^B ≤ |u x|+Real.sqrt (coordinateGradientPair g u u x)/n) →
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (u ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*n^(j+4)*W ((chartAt E (A.p i)).symm y)) →
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g u x+n*(n+2)*u x) ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*n^4/(n^D)*W ((chartAt E (A.p i)).symm y)) →
      A.ChartJetBound h (fun x => ((intrinsicCorrectionB g n (n*(n+2)) u x-1 : ℝ) : ℂ))
        (L*n^((2*B+21)*(h+2)+10)/(n^D)) ∧
      A.ChartJetBound h (fun x => ((intrinsicCorrectionS g n (n*(n+2)) u x-1 : ℝ) : ℂ))
        (L*n^((2*B+21)*(h+2)+10)/(n^D)) ∧
      (∀ x, |intrinsicCorrectionB g n (n*(n+2)) u x-1|+
        |intrinsicCorrectionS g n (n*(n+2)) u x-1| ≤
        L*n^((2*B+21)*(h+2)+10)/(n^D)) := by
  classical
  choose L hL hLjet using fun i : A.t =>
    quantitative_intrinsic_correction_on_compact_chart g (A.p i)
      (A.scalarChartSupport_compact i) (A.scalarChartSupport_target i) h B hC
  choose T hT hTjet using fun i : A.t =>
    localized_real_chart_jet_bound (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
      (A.chart_η i) (A.smooth_η i) h
  let L₀ : ℝ := 1+∑ i : A.t, (T i+1)*L i
  have hL₀ : 0 < L₀ := by
    have hsum : 0 ≤ ∑ i : A.t, (T i+1)*L i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (by linarith [hT i]) (hL i).le)
    dsimp only [L₀]
    linarith
  have hiL' (i : A.t) : (T i+1)*L i ≤ L₀ := by
    apply (Finset.single_le_sum (fun j _ => mul_nonneg (by linarith [hT j]) (hL j).le)
      (Finset.mem_univ i)).trans
    dsimp only [L₀]
    linarith
  have hiL (i : A.t) : T i*L i ≤ L₀ := (by nlinarith [hL i] : T i*L i ≤ (T i+1)*L i).trans (hiL' i)
  have hiLraw (i : A.t) : L i ≤ L₀ := (by nlinarith [hT i,hL i] : L i ≤ (T i+1)*L i).trans (hiL' i)
  refine ⟨L₀,hL₀,?_⟩
  intro n hn D u hu W hW hnc huj hRj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hD (x : M) : intrinsicCorrectionD g n u x ≠ 0 :=
    (intrinsicCorrectionD_pos g u x hn0 (hW x) (hnc x)).ne'
  obtain ⟨hb,hsmooth,heq⟩ := intrinsic_scalar_correction hu g n (n*(n+2))
    (by positivity) hD
  have hraw := fun i => hLjet i n hn D u hu W hW hnc (huj i) (hRj i)
  have hloc (i : A.t) (f : M → ℝ)
      (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
      (hjf : ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (f ∘ (chartAt E (A.p i)).symm) y‖ ≤
          L i*n^((2*B+21)*(h+2)+10)/n^D) :
      ∀ j ≤ h, ∀ y : E,
        ‖iteratedFDeriv ℝ j (chartLocalize (E:=E) (A.p i) (A.η i) (fun x => (f x : ℂ))) y‖ ≤
          L₀*n^((2*B+21)*(h+2)+10)/n^D := by
    intro j hj y
    apply (hTjet i f hf _ (div_nonneg (mul_nonneg (hL i).le (pow_nonneg hn0.le _))
      (pow_nonneg hn0.le _)) hjf y j hj).trans
    calc
      T i*(L i*n^((2*B+21)*(h+2)+10)/n^D) =
        (T i*L i)*n^((2*B+21)*(h+2)+10)/n^D := by ring
      _ ≤ _ := by gcongr; exact hiL i
  refine ⟨?_,?_,?_⟩
  · intro i j hj y
    exact hloc i _ (hb.sub contMDiff_const)
      (fun z hz l hl => (le_add_of_nonneg_right (norm_nonneg _)).trans (hraw i z hz l hl)) j hj y
  · intro i j hj y
    exact hloc i _ (hsmooth.sub contMDiff_const)
      (fun z hz l hl => (le_add_of_nonneg_left (norm_nonneg _)).trans (hraw i z hz l hl)) j hj y
  · intro x
    have hi : ∃ i : A.t, A.η i x ≠ 0 := by
      by_contra hno
      push Not at hno
      have hz : (∑ i : A.t, A.η i x)=0 := Finset.sum_eq_zero (fun i _ => hno i)
      rw [A.sum_η x] at hz
      exact one_ne_zero hz
    obtain ⟨i,hi⟩ := hi
    have hxη : x ∈ tsupport (A.η i) := subset_tsupport _ hi
    have hxs : x ∈ (chartAt E (A.p i)).source := A.chart_η i hxη
    have hbnd := hraw i ((chartAt E (A.p i)) x) ⟨x,hxη,rfl⟩ 0 (Nat.zero_le h)
    simp only [norm_iteratedFDeriv_zero,Function.comp_apply,
      (chartAt E (A.p i)).left_inv hxs,Real.norm_eq_abs] at hbnd
    exact hbnd.trans (by gcongr; exact hiLraw i)
end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
section ProjectionJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma weighted_quotient_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f d : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hd : ContDiffOn ℝ ∞ d O)
    (h : ℕ) {δ W M N R S : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hN : 0 ≤ N) (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : δ*W^2 ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ N*R^j*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ M*S^j*W^2) :
    ‖iteratedFDeriv ℝ h (fun y => f y/d y) x‖ ≤
      N*(h.factorial : ℝ)^2/δ*(R+max 1 (M/δ)*S)^h := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨d',hd',hdp,hde⟩ := positive_smooth_extension_at hO hxO hd
    ((by positivity : 0 < δ*W^2).trans_le hx)
  have hq := weighted_quotient_jet_bound hf' hd' (fun y => (hdp y).ne') x h hδ hW
    hN hR hS (hde.self_of_nhds ▸ hx)
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj hjh => (hde.iteratedFDeriv ℝ j).self_of_nhds ▸ hdj j hj hjh)
  change ‖iteratedFDeriv ℝ h (f/d) x‖ ≤ _
  rw [(hfe.div hde).iteratedFDeriv ℝ h |>.self_of_nhds]
  exact hq

variable {ι : Type*} [Fintype ι]

theorem rankOne_projection_jet_bound_on (X α : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hα : ∀ i, ContDiffOn ℝ ∞ (α i) O)
    (h : ℕ) {δ W n C B : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : δ*W^2 ≤ ∑ i, α i x*X i x)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^j*W)
    (hαj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (α i) x‖ ≤ B*n^j*W)
    (i j : ι) :
    ‖iteratedFDeriv ℝ h
      (fun y => X i y*α j y/(∑ l, α l y*X l y)) x‖ ≤
      (C*B*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))^h)*n^h := by
  have hprod (i j : ι) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => X i y*α j y) x‖ ≤ C*B*(2*n)^k*W^2 := by
    have hh := geometric_product_jet_bound_on hO hxO (hX i) (hα j) k
      (show 0 ≤ C*W by positivity) (show 0 ≤ B*W by positivity) hn hn
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hXj i l (hl.trans hk))
      (fun l hl => by simpa only [mul_assoc,mul_comm,mul_left_comm] using hαj j l (hl.trans hk))
    convert hh using 1; ring
  have hden : ContDiffOn ℝ ∞ (fun y => ∑ l, α l y*X l y) O :=
    ContDiffOn.sum (fun l _ => (hα l).mul (hX l))
  have hdenj (k : ℕ) (_hk : 1 ≤ k) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (fun y => ∑ l, α l y*X l y) x‖ ≤
        ((Fintype.card ι:ℝ)*C*B)*(2*n)^k*W^2 := by
    rw [iteratedFDeriv_fun_sum_apply (fun l _ =>
      (((hα l).mul (hX l)).contDiffAt (hO.mem_nhds hxO)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))))]
    calc
      _ ≤ ∑ l : ι, ‖iteratedFDeriv ℝ k (fun y => α l y*X l y) x‖ := norm_sum_le _ _
      _ ≤ ∑ l : ι, C*B*(2*n)^k*W^2 := by
        apply Finset.sum_le_sum
        intro l _
        simpa only [mul_comm] using hprod l l k hk
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hq := weighted_quotient_jet_bound_on hO hxO ((hX i).mul (hα j)) hden h hδ hW
    (mul_nonneg hC hB) (show 0 ≤ 2*n by positivity) (show 0 ≤ 2*n by positivity)
    hx (hprod i j) hdenj
  convert hq using 1
  rw [show 2*n+max 1 ((Fintype.card ι:ℝ)*C*B/δ)*(2*n) =
    (2+2*max 1 ((Fintype.card ι:ℝ)*C*B/δ))*n by ring,mul_pow]
  ring
end ProjectionJets

open scoped Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def chartGradientProjection (g : SmoothMetric E M) (u : M → ℝ) (p : M)
    (i j : CoordIndex E) (y : E) : ℝ :=
  chartGradientField g u p i y *
    fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) /
      localGradientPair g u u p y

lemma chartGradientField_sharp_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {n W C A : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W) :
    ∀ i, ∀ k ≤ h, ‖iteratedFDeriv ℝ k (chartGradientField g u p i) y‖ ≤
      (2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖))*n^k*(n*W) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hh := chartGradientField_jet_bound hu g p hy h hn
    (show 0 < W/n^4 by positivity) hC hA haj
    (fun k hk => (huj k hk).trans_eq (by rw [pow_add]; field_simp))
  intro i k hk
  apply (hh i k hk).trans_eq
  rw [show k+5=k+1+4 by omega,pow_add,pow_succ]
  field_simp

theorem chartGradientProjection_jet_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (p : M)
    {y : E} (hy : y ∈ (chartAt E p).target) (h : ℕ) {δ n W C A L : ℝ}
    (hδ : 0 < δ) (hn : 1 ≤ n) (hW : 0 < W)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (he : ∀ i, ‖Module.finBasis ℝ E i‖ ≤ L)
    (haj : ∀ i j, ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun z => (metricCoefficients g p z)⁻¹ i j) y‖ ≤ A)
    (huj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (u ∘ (chartAt E p).symm) y‖ ≤ C*n^k*W)
    (hgrad : δ*(n*W)^2 ≤ coordinateGradientPair g u u ((chartAt E p).symm y)) :
    let K := 2^h*A*C*(∑ j, ‖Module.finBasis ℝ E j‖)
    ∀ i j, ‖iteratedFDeriv ℝ h (chartGradientProjection g u p i j) y‖ ≤
      (K*(C*L)*(h.factorial:ℝ)^2/δ*
        (2+2*max 1 ((Fintype.card (CoordIndex E):ℝ)*K*(C*L)/δ))^h)*n^h := by
  intro K i j
  let α := fun i z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E i)
  have hα (i : CoordIndex E) : ContDiffOn ℝ ∞ (α i) (chartAt E p).target := by
    intro z hz
    exact (((contDiffAt_inChart hu p hz).fderiv_right (m:=∞) (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hU : ContDiffOn ℝ ∞ (u ∘ (chartAt E p).symm) (chartAt E p).target :=
    fun z hz => (contDiffAt_inChart hu p hz).contDiffWithinAt
  have hαj (i : CoordIndex E) (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k (α i) y‖ ≤ (C*L)*n^k*(n*W) := by
    calc
      _ ≤ ‖Module.finBasis ℝ E i‖*‖iteratedFDeriv ℝ (k+1) (u ∘ (chartAt E p).symm) y‖ :=
        norm_iteratedFDeriv_scalar_direction_on (chartAt E p).open_target hy hU _ _
      _ ≤ L*(C*n^(k+1)*W) := mul_le_mul (he i) (huj (k+1) (by omega))
        (norm_nonneg _) hL
      _ = _ := by rw [pow_succ]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpair (z : E) : localGradientPair g u u p z =
      ∑ l, α l z*chartGradientField g u p l z := rfl
  have hg : δ*(n*W)^2 ≤ ∑ l, α l y*chartGradientField g u p l y := by
    rw [coordinateGradientPair_inChart hu hu g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy,hpair] at hgrad
    exact hgrad
  have hh := rankOne_projection_jet_bound_on (chartGradientField g u p) α
    (chartAt E p).open_target hy (chartGradientField_smooth hu g p) hα h hδ
    (mul_pos (zero_lt_one.trans_le hn) hW) (zero_le_one.trans hn) hK
    (mul_nonneg hC hL) hg (chartGradientField_sharp_jet_bound hu g p hy h hn hW hC hA haj huj)
    hαj i j
  have hfun : chartGradientProjection g u p i j =
      (fun z => chartGradientField g u p i z*α j z/(∑ l, α l z*chartGradientField g u p l z)) := by
    funext z
    rw [chartGradientProjection,hpair]
  rw [hfun]
  exact hh

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma sharp_conjugate_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f w : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hw : ContDiffOn ℝ ∞ w O)
    (h : ℕ) {δ W n C D : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hn : 1 ≤ n)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : δ ≤ w x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ C*n^j*W)
    (hwj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j w x‖ ≤ D) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/w y) x‖ ≤
      (C*(h.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^h)*n^j*W := by
  intro j hj
  have hh := weighted_quotient_jet_bound_on hO hxO hf hw j hδ zero_lt_one
    (show 0 ≤ C*W by positivity) (zero_le_one.trans hn) (zero_le_one.trans hn)
    (by simpa only [one_pow,mul_one] using hx)
    (fun k hk => by simpa only [one_pow,mul_one,mul_assoc,mul_comm,mul_left_comm] using
        (hfj k (hk.trans hj))) (fun k hk hkj => by
      calc
        _ ≤ D := hwj k hk (hkj.trans hj)
        _ ≤ D*n^k*1^2 := by
          simpa only [one_pow,mul_one] using
            (le_mul_of_one_le_right hD (one_le_pow₀ hn)))
  have hp : (j.factorial:ℝ)^2 ≤ (h.factorial:ℝ)^2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Nat.factorial_le hj
  have hR : 1 ≤ 1+max 1 (D/δ) := by have := le_max_left (1:ℝ) (D/δ); linarith
  calc
    _ ≤ (C*W)*(j.factorial:ℝ)^2/δ*(n+max 1 (D/δ)*n)^j := hh
    _ = (C*(j.factorial:ℝ)^2/δ*(1+max 1 (D/δ))^j)*n^j*W := by
      rw [show n+max 1 (D/δ)*n=(1+max 1 (D/δ))*n by ring,mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hn) _)
      exact mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hδ.le)
        (pow_le_pow_right₀ hR hj) (pow_nonneg (zero_le_one.trans hR) _)
        (div_nonneg (mul_nonneg hC (sq_nonneg _)) hδ.le)

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientProjection_smooth_on (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M)
    {O : Set E} (_hO : IsOpen O) (hOT : O ⊆ (chartAt E p).target)
    (hF : ∀ y ∈ O, coordinateGradientPair g u u ((chartAt E p).symm y) ≠ 0)
    (i j : CoordIndex E) : ContDiffOn ℝ ∞ (chartGradientProjection g u p i j) O := by
  intro y hy
  have hα : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y :=
    ((contDiffAt_inChart hu p (hOT hy)).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const
  have hgp : ContDiffAt ℝ ∞ (localGradientPair g u u p) y := by
    apply (contDiffAt_inChart (contMDiff_coordinateGradientPair hu hu g) p (hOT hy)).congr_of_eventuallyEq
    filter_upwards [(chartAt E p).open_target.mem_nhds (hOT hy)] with z hz
    exact localGradientPair_eq_global hu g p hz
  have hgp0 : localGradientPair g u u p y ≠ 0 := by
    rw [localGradientPair_eq_global hu g p (hOT hy)]
    exact hF y hy
  exact ((((chartGradientField_smooth hu g p i).contDiffAt
    ((chartAt E p).open_target.mem_nhds (hOT hy))).mul hα).div hgp hgp0).contDiffWithinAt


end YauCounterexamples
end

end OAI
