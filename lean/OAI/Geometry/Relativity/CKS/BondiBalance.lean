import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CompactMetricCoercivity
import OAI.Geometry.Relativity.CKS.OriginalMetricEstimate
import OAI.Geometry.Relativity.CKS.SourceCollarMetric
import OAI.Geometry.Relativity.CKS.MetricComparisonAssembly
import OAI.Geometry.Relativity.CKS.SurfaceNormalization
import OAI.Geometry.Relativity.CKS.BondiCharge

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

lemma boost_to_rest {e : ℝ} {p : E} (he : ‖p‖ < e) :
    boostCLM e (mass e p) (-p) (e,p) = (mass e p,0) := by
  have h := boost_neg_inverse (mass_pos he).ne'
    (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he) (mass e p,0)
  rw [boost_mass (mass_pos he).ne'] at h
  exact h

lemma charge_energy {M : Sphere → ℝ} (hM : SmoothSphere M) :
    (bondiCharge M).1 = (16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure := by
  have h := rawCharge_test hM (ContinuousLinearMap.fst ℝ ℝ E)
  change (rawCharge M).1 = ∫ n, M n * 1 ∂surfaceMeasure at h
  simp only [mul_one] at h
  change (16*Real.pi)⁻¹ * (rawCharge M).1 = _
  rw [h]

lemma charge_momentum {M : Sphere → ℝ} (hM : SmoothSphere M) (i : Fin 3) :
    (bondiCharge M).2 i = (16*Real.pi)⁻¹ * ∫ n, M n * (n:E) i ∂surfaceMeasure := by
  have h := rawCharge_test hM
    ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))
  change (rawCharge M).2 i = ∫ n, M n * (n:E) i ∂surfaceMeasure at h
  change (16*Real.pi)⁻¹ * (rawCharge M).2 i = _
  rw [h]

def heatDatum (M : Sphere → ℝ) (hM : SmoothSphere M) : C(Sphere,ℝ) :=
  ⟨fun n => M n/4, hM.continuous.div_const 4⟩

lemma heatDatum_smooth {M : Sphere → ℝ} (hM : SmoothSphere M) :
    SmoothSphere (heatDatum M hM) := hM.div_const 4

lemma heatDatum_balanced {M : Sphere → ℝ} (hM : SmoothSphere M) {m : ℝ}
    (hc : bondiCharge M = (m,0)) : Balanced (heatDatum M hM) m := by
  have hp : 16*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he := charge_energy hM
  rw [hc] at he
  have hm : ∫ n, M n ∂surfaceMeasure = (16*Real.pi)*m := by
    change m = (16*Real.pi)⁻¹ * _ at he
    calc
      _ = (16*Real.pi)*((16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure) := by field_simp
      _ = _ := by rw [← he]
  constructor
  · rw [CKSSphericalHarmonics.sphereIntegral_apply, CKSSphericalHarmonics.sphereArea_eq_four_pi]
    change (∫ n, M n/4 ∂surfaceMeasure) = m*(4*Real.pi)
    simp only [div_eq_mul_inv, integral_mul_const, hm]
    ring
  · intro i
    have hq := charge_momentum hM i
    rw [hc] at hq
    have hi : ∫ n, M n * (n:E) i ∂surfaceMeasure = 0 := by
      have hz : (16*Real.pi)⁻¹ * (∫ n, M n * (n:E) i ∂surfaceMeasure) = 0 := hq.symm
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hp)
    rw [CKSSphericalHarmonics.sphereIntegral_apply]
    change (∫ n, (M n/4)*(n:E) i ∂surfaceMeasure) = 0
    have heq : (fun n : Sphere => (M n/4)*(n:E) i) = fun n => (M n*(n:E) i)/4 := by
      funext n; ring
    rw [heq]
    simp only [div_eq_mul_inv, integral_mul_const, hi, zero_mul]

theorem balanced_charge_and_heat {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let M' := aspectPullback e p ht M
    ∃ hM' : SmoothSphere M',
      bondiCharge M' = (mass e p,0) ∧
      SmoothSphere (heatDatum M' hM') ∧
      Balanced (heatDatum M' hM') (mass e p) := by
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let M' := aspectPullback e p ht M
  have hM' : SmoothSphere M' := aspectPullback_smooth e p ht hM
  refine ⟨hM', ?_, heatDatum_smooth hM', ?_⟩
  · rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht
  · apply heatDatum_balanced hM'
    rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def polarInverse (P : SmoothAngularPatch) (x : E) : Point :=
  slice ‖x‖ (P.extension (normalizeAmbient x))
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma normalizeAmbient_polarParam (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    normalizeAmbient (polarParam P y) = P.param (angularProjection y) := by
  rw [normalizeAmbient,polarParam_norm P hr.le,polarParam,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
lemma slice_projection (y : Point) : slice (y 0) (angularProjection y) = y := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact slice_zero _ _
  · exact slice_succ _ _ a
lemma polarInverse_param (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    polarInverse P (polarParam P y)=y := by
  simp only [polarInverse,polarParam_norm P hr.le,normalizeAmbient_polarParam P hr,
    P.extension_param hy,slice_projection]
lemma polarInverse_smoothAt_param (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    ContDiffAt ℝ ∞ (polarInverse P) (polarParam P y) := by
  have hn : polarParam P y ≠ 0 := norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne')
  have he : ContDiffAt ℝ ∞ P.extension (normalizeAmbient (polarParam P y)) := by
    rw [normalizeAmbient_polarParam P hr]
    exact P.extension_contDiffAt_param hy
  have hθ := he.comp (polarParam P y) (normalizeAmbient_smooth hn)
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [polarInverse,slice_zero] using contDiffAt_norm ℝ hn (n := ∞)
  · simpa only [polarInverse,slice_succ,Function.comp_apply] using contDiffAt_pi.mp hθ a
lemma polarInverse_fderiv_left (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fderiv ℝ (polarInverse P) (polarParam P y)).comp (fderiv ℝ (polarParam P) y) =
      ContinuousLinearMap.id ℝ Point := by
  have hh : (polarInverse P ∘ polarParam P) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr,
      angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy)] with z hz hzt
    exact polarInverse_param P hz hzt
  have hg := hh.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp y ((polarInverse_smoothAt_param P hr hy).differentiableAt (by simp))
    ((polarParam_contDiffAt P hy).differentiableAt (by simp)),fderiv_id] at hg
  exact hg
lemma polarParam_fderiv_injective (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    Function.Injective (fderiv ℝ (polarParam P) y) := by
  intro v w hvw
  have hleft z := congrArg (fun L : Point →L[ℝ] Point => L z) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hleft
  rw [← hleft v,← hleft w,hvw]
lemma polarParam_fderiv_surjective (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    Function.Surjective (fderiv ℝ (polarParam P) y) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [CKSMixedGeometry.Point,E])).mp (polarParam_fderiv_injective P hr hy)
theorem polar_inverse_differentials (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    polarInverse P (polarParam P y) = y ∧
    ContDiffAt ℝ ∞ (polarInverse P) (polarParam P y) ∧
    (fderiv ℝ (polarInverse P) (polarParam P y)).comp (fderiv ℝ (polarParam P) y) =
      ContinuousLinearMap.id ℝ Point ∧
    (fderiv ℝ (polarParam P) y).comp (fderiv ℝ (polarInverse P) (polarParam P y)) =
      ContinuousLinearMap.id ℝ E := by
  refine ⟨polarInverse_param P hr hy,polarInverse_smoothAt_param P hr hy,
    polarInverse_fderiv_left P hr hy,?_⟩
  ext z
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy z
  have hh := congrArg (fun L : Point →L[ℝ] Point => L v) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hh ⊢
  rw [hh]
end
end CKSLorentz

end

noncomputable section
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology
open scoped Bundle Manifold ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] real_continuousAdd

structure CompatibleLocalMetrics (ι : Type*) where
  domain : ι → Set M
  isOpen : ∀ i, IsOpen (domain i)
  covers : ∀ x, ∃ i, x ∈ domain i
  inner : ι → InnerField I (M := M)
  compatible : ∀ i j x, x ∈ domain i → x ∈ domain j → inner i x = inner j x
  smooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (innerSection I (inner i)) (domain i)
  symm : ∀ i x, x ∈ domain i → ∀ v w, inner i x v w = inner i x w v
  pos : ∀ i x, x ∈ domain i → ∀ v, v ≠ 0 → 0 < inner i x v v
  bounded : ∀ i x, x ∈ domain i → IsVonNBounded ℝ {v | inner i x v v < 1}
variable {I}
def CompatibleLocalMetrics.gluedInner {ι : Type*} (q : CompatibleLocalMetrics I (M := M) ι) :
    InnerField I (M := M) := fun x => q.inner (Classical.choose (q.covers x)) x
end
end CKSMetricGluing

end

noncomputable section
namespace CKSMetricGluing
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma CompatibleLocalMetrics.gluedInner_eq {ι : Type*}
    (q : CompatibleLocalMetrics I (M := M) ι) {i : ι} {x : M} (hx : x ∈ q.domain i) :
    q.gluedInner x = q.inner i x :=
  q.compatible _ _ _ (Classical.choose_spec (q.covers x)) hx
lemma CompatibleLocalMetrics.gluedInner_smooth {ι : Type*}
    (q : CompatibleLocalMetrics I (M := M) ι) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞ (innerSection I q.gluedInner) := by
  intro x
  obtain ⟨i,hi⟩ := q.covers x
  apply ((q.smooth i).contMDiffAt ((q.isOpen i).mem_nhds hi)).congr_of_eventuallyEq
  filter_upwards [(q.isOpen i).mem_nhds hi] with y hy
  change innerSection I q.gluedInner y = innerSection I (q.inner i) y
  simp only [innerSection,q.gluedInner_eq hy]

theorem CompatibleLocalMetrics.exists_smoothMetric {ι : Type*}
    (q : CompatibleLocalMetrics I (M := M) ι) :
    ∃ G : SmoothMetric I (M := M), ∀ i x, x ∈ q.domain i → G.inner x = q.inner i x := by
  let G : SmoothMetric I (M := M) := {
    inner := q.gluedInner
    symm := fun x => q.symm _ x (Classical.choose_spec (q.covers x))
    pos := fun x => q.pos _ x (Classical.choose_spec (q.covers x))
    isVonNBounded := fun x => q.bounded _ x (Classical.choose_spec (q.covers x))
    contMDiff := q.gluedInner_smooth }
  exact ⟨G,fun i x hx => q.gluedInner_eq hx⟩
end
end CKSMetricGluing

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators
abbrev V := Fin 3 → ℝ
abbrev Mat := Fin 3 → Fin 3 → ℝ
abbrev Bil := V →L[ℝ] V →L[ℝ] ℝ

def matrixBilinear (G : Mat) : Bil :=
  ∑ i : Fin 3, ∑ j : Fin 3, G i j •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ V H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
abbrev TangentTriv := Trivialization V (π V (fun x : M => TangentSpace I x))
local instance scalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) :=
  ⟨by rfl⟩
def bilinearTriv (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    Trivialization Bil (π Bil (fun x : M =>
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  e.continuousLinearMap (RingHom.id ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ))
def liftedInner (e : TangentTriv I (M := M)) [MemTrivializationAtlas e]
    (G : M → Mat) : CKSMetricGluing.InnerField I (M := M) :=
  fun x => (bilinearTriv I e).symm x (matrixBilinear (G x))
end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology
lemma matrixBilinear_apply (G : Mat) (v w : V) :
    matrixBilinear G v w = ∑ i : Fin 3, ∑ j : Fin 3, G i j * v i * w j := by
  simp [matrixBilinear, mul_assoc]
lemma matrixBilinear_symm {G : Mat} (hG : Matrix.IsHermitian G) (v w : V) :
    matrixBilinear G v w = matrixBilinear G w v := by
  have hs : ∀ i j, G i j = G j i := by
    intro i j
    have h := congrFun (congrFun hG.eq j) i
    change star (G i j) = G j i at h
    simpa only [star_trivial] using h
  simp only [matrixBilinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring
lemma matrixBilinear_pos {G : Mat} (hG : Matrix.PosDef G) {v : V} (hv : v ≠ 0) :
    0 < matrixBilinear G v v := by
  have h := hG.dotProduct_mulVec_pos hv
  simpa [matrixBilinear_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas
instance bilinearTriv_atlas (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    MemTrivializationAtlas (bilinearTriv I e) := by unfold bilinearTriv; infer_instance
@[simp] lemma bilinearTriv_baseSet (e : TangentTriv I (M := M)) [MemTrivializationAtlas e] :
    (bilinearTriv I e).baseSet = e.baseSet := by simp [bilinearTriv]
lemma bilinearTriv_pair (e : TangentTriv I (M := M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : V) :
    ((bilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
  unfold bilinearTriv
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ))
    (show x ∈ (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ)).baseSet by simpa using hx)]
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (Trivial.trivialization M ℝ) (show x ∈ (Trivial.trivialization M ℝ).baseSet from mem_univ x)]
  rfl
lemma liftedInner_pair (e : TangentTriv I (M := M)) [MemTrivializationAtlas e]
    (G : M → Mat) {x : M} (hx : x ∈ e.baseSet) (v w : TangentSpace I x) :
    liftedInner I e G x v w = matrixBilinear (G x)
      (e.continuousLinearMapAt ℝ x v) (e.continuousLinearMapAt ℝ x w) := by
  have h := congrArg Prod.snd ((bilinearTriv I e).apply_mk_symm
    (show x ∈ (bilinearTriv I e).baseSet by simpa) (matrixBilinear (G x)))
  have h' := congrArg (fun B : Bil => B (e.continuousLinearMapAt ℝ x v)
    (e.continuousLinearMapAt ℝ x w)) h
  rw [bilinearTriv_pair e hx] at h'
  simpa only [liftedInner, Trivialization.symmL_continuousLinearMapAt e hx] using h'
end
end CKSTangentCoefficients

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients

def polarLift (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ) : SpatialTensor :=
  fun x => (matrixBilinear (F (polarInverse P x))).bilinearComp
    (fderiv ℝ (polarInverse P) x) (fderiv ℝ (polarInverse P) x)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators
lemma bilinear_eq_of_coordinate_basis (B C : Point →L[ℝ] Point →L[ℝ] ℝ)
    (h : ∀ i j, B (basis i) (basis j) = C (basis i) (basis j)) : B = C := by
  ext v w
  rw [← sum_coordinate_basis v,← sum_coordinate_basis w]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,h]
lemma polarLift_components (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i j : I) :
    polarTensorComponents P (polarLift P F) i j y = F y i j := by
  have hi := congrArg (fun L : Point →L[ℝ] Point => L (basis i)) (polarInverse_fderiv_left P hr hy)
  have hj := congrArg (fun L : Point →L[ℝ] Point => L (basis j)) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi hj
  change matrixBilinear (F (polarInverse P (polarParam P y)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis i)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis j))) = _
  rw [polarInverse_param P hr hy,hi,hj]
  simp [matrixBilinear,basis,Pi.single_apply]
lemma polarTensor_ext (P : SmoothAngularPatch) {A B : SpatialTensor}
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : ∀ i j, polarTensorComponents P A i j y = polarTensorComponents P B i j y) :
    A (polarParam P y) = B (polarParam P y) := by
  have hh : (A (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) =
      (B (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) :=
    bilinear_eq_of_coordinate_basis _ _ h
  ext v w
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy v
  obtain ⟨w,rfl⟩ := polarParam_fderiv_surjective P hr hy w
  exact congrArg (fun L : Point →L[ℝ] Point →L[ℝ] ℝ => L v w) hh

theorem polarLift_reconstruction (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ i j, polarTensorComponents P (polarLift P F) i j y = F y i j) ∧
    (∀ A : SpatialTensor, (∀ i j, polarTensorComponents P A i j y = F y i j) →
      polarLift P F (polarParam P y) = A (polarParam P y)) := by
  refine ⟨polarLift_components P F hr hy,?_⟩
  intro A hA
  apply polarTensor_ext P hr hy
  intro i j
  rw [polarLift_components P F hr hy,hA]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

theorem polarLift_overlap (P Q : SmoothAngularPatch)
    (F G : CKSMixedGeometry.Point → Matrix CKSMixedGeometry.I CKSMixedGeometry.I ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0)
    (hy : angularProjection y ∈ angularOverlap P Q)
    (hFG : ∀ a b, F y a b = coordinateTensorPullback (angularChange (angleTransition P Q))
      (fun i j z => G z i j) a b y) :
    polarLift P F (polarParam P y) = polarLift Q G (polarParam P y) := by
  apply polarTensor_ext P hr hy.1
  intro a b
  rw [polarLift_components P F hr hy.1,hFG,
    ← polarTensor_angularTransition P Q (polarLift Q G) hy a b]
  have hθ : angularProjection (angularChange (angleTransition P Q) y) ∈ Q.chart.target := by
    simpa only [angularProjection_angularChange] using angleTransition_target hy
  have hr' : 0 < (angularChange (angleTransition P Q) y) 0 := by simpa using hr
  unfold coordinateTensorPullback
  simp only [polarLift_components Q G hr' hθ]
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
open scoped BigOperators
lemma fderiv_angularChange_entries {φ : Point → Point} {y : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection y)) (i j : Fin 3) :
    fderiv ℝ (angularChange φ) y (CKSMixedGeometry.basis j) i =
      angularBlock (CKSAngularGeometry.angularJacobian φ y) i j := by
  change fderiv ℝ (angularChange φ) y (CKSRealizedRound.basis j) i = _
  refine Fin.cases ?_ (fun a => ?_) j
  · rw [fderiv_angularChange_radial hφ]
    fin_cases i <;> simp [CKSRealizedRound.basis,angularBlock]
  · rw [fderiv_angularChange_basis hφ]
    fin_cases i <;> fin_cases a <;>
      simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply,angularBlock]
lemma coordinateTensorPullback_angularBlock {φ : Point → Point} {y : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection y))
    (G : PhysicalPoint → Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    coordinateTensorPullback (angularChange φ) (fun i j z => G z i j) a b y =
      ((angularBlock (CKSAngularGeometry.angularJacobian φ y)).transpose *
        G (angularChange φ y) * angularBlock (CKSAngularGeometry.angularJacobian φ y)) a b := by
  have hd (i j : Fin 3) : D (CKSMixedGeometry.basis j) (fun z => angularChange φ z i) y =
      angularBlock (CKSAngularGeometry.angularJacobian φ y) i j := by
    simp only [D,fderiv_apply (angularChange_differentiableAt hφ),ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply,fderiv_angularChange_entries hφ]
  simp only [coordinateTensorPullback,hd,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

theorem physicalCollar_lift_angular_covariant (P Q : SmoothAngularPatch)
    {R : ℝ} (hR : 0 < R) {f f' : LogCollarData} {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ angularOverlap P Q)
    (hf : f.SmoothAt (radiusLogPoint (angularChange (angleTransition P Q) y)))
    (hf' : f'.SmoothAt (radiusLogPoint y))
    (hrel : ∀ᶠ z in 𝓝 (radiusLogPoint y), f.AngularRelatedAt (angleTransition P Q) f' z)
    (hγ : (physicalCollarGamma R f (angularChange (angleTransition P Q) y)).PosDef)
    (hτ : (physicalCollarRawTau R f (angularChange (angleTransition P Q) y)).IsHermitian) :
    polarLift P (physicalCollarMetric R f') (polarParam P y) =
      polarLift Q (physicalCollarMetric R f) (polarParam P y) ∧
    polarLift P (physicalCollarTensor R f') (polarParam P y) =
      polarLift Q (physicalCollarTensor R f) (polarParam P y) := by
  have hφ := angleTransition_smoothAt hy
  obtain ⟨hg,hk⟩ := physicalCollar_angular_covariant hR hr
    (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hf hf' hrel (actual_angleTransition_isUnit P Q hy) hγ hτ
  constructor
  · apply polarLift_overlap P Q _ _ hr hy
    intro a b
    rw [coordinateTensorPullback_angularBlock (hφ.differentiableAt (by simp)),hg]
  · apply polarLift_overlap P Q _ _ hr hy
    intro a b
    rw [coordinateTensorPullback_angularBlock (hφ.differentiableAt (by simp)),hk]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped ContDiff Matrix.Norms.Elementwise
local instance bilNorm : NormedAddCommGroup CKSTangentCoefficients.Bil :=
  ContinuousLinearMap.toNormedAddCommGroup (E := CKSTangentCoefficients.V) (F := CKSTangentCoefficients.V →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance bilSpace : NormedSpace ℝ CKSTangentCoefficients.Bil := ContinuousLinearMap.toNormedSpace
local instance epNorm : NormedAddCommGroup (E →L[ℝ] Point →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := Point →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance epSpace : NormedSpace ℝ (E →L[ℝ] Point →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance peNorm : NormedAddCommGroup (Point →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := Point) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance peSpace : NormedSpace ℝ (Point →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance eeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance eeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma matrixBilinear_contDiff : ContDiff ℝ ∞ matrixBilinear := by
  unfold matrixBilinear
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((ContinuousLinearMap.proj j : CKSTangentCoefficients.V →L[ℝ] ℝ).contDiff.comp
    (ContinuousLinearMap.proj i : CKSTangentCoefficients.Mat →L[ℝ] CKSTangentCoefficients.V).contDiff).smul contDiff_const
lemma polarLift_smoothAt (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) : ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) := by
  have hi := polarInverse_smoothAt_param P hr hy
  have hFi : ContDiffAt ℝ ∞ F (polarInverse P (polarParam P y)) := by
    rw [polarInverse_param P hr hy]; exact hF
  have hB := matrixBilinear_contDiff.contDiffAt.comp (polarParam P y) (hFi.comp (polarParam P y) hi)
  have hD := hi.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hf1 : ContDiff ℝ ∞ (fun B : E →L[ℝ] Point →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] Point →L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E Point ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hf2 : ContDiff ℝ ∞ (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf2.contDiffAt.comp _ ((hf1.contDiffAt.comp _ (hB.clm_comp hD)).clm_comp hD)
lemma polarLift_smooth_positive (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) (hp : Matrix.PosDef (F y)) :
    ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) ∧
    (∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v) ∧
    ∀ v : E, v ≠ 0 → 0 < polarLift P F (polarParam P y) v v := by
  refine ⟨polarLift_smoothAt P F hr hy hF,?_,?_⟩
  · intro v w
    unfold polarLift
    rw [polarInverse_param P hr hy]
    exact matrixBilinear_symm hp.isHermitian _ _
  · intro v hv
    unfold polarLift
    rw [polarInverse_param P hr hy]
    apply matrixBilinear_pos hp
    intro hz
    change fderiv ℝ (polarInverse P) (polarParam P y) v = 0 at hz
    have hh := congrArg (fun L : E →L[ℝ] E => L v) (polar_inverse_differentials P hr hy).2.2.2
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,hz,map_zero] at hh
    exact hv hh.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_cksLeading_smoothAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x)) (hs : determinant (f.logFields.sigma x) ≠ 0) :
    ContDiffAt ℝ ∞ (cksLeadingField f.logFields) x := by
  have hσ := hf.sigma
  have hg := hf.mg
  have hk := hf.mK
  have hr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hg hk hr
  have hi := inverse_smoothAt (angularLift_diff hσ) hs
  exact ((contDiffAt_const.mul (angularLift_diff hr)).add
    (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hg)))).add
      (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hk)))

theorem sourceCollarData_smoothAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : determinant (f.base.logFields.sigma x) ≠ 0) :
    (sourceCollarData f.logFields).SmoothAt x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hc := logRadiusChart_smooth.contDiffAt (x := x)
  have hσ := hf.base.sigma
  rw [angularProjection_logRadiusChart] at hσ
  have hσ' := angularLift_diff hσ
  have hγ := (sourceGamma_smoothAt hf.base hr).comp x hc
  dsimp only [Function.comp_def] at hγ
  rw [sourceGamma_pullback] at hγ
  have hshift := (sourceShift_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hshift
  rw [sourceShift_pullback] at hshift
  have ht := (sourceT_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at ht
  rw [sourceT_pullback] at ht
  have hL := (sourceOriginalL_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hL
  rw [sourceOriginalL_pullback] at hL
  have hη := (sourceOriginalEta_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hη
  rw [sourceOriginalEta_pullback] at hη
  have hτ := (sourceOriginalTau_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hτ
  rw [sourceOriginalTau_pullback] at hτ
  have heq : logPhysicalMass f.base.logFields =ᶠ[𝓝 x] (fun y => sourcePhysicalMass f.base (logRadiusChart y)) := by
    filter_upwards [hc.continuousAt.tendsto.eventually hf.base.regularAt.eventually,
      hc.continuousAt.tendsto.eventually hp] with y hy hyp
    exact (sourcePhysicalMass_pullback hy hyp).symm
  have hmass := ((sourcePhysicalMass_smoothAt hf.base hr hp.self_of_nhds).comp x hc).congr_of_eventuallyEq heq
  have hlead := source_cksLeading_smoothAt hf.base hs
  have hexp : ContDiffAt ℝ ∞ (fun y : Point => Real.exp (y 0)) x := by fun_prop
  have he : ContDiffAt ℝ ∞ (logQError f.base.logFields) x := by
    have he' : logQError f.base.logFields=fun y =>
        (1/Real.exp (y 0)^2) • logGamma f.base.logFields y-f.base.logFields.sigma y :=
      funext (logQError_scaled f.base.logFields)
    rw [he']
    exact ((contDiffAt_const.div (hexp.pow 2) (by positivity)).smul hγ).sub hσ'
  refine ⟨hσ',he,hshift,ht.sub contDiffAt_const,hL.sub contDiffAt_const,
    hmass.sub hlead,hlead,?_,?_⟩
  · exact contDiffAt_pi.mpr fun a => (contDiffAt_pi.mp hη a).div hexp (Real.exp_ne_zero _)
  · exact contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hτ a) b).div (hexp.pow 2) (by positivity)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceAspect_smoothAt {f : SourceMassFields} {x : Angle}
    (hσ : ContDiffAt ℝ ∞ f.sigma x) (hg : ContDiffAt ℝ ∞ f.mg x)
    (hk : ContDiffAt ℝ ∞ f.mK x) (hr : ContDiffAt ℝ ∞ f.mr x)
    (hs : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ ∞ (sourceAspect f) x := by
  have hi : ContDiffAt ℝ ∞ (fun y : Angle => inverse (f.sigma y)) x := inverse_smoothAt hσ hs
  have hm : ContDiffAt ℝ ∞ (fun y : Angle => f.mg y+(2:ℝ) • f.mK y) x :=
    hg.add ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Angle => (2:ℝ)) x).smul hk)
  have ht := traceProduct_smoothAt hi hm
  exact ht.add (contDiffAt_const.mul hr)

lemma sourceCollar_sigma_radial {f : SourceTensorFields} {x : Point}
    (hf : f.base.RegularAt (logRadiusChart x)) :
    ∀ i j, D (CKSRealizedRound.basis 0)
      (fun z => (sourceCollarData f.logFields).sigma z i j) x=0 := by
  have hs := hf.sigma
  rw [angularProjection_logRadiusChart] at hs
  intro i j
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hs i) j).differentiableAt (by norm_num))

lemma sourceCollar_sigma_radial_eventually {f : SourceTensorFields} {x : Point}
    (hf : f.base.RegularAt (logRadiusChart x)) :
    ∀ᶠ y in 𝓝 x, ∀ i j, D (CKSRealizedRound.basis 0)
      (fun z => (sourceCollarData f.logFields).sigma z i j) y=0 := by
  filter_upwards [(logRadiusChart_smooth.continuous.continuousAt (x:=x)).tendsto.eventually hf.eventually]
    with y hy
  exact sourceCollar_sigma_radial hy

lemma sourceCollar_fstar_radial {f : SourceTensorFields} {x : Point}
    (hf : f.base.SmoothAt (logRadiusChart x))
    (hs : determinant (f.base.logFields.sigma x) ≠ 0) :
    D (CKSRealizedRound.basis 0) (sourceCollarData f.logFields).fstar x=0 := by
  change D (basis 0) (cksLeadingField f.base.logFields) x=0
  rw [source_leading_mass]
  have hσ := hf.sigma
  have hg := hf.mg
  have hk := hf.mK
  have hr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hg hk hr
  exact D_angularLift (((sourceAspect_smoothAt hσ hg hk hr hs).div_const 4).differentiableAt (by simp))

lemma sourceCollar_sigma_hermitian {f : SourceTensorFields} {x : Point}
    (hs : (f.base.sigma (angularProjection x)).IsHermitian) :
    ((sourceCollarData f.logFields).sigma x).IsHermitian := hs

lemma sourceCollar_metricError_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hs : (f.base.sigma (angularProjection x)).IsHermitian) :
    ((sourceCollarData f.logFields).metricError x).IsHermitian := by
  change (logQError f.base.logFields x).IsHermitian
  rw [logQError_scaled]
  have hγ := (metricBlock_leaf_posDef hp).isHermitian
  change (sourceGamma f.base (logRadiusChart x)).IsHermitian at hγ
  rw [congrFun (sourceGamma_pullback f.base) x] at hγ
  exact (hγ.smul (by rfl)).sub hs

lemma sourceCollar_tau_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hk : (sourceTangentialK f.base (logRadiusChart x)).IsHermitian) :
    ((sourceCollarData f.logFields).tauDivR2 x).IsHermitian := by
  have he : (sourceCollarData f.logFields).tauDivR2 x=
      (1/Real.exp (x 0)^2) • sourceOriginalTau f (logRadiusChart x) := by
    rw [congrFun (sourceOriginalTau_pullback f) x]
    ext i j
    change logOriginalTau f.logFields x i j / Real.exp (x 0)^2 =
      (1/Real.exp (x 0)^2) * logOriginalTau f.logFields x i j
    ring
  rw [he]
  exact (hk.sub ((metricBlock_leaf_posDef hp).isHermitian.smul (by rfl))).smul (by rfl)

lemma sourceCollar_symmetries {f : SourceTensorFields} {x : Point}
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceTangentialK f.base y).IsHermitian) :
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).sigma y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).metricError y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).tauDivR2 y).IsHermitian) := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x:=x)
  have hp' := hc.tendsto.eventually hp
  have hk' := hc.tendsto.eventually hk
  refine ⟨hs,?_,?_⟩
  · filter_upwards [hp',hs] with y hyp hys
    exact sourceCollar_metricError_hermitian hyp hys
  · filter_upwards [hp',hk'] with y hyp hyk
    exact sourceCollar_tau_hermitian hyp hyk

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def rawFutureDomain : Set RawNullInput :=
  rawPositiveDomain ∩ {p | 0 < (lapseD (rawLapseInput p.1)).1}

lemma rawFutureDomain_open : IsOpen rawFutureDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hd : ContinuousAt (fun q : RawNullInput => (lapseD (rawLapseInput q.1)).1) p :=
    (continuous_fst.comp lapseD_smooth.continuous).continuousAt.comp
      ((rawLapseInput_smooth hp.1.1.1).continuousAt.comp continuousAt_fst)
  filter_upwards [rawPositiveDomain_open.mem_nhds hp.1,
    hd.eventually (Ioi_mem_nhds hp.2)] with q hq hqd
  exact ⟨hq,hqd⟩

lemma rawFutureFamily_regular {K : Set MatrixScalarJet}
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B : ℝ) :
    rawReferenceFamily K B ⊆ rawFutureDomain := by
  intro p hp
  refine ⟨rawPositiveFamily_regular hreg B hp,?_⟩
  change 0 < 1+rz p.1^3*(rawD p.1).1
  rw [hp.1.2]
  norm_num

lemma field_future_regular (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point}
    (hf : f.RegularAt x) (hp : thinRaw (fieldRaw b f x) ∈ rawFutureDomain) :
    positiveAngular (fieldQ b f x) ∧
      0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
      0 < lapseDField (b 0) (fieldD b f) x := by
  have hprim := (thinRaw_primitive_regular (fieldRaw b f x)).mp ⟨hp.1.1.1,hp.1.1.2.1⟩
  have hq : determinant (fieldQ b f x) ≠ 0 := by
    rw [field_angular_matrix b hf]
    exact hprim.1
  have hd := congrArg Prod.fst (actual_lapseDField (b 0) (fieldD_diff b hf hq)
    (rawT (fieldRaw b f x).1) (rawF (fieldRaw b f x).1))
  rw [field_rawD b hf hq] at hd
  change lapseDField (b 0) (fieldD b f) x=(lapseD (rawLapseInput (fieldRaw b f x).1)).1 at hd
  refine ⟨?_,(field_primitive_regular b hf hprim).2.1,?_⟩
  · rw [field_angular_matrix b hf]
    exact hp.1.2
  · rw [hd]
    exact hp.2

theorem bounded_thin_future_field_regions {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r →
      (positiveAngular (fieldQ b f x) ∧
        0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x ∧
        0 < lapseDField (b 0) (fieldD b f) x) ∧
      (positiveAngular (fieldQ (oldParams b) f x) ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x ∧
        0 < lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x)
 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : FiniteDimensional ℝ RawNullInput := inferInstance
  let : ProperSpace RawNullInput := FiniteDimensional.proper ℝ RawNullInput
  obtain ⟨δ,hδ,hdom⟩ := (rawReferenceFamily_compact hK B).exists_cthickening_subset_open
    rawFutureDomain_open (rawFutureFamily_regular hreg B)
  refine ⟨max 1 (1/δ),le_max_left _ _,?_⟩
  intro b f x hf hq hb hbound r hr hz
  obtain ⟨_,hd⟩ := inverse_radius_threshold hδ hr
  have hh : |rz (thinRaw (fieldRaw b f x)).1| ≤ δ := by change |b 0| ≤ δ; rw [hz]; exact hd
  obtain ⟨hp,hp₀⟩ := raw_reference_tube (p:=thinRaw (fieldRaw b f x)) hq
    (fieldRaw_thin_norm hB hb hbound) hh
  have h1 := hdom hp
  have h0 : thinRaw (fieldRaw (oldParams b) f x) ∈ rawFutureDomain := by
    rw [fieldRaw_old,thinRaw_old]
    exact hdom hp₀
  exact ⟨field_future_regular b hf h1,
    field_future_regular (oldParams b) hf h0⟩

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem cks_collar_future_regions {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ Real.exp ρ → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      ∀ b : Fin 5 → ℝ, ‖b‖ ≤ P → b 0=1/Real.exp ρ →
      (positiveAngular (fieldQ b ((sourceCollarData f).angular ρ) x) ∧
        0 < lapseRadField (b 0) (fieldT b ((sourceCollarData f).angular ρ))
          (fieldF b ((sourceCollarData f).angular ρ)) x ∧
        0 < lapseDField (b 0) (fieldD b ((sourceCollarData f).angular ρ)) x) ∧
      (positiveAngular (fieldQ (oldParams b) ((sourceCollarData f).angular ρ) x) ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) ((sourceCollarData f).angular ρ))
          (fieldF (oldParams b) ((sourceCollarData f).angular ρ)) x ∧
        0 < lapseDField ((oldParams b) 0) (fieldD (oldParams b) ((sourceCollarData f).angular ρ)) x) := by
  have hd (q) (hq : q ∈ K) : determinant (fun i k => (q i k).1.1) ≠ 0 := by
    exact (determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos.ne'
  obtain ⟨R,hR,C,hC,hcoeff⟩ := cks_sourceCollarData_bounded hK hd hB
  let L := restrictMatrixThree '' K
  have hL : IsCompact L := hK.image restrictMatrixThree_continuous
  have hpos : ∀ q ∈ L, positiveAngular (fun i k => (q i k).1) := by
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨(hreg q hq).diag_pos,?_⟩
    change 0 < determinant (fun i k => (q i k).1.1)
    exact (determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos
  let T := max P (2*C)
  have hT : 0 ≤ T := hP.trans (le_max_left _ _)
  obtain ⟨S,hS,hfuture⟩ := bounded_thin_future_field_regions hL hpos hT
  refine ⟨max R S,hR.trans (le_max_left _ _),?_⟩
  intro f ρ x hr hf hmk hek hp hs hb b hbp hz
  have hrR : R ≤ Real.exp ρ := (le_max_left _ _).trans hr
  have hrS : S ≤ Real.exp ρ := (le_max_right _ _).trans hr
  have hsd : determinant (f.base.sigma (slice ρ x)) ≠ 0 := hd _ hs
  have hsource := sourceCollarData_regular hf hp hsd
  have hfield := angular_regular hsource (logTError_three_diff hf.base hmk hek hp.self_of_nhds)
  have hbound := hcoeff f (slice ρ x) (by simpa only [slice_zero] using hrR) hf hp hs hb
  have hthin := angular_thin_bounded hC (hR.trans hrR) hsource hbound
  have hmem : CKSAngularGeometry.matrixScalarJets (((sourceCollarData f).angular ρ).metric 0) x ∈ L := by
    change CKSAngularGeometry.matrixScalarJets (fun y => f.base.sigma (slice ρ y)) x ∈ L
    rw [sigma_slice_jets hf.base.sigma]
    exact ⟨_,hs,rfl⟩
  exact hfuture b _ x hfield hmem (hbp.trans (le_max_left _ _))
    (hthin.mono (le_max_right _ _)) (Real.exp ρ) hrS hz

theorem source_actual_collar_future_regions {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      let b := collarParams R (Real.exp ρ)
      let c := (sourceCollarData f.logFields).angular ρ
      (positiveAngular (fieldQ b c x) ∧
        0 < lapseRadField (b 0) (fieldT b c) (fieldF b c) x ∧
        0 < lapseDField (b 0) (fieldD b c) x) ∧
      (positiveAngular (fieldQ (oldParams b) c x) ∧
        0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) c) (fieldF (oldParams b) c) x ∧
        0 < lapseDField ((oldParams b) 0) (fieldD (oldParams b) c) x) := by
  obtain ⟨A,hA,hparams⟩ := collarParams_weighted
  obtain ⟨R₀,hR₀,hh⟩ := cks_collar_future_regions hK hreg hB (zero_le_one.trans hA)
  refine ⟨R₀,hR₀,?_⟩
  intro R f ρ x hR hr htop hf hp hσ hs hmg hmk hmr hb
  have hmk' := hf.base.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  rw [angularProjection_logRadiusChart] at hmk'
  have hcl := (logRadiusChart_smooth.contDiffAt (x:=slice ρ x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hek := (hf.base.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).comp _ hcl
  have hf' := hf.regularAt
  exact hh f.logFields ρ x (hR.trans hr) (source_tensor_log_regular hf') (angularLift_diff hmk')
    hek (source_tensor_log_positive hp) hσ (source_tensor_log_bounds hB hf' hs hmg hmk hmr hb)
    _ (hparams R (Real.exp ρ) (hR₀.trans hR) hr htop).2 rfl

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarQ_hermitian {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hσ : (f.sigma (slice ρ a)).IsHermitian)
    (he : (f.metricError (slice ρ a)).IsHermitian) :
    (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).IsHermitian := by
  have hs' : (f.sigma (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using hσ
  have he' : (f.metricError (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using he
  have h := (physicalCollarGamma_isHermitian R f (slice (Real.exp ρ) a) hs' he').smul
    (show star (1/Real.exp ρ^2)=1/Real.exp ρ^2 by rfl)
  rw [physicalCollarGamma_slice,smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] at h
  exact h

lemma physical_collar_pivots {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), (f.sigma y).IsHermitian)
    (he : ∀ᶠ y in 𝓝 (slice ρ a), (f.metricError y).IsHermitian)
    (hσD : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hq : positiveAngular (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
      (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a) :
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) ∧
      0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) ∧
      0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) := by
  have hpq := positiveAngular_posDef (physicalCollarQ_hermitian hσ.self_of_nhds he.self_of_nhds) hq
  have hp := (physicalCollarGamma_pos_iff R ρ f a).mpr hpq
  refine ⟨?_,?_,(physicalCollarRadical_pos_iff R ρ f a).mpr hu⟩
  · apply physicalCollarGamma_eventually_posDef (by simp) (by simpa using hf)
      (by simpa using hσ) (by simpa using he) hp
  · rw [physicalCollarExpansion_slice R ρ hf.regularAt hσD hp]
    exact hd

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

@[simp] lemma logRadiusChart_slice (ρ : ℝ) (x : AP) :
    logRadiusChart (slice ρ x)=slice (Real.exp ρ) x := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart]

lemma physical_source_collar_old_DEC {R ρ : ℝ} {f : SourceTensorFields} {x : AP}
    (hf : f.SmoothAt (logRadiusChart (slice ρ x)))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef)
    (hσ : ∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian)
    (hs : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0)
    (hq : positiveAngular (fieldQ (oldParams (collarParams R (Real.exp ρ)))
      ((sourceCollarData f.logFields).angular ρ) x))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ))
      (fieldF (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x)
    (hDEC : physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base)
      (logRadiusChart (slice ρ x))) :
    coordinateDEC (fieldNullInput (oldParams (collarParams R (Real.exp ρ)))
      ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) := by
  let S := 2*Real.exp ρ
  have hS : 0 < S := by dsimp [S]; positivity
  have hi : Real.exp ρ < S := by dsimp [S]; linarith [Real.exp_pos ρ]
  have heq : collarParams S (Real.exp ρ)=oldParams (collarParams R (Real.exp ρ)) :=
    collarParams_initial hS hi.le
  have hc := sourceCollarData_smoothAt hf hp hs
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  have hstar := sourceCollar_fstar_radial hf.base hs
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots (R:=S) hc hσh heh hσD.self_of_nhds
    (by rw [heq]; exact hq) (by rw [heq]; exact hu) (by rw [heq]; exact hd)
  have hr : 0 < (slice (Real.exp ρ) x) 0 := by simpa using Real.exp_pos ρ
  have hi' : (slice (Real.exp ρ) x) 0 < S := by simpa using hi
  have hf' : f.SmoothAt (slice (Real.exp ρ) x) := by simpa using hf
  have hp' : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) x), (sourceMetric f.base y).PosDef := by simpa using hp
  have hfields := source_inner_collar_fields_eventually hr hi' hf'.base.regularAt hp'
  have hexp := radialExpansion_congr (hfields.mono (fun _ h => h.1)) (hfields.mono (fun _ h => h.2.1))
  rw [source_radialExpansion_eq] at hexp
  have hdSource : 0 < sourceExpansion f.base (slice (Real.exp ρ) x) := by
    rw [← hexp]; exact hd'
  have hdS := ((sourceExpansion_smoothAt hf'.base hr.ne' hp'.self_of_nhds).continuousAt).eventually
    (Ioi_mem_nhds hdSource)
  have hphysical := (physical_source_inner_collar_DEC_iff hr hi' hf'.base.regularAt hp' hdS
    (by simpa using hk)).mpr (by simpa using hDEC)
  have hh := (physical_collar_DEC_iff hS hc hσD hstar hτh hγ hd' hu').mp hphysical
  rwa [heq] at hh

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_actual_collar_physical_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      physicalDEC (sourceMetric f.base) (sourceTensor f) (sourceFrame f.base)
        (logRadiusChart (slice ρ x)) →
      physicalDEC (physicalCollarMetric R (sourceCollarData f.logFields))
        (physicalCollarTensor R (sourceCollarData f.logFields))
        (physicalCollarFrame R (sourceCollarData f.logFields)) (slice (Real.exp ρ) x)
 := by
  obtain ⟨A,hA,hcoord⟩ := source_actual_collar_coordinate_DEC hK hreg hB
  obtain ⟨C,hC,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨max A C,hA.trans (le_max_left _ _),?_⟩
  intro R f ρ x hR hr htop hf hp hσ hk hmem hs hmg hmk hmr hb hDEC
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hRC : C ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hA.trans hRA)
  obtain ⟨⟨hq,hu,hd⟩,⟨hoq,hou,hod⟩⟩ := hfuture R f ρ x hRC hr htop hf hp hmem hs hmg hmk hmr hb
  have hdet : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hold := physical_source_collar_old_DEC hf hp hσ hk hdet hoq hou hod hDEC
  have hmk' := hf.base.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hek := hf.base.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hnew := hcoord R f ρ x hRA hr htop hf.regularAt hmk' hek hp hmem hs hmg hmk hmr hb hold
  have hc := sourceCollarData_smoothAt hf hp hdet
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  have hstar := sourceCollar_fstar_radial hf.base hdet
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots hc hσh heh hσD.self_of_nhds hq hu hd
  exact (physical_collar_DEC_iff hRpos hc hσD hstar hτh hγ hd' hu').mpr hnew

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise

structure PhysicalRegularAt (g k : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ g x
  tensor_smooth : ContDiffAt ℝ ∞ k x
  metric_positive : (g x).PosDef
  tensor_symmetric : (k x).IsHermitian
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationTensor_contDiffAt {U L : PhysicalPoint → ℝ}
    {η s : PhysicalPoint → Point} {kT : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hL : ContDiffAt ℝ ∞ L x)
    (hη : ContDiffAt ℝ ∞ η x) (hk : ContDiffAt ℝ ∞ kT x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => foliationTensor (U y) (L y) (η y) (kT y) (s y)) x := by
  have hkc (i j) : ContDiffAt ℝ ∞ (fun y => kT y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hηc (i) : ContDiffAt ℝ ∞ (fun y => η y i) x := contDiffAt_pi.mp hη i
  have hrr : ContDiffAt ℝ ∞
      (fun y => L y/(U y)^2+2/U y*(∑ a, η y a*s y a)+∑ a, ∑ b, kT y a b*s y a*s y b) x :=
    ((hL.div (hU.pow 2) (pow_ne_zero _ h0)).add
      ((contDiffAt_const.div hU h0).mul (ContDiffAt.sum (fun a _ => (hηc a).mul (hsc a))))).add
      (ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ((hkc a b).mul (hsc a)).mul (hsc b))))
  have hm (a) : ContDiffAt ℝ ∞ (fun y => η y a/U y+∑ b, kT y a b*s y b) x :=
    ((hηc a).div hU h0).add (ContDiffAt.sum (fun b _ => (hkc a b).mul (hsc b)))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hkc 0 0
  · exact hkc 0 1
  · exact hm 1
  · exact hkc 1 0
  · exact hkc 1 1

lemma physical_collar_regularAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hγ : (physicalCollarGamma R f x).PosDef)
    (hτ : (f.tauDivR2 (radiusLogPoint x)).IsHermitian)
    (hd : 0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x)
    (hu : 0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) x) :
    PhysicalRegularAt (physicalCollarMetric R f) (physicalCollarTensor R f) x := by
  have hU : ContDiffAt ℝ ∞ (physicalCollarU R f) x :=
    physicalCollarU_smoothAt hR hr.ne' hf hγ hd.ne' hu.ne'
  have hU0 : physicalCollarU R f x ≠ 0 := (radialMassLapse_pos hd hu).ne'
  have hγs := physicalCollarGamma_smoothAt R hr.ne' hf
  have hss := physicalCollarShift_smoothAt R hr.ne' hf
  refine ⟨foliationMetric_contDiffAt hU hγs hss hU0,?_,foliationMetric_posDef hU0 hγ _,?_⟩
  · exact foliationTensor_contDiffAt hU (physicalCollarL_smoothAt R hr.ne' hf)
      (physicalCollarEta_smoothAt R hr.ne' hf) (physicalCollarTangential_smoothAt R hr.ne' hf hγ) hss hU0
  · unfold physicalCollarTensor foliationTensor
    exact metricBlock_hermitian _ _ (physicalCollarTangential_isHermitian R f x hγ.isHermitian hτ)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_actual_collar_regular {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData f.logFields))
        (physicalCollarTensor R (sourceCollarData f.logFields)) (slice (Real.exp ρ) x)
 := by
  obtain ⟨C,hC,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨C,hC,?_⟩
  intro R f ρ x hR hr htop hf hp hσ hk hmem hs hmg hmk hmr hb
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hC.trans hR)
  obtain ⟨⟨hq,hu,hd⟩,_⟩ := hfuture R f ρ x hR hr htop hf hp hmem hs hmg hmk hmr hb
  have hdet : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hc := sourceCollarData_smoothAt hf hp hdet
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots hc hσh heh hσD.self_of_nhds hq hu hd
  apply physical_collar_regularAt hRpos (by simpa using Real.exp_pos ρ)
    (by simpa using hc) hγ.self_of_nhds
    (by simpa using hτh.self_of_nhds) hd' hu'

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

structure CollarSourcePatch (A B : SpatialTensor) where
  patch : SmoothAngularPatch
  region : Set Angle
  region_open : IsOpen region
  region_target : region ⊆ patch.chart.target
  radius : ℝ
  mr : Angle → ℝ
  mg : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ
  mK : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ
  metric_CKS : SourceCKSComponents 3 6 (angularRadialTail radius region)
    (polarTensorComponents patch A) mr mg
  tensor_CKS : SourceCKSComponents 2 5 (angularRadialTail radius region)
    (polarTensorComponents patch B) (fun _ => 0) mK

def CollarSourcePatch.fields {A B : SpatialTensor} (Q : CollarSourcePatch A B) : SourceTensorFields :=
  spatialSourceFields Q.patch A B Q.mr Q.mg Q.mK

def CollarSourcePatch.metric {A B : SpatialTensor} (Q : CollarSourcePatch A B) (R : ℝ) : SpatialTensor :=
  polarLift Q.patch (physicalCollarMetric R (sourceCollarData Q.fields.logFields))
def CollarSourcePatch.tensor {A B : SpatialTensor} (Q : CollarSourcePatch A B) (R : ℝ) : SpatialTensor :=
  polarLift Q.patch (physicalCollarTensor R (sourceCollarData Q.fields.logFields))
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology
 theorem actual_collar_lift_eq {A B : SpatialTensor} (P Q : CollarSourcePatch A B)
    {R : ℝ} (hR : 0 < R) {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ angularOverlap P.patch Q.patch)
    (hW : angleTransition P.patch Q.patch (angularProjection y) ∈ Q.region)
    (hW' : angularProjection y ∈ P.region)
    (hf : Q.fields.SmoothAt (angularChange (angleTransition P.patch Q.patch) y))
    (hf' : P.fields.SmoothAt y)
    (hp : ∀ᶠ z in 𝓝 (angularChange (angleTransition P.patch Q.patch) y), (sourceMetric Q.fields.base z).PosDef)
    (hp' : ∀ᶠ z in 𝓝 y, (sourceMetric P.fields.base z).PosDef)
    (hk : (sourceTangentialK Q.fields.base (angularChange (angleTransition P.patch Q.patch) y)).IsHermitian)
    (hγ : (physicalCollarGamma R (sourceCollarData Q.fields.logFields)
      (angularChange (angleTransition P.patch Q.patch) y)).PosDef) :
    P.metric R (polarParam P.patch y) = Q.metric R (polarParam P.patch y) ∧
    P.tensor R (polarParam P.patch y) = Q.tensor R (polarParam P.patch y) := by
  have hrq : 0 < (angularChange (angleTransition P.patch Q.patch) y) 0 := by simpa using hr
  have hrel := actual_log_collar_angular_related P.patch Q.patch A B Q.region_open P.region_open
    Q.metric_CKS P.metric_CKS Q.tensor_CKS P.tensor_CKS
    (y := radiusLogPoint y)
    (by simpa [radiusLogPoint,angularProjection] using hy)
    (by simpa [radiusLogPoint,angularProjection] using hW)
    (by simpa [radiusLogPoint,angularProjection] using hW')
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf.regularAt)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf'.regularAt)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp')
  have hdetQ : determinant (Q.fields.base.logFields.sigma
      (radiusLogPoint (angularChange (angleTransition P.patch Q.patch) y))) ≠ 0 := by
    rw [determinant_eq]
    simpa [CollarSourcePatch.fields,spatialSourceFields,cksSourceFields,SourceMassFields.logFields,angularLift,radiusLogPoint,angularChange,angularProjection,slice] using (Q.patch.roundMetric_posDef (angleTransition_target hy)).det_pos.ne'
  have hdetP : determinant (P.fields.base.logFields.sigma (radiusLogPoint y)) ≠ 0 := by
    rw [determinant_eq]
    exact (P.patch.roundMetric_posDef hy.1).det_pos.ne'
  have hsf := sourceCollarData_smoothAt
    (show Q.fields.SmoothAt (logRadiusChart (radiusLogPoint (angularChange (angleTransition P.patch Q.patch) y))) by
      simpa only [logRadiusChart_radiusLogPoint hrq] using hf)
    (by simpa only [logRadiusChart_radiusLogPoint hrq] using hp) hdetQ
  have hsf' := sourceCollarData_smoothAt
    (show P.fields.SmoothAt (logRadiusChart (radiusLogPoint y)) by
      simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf')
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp') hdetP
  apply physicalCollar_lift_angular_covariant P.patch Q.patch hR hr hy hsf hsf' hrel hγ
  unfold physicalCollarRawTau
  apply Matrix.IsHermitian.smul _ (by rfl)
  apply sourceCollar_tau_hermitian
  · simpa only [logRadiusChart_radiusLogPoint hrq] using hp.self_of_nhds
  · simpa only [logRadiusChart_radiusLogPoint hrq] using hk
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def spatialDirection (x : E) : Sphere := if h : x = 0 then
  Classical.choice ((NormedSpace.sphere_nonempty.mpr (zero_le_one : (0:ℝ) ≤ 1)).coe_sort : Nonempty Sphere) else
  ⟨normalizeAmbient x, by
    simp only [Metric.mem_sphere,dist_zero_right,normalizeAmbient,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩
def polarCone (P : SmoothAngularPatch) (W : Set Angle) : Set E :=
  {x | x ≠ 0 ∧ spatialDirection x ∈ P.sphereRegion W}
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma spatialDirection_val {x : E} (hx : x ≠ 0) : (spatialDirection x : E) = normalizeAmbient x := by
  simp [spatialDirection,hx]
lemma spatialDirection_continuousAt {x : E} (hx : x ≠ 0) : ContinuousAt spatialDirection x := by
  have he : (fun y => (spatialDirection y : E)) =ᶠ[𝓝 x] normalizeAmbient := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hx] with y hy
    exact spatialDirection_val hy
  have hc : ContinuousAt (fun y => (spatialDirection y : E)) x := (normalizeAmbient_smooth hx).continuousAt.congr_of_eventuallyEq he
  exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc
lemma spatialDirection_polarParam (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    spatialDirection (polarParam P y) = P.chart.symm (angularProjection y) := by
  apply Subtype.ext
  rw [spatialDirection_val (norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne')),
    normalizeAmbient_polarParam P hr]
  rfl
 theorem polarCone_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (polarCone P W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem
    ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx.1)
    ((spatialDirection_continuousAt hx.1).preimage_mem_nhds ((P.sphereRegion_open hW).mem_nhds hx.2))
lemma polarInverse_direction (P : SmoothAngularPatch) {x : E}
    (hx : x ≠ 0) (hs : spatialDirection x ∈ P.chart.source) :
    polarInverse P x = slice ‖x‖ (P.chart (spatialDirection x)) := by
  unfold polarInverse
  rw [← spatialDirection_val hx,P.extension_eq _ hs]
 theorem polarCone_inverse (P : SmoothAngularPatch) {W : Set Angle} {x : E}
    (hx : x ∈ polarCone P W) :
    0 < (polarInverse P x) 0 ∧ angularProjection (polarInverse P x) ∈ W ∧
    angularProjection (polarInverse P x) ∈ P.chart.target ∧
    polarParam P (polarInverse P x) = x := by
  rw [polarInverse_direction P hx.1 hx.2.1]
  refine ⟨by simpa using norm_pos_iff.mpr hx.1,by
      rw [angularProjection_slice]
      exact hx.2.2,
    by simpa only [angularProjection_slice] using P.chart.map_source hx.2.1,?_⟩
  simp only [polarParam,slice_zero,angularProjection_slice,P.param_chart hx.2.1,
    spatialDirection_val hx.1,normalizeAmbient,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx.1),one_smul]
 theorem polarCone_param (P : SmoothAngularPatch) {W : Set Angle} {y : Point}
    (hy : angularProjection y ∈ W) (ht : angularProjection y ∈ P.chart.target)
    (hr : 0 < y 0) : polarParam P y ∈ polarCone P W := by
  refine ⟨norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne'),?_⟩
  rw [spatialDirection_polarParam P hr]
  exact ⟨P.chart.map_target ht,by change P.chart (P.chart.symm (angularProjection y)) ∈ W; rwa [P.chart.right_inv ht]⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

structure SourceCollarAtlas (A B : SpatialTensor) (ι : Type*) where
  patch : ι → CollarSourcePatch A B
  radius : ℝ
  radius_pos : 0 < radius
  jetSet : Set CKSMixedGeometry.MatrixThreeJet
  jetSet_compact : IsCompact jetSet
  jetSet_positive : ∀ q ∈ jetSet, Matrix.PosDef (fun i k => (q i k).1.1)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounds : ∀ i, (patch i).fields.UniformCollarInput jetSet bound radius (patch i).region
  source_smooth : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (patch i).fields.SmoothAt y
  source_positive : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (sourceMetric (patch i).fields.base y).PosDef
  source_symmetric : ∀ i y, y ∈ angularRadialTail radius (patch i).region → (sourceTangentialK (patch i).fields.base y).IsHermitian
  source_DEC : ∀ i y, y ∈ angularRadialTail radius (patch i).region →
    physicalDEC (sourceMetric (patch i).fields.base) (sourceTensor (patch i).fields)
      (sourceFrame (patch i).fields.base) y
  covers : ∀ n : Sphere, ∃ i, n ∈ (patch i).patch.sphereRegion (patch i).region

def collarAnnulus (R : ℝ) : Set E := {x | R < ‖x‖ ∧ ‖x‖ < 3*R}

def SourceCollarAtlas.localIndex {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (x : E) : ι := Classical.choose (q.covers (spatialDirection x))
def SourceCollarAtlas.metric {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (R : ℝ) : SpatialTensor := fun x => (q.patch (q.localIndex x)).metric R x
def SourceCollarAtlas.tensor {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (R : ℝ) : SpatialTensor := fun x => (q.patch (q.localIndex x)).tensor R x
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma CollarSourcePatch.sigma_eventually {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.region) :
    ∀ᶠ z in 𝓝 y, (P.fields.base.sigma (angularProjection z)).IsHermitian := by
  filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
    (P.region_open.mem_nhds hy)] with z hz
  exact (P.patch.roundMetric_posDef (P.region_target hz)).isHermitian
lemma SourceCollarAtlas.positive_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceMetric (q.patch i).fields.base z).PosDef := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_positive i z hz
lemma SourceCollarAtlas.symmetric_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceTangentialK (q.patch i).fields.base z).IsHermitian := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_symmetric i z hz
lemma slice_exp_log_projection {y : CKSMixedGeometry.Point} (hy : 0 < y 0) :
    slice (Real.exp (Real.log (y 0))) (angularProjection y) = y := by
  rw [Real.exp_log hy,slice_projection]
lemma logRadiusChart_slice_exp (ρ : ℝ) (a : Angle) :
    logRadiusChart (slice ρ a) = slice (Real.exp ρ) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

theorem SourceCollarAtlas.eventually_pointwise {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∀ R ≥ R₀, ∀ i y,
      R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y ∧
      physicalDEC (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  obtain ⟨R₁,hR₁,hreg⟩ := source_actual_collar_regular q.jetSet_compact q.jetSet_positive q.bound_nonneg
  obtain ⟨R₂,hR₂,hDEC⟩ := source_actual_collar_physical_DEC q.jetSet_compact q.jetSet_positive q.bound_nonneg
  refine ⟨max (max R₁ R₂) (q.radius+1),hR₁.trans ((le_max_left _ _).trans (le_max_left _ _)),?_,?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  intro R hR i y hr ht hw
  have hR1 : R₁ ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hR2 : R₂ ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hr0 : 0 < y 0 := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)) hr
  have hrad : q.radius < y 0 := lt_of_lt_of_le
    ((show q.radius < q.radius+1 by linarith).trans_le ((le_max_right _ _).trans hR)) hr
  have hx : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hw⟩
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hr0)
  have hf := q.source_smooth i y hx
  have hp := q.positive_eventually i hx
  have hk := q.symmetric_eventually i hx
  have hσ := (q.patch i).sigma_eventually (y := slice (Real.log (y 0)) (angularProjection y))
    (by simpa only [angularProjection_slice] using hw)
  obtain ⟨hm,h1,h2,h3,h4,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hr0])
  rw [hlog] at hb'
  constructor
  · have h := hreg R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR1
      (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
      (by rwa [hlog]) (by rwa [hlog]) hσ (by rwa [hlog]) hm h1 h2 h3 h4
      (by rwa [hlog])
    simpa only [slice_exp_log_projection hr0] using h
  · have h := hDEC R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR2
      (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
      (by rwa [hlog]) (by rwa [hlog]) hσ (by rwa [hlog]) hm h1 h2 h3 h4
      (by rwa [hlog]) (by rw [hlog]; exact q.source_DEC i y hx)
    simpa only [slice_exp_log_projection hr0] using h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarCone_overlap (P Q : SmoothAngularPatch) {W Z : Set Angle} {x : E}
    (hP : x ∈ polarCone P W) (hQ : x ∈ polarCone Q Z) :
    angularProjection (polarInverse P x) ∈ angularOverlap P Q ∧
    angleTransition P Q (angularProjection (polarInverse P x)) ∈ Z ∧
    angularChange (angleTransition P Q) (polarInverse P x) = polarInverse Q x := by
  rw [polarInverse_direction P hP.1 hP.2.1,polarInverse_direction Q hQ.1 hQ.2.1]
  simp only [angularProjection_slice]
  have ht : P.chart (spatialDirection x) ∈ angularOverlap P Q := by
    refine ⟨P.chart.map_source hP.2.1,?_⟩
    change P.chart.symm (P.chart (spatialDirection x)) ∈ Q.chart.source
    rw [P.chart.left_inv hP.2.1]
    exact hQ.2.1
  have he : angleTransition P Q (P.chart (spatialDirection x)) = Q.chart (spatialDirection x) := by
    rw [angleTransition_eq_chart ht,P.chart.left_inv hP.2.1]
  exact ⟨ht,he ▸ hQ.2.2,by simp only [angularChange,slice_zero,angularProjection_slice,he]⟩
lemma physicalCollarGamma_pos_of_metric {R : ℝ} {f : LogCollarData} {y : CKSMixedGeometry.Point}
    (h : (physicalCollarMetric R f y).PosDef) : (physicalCollarGamma R f y).PosDef := by
  have hh := h.submatrix (e := Fin.succ) (Fin.succ_injective 2)
  have he : (physicalCollarMetric R f y).submatrix Fin.succ Fin.succ = physicalCollarGamma R f y := by
    ext i j
    exact foliationMetric_angular (physicalCollarU R f y) (physicalCollarGamma R f y) (physicalCollarShift R f y) i j
  rwa [he] at hh
lemma SourceCollarAtlas.compatible {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {R : ℝ} (hR : 0 < R) (hqR : q.radius < R)
    (hregular : ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y)
    {x : E} (hr : R ≤ ‖x‖) (ht : ‖x‖ ≤ 3*R) {i j : ι}
    (hi : x ∈ polarCone (q.patch i).patch (q.patch i).region)
    (hj : x ∈ polarCone (q.patch j).patch (q.patch j).region) :
    (q.patch i).metric R x = (q.patch j).metric R x ∧
    (q.patch i).tensor R x = (q.patch j).tensor R x := by
  let y := polarInverse (q.patch i).patch x
  let z := polarInverse (q.patch j).patch x
  obtain ⟨hyi,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hi
  obtain ⟨hzj,hzw,hzt,hzx⟩ := polarCone_inverse (q.patch j).patch hj
  obtain ⟨hov,hw,he⟩ := polarCone_overlap (q.patch i).patch (q.patch j).patch hi hj
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hzr : z 0 = ‖x‖ := by simp [z,polarInverse]
  have hyold : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rw [hyr]; exact hqR.trans_le hr, hyw⟩
  have hzold : z ∈ angularRadialTail q.radius (q.patch j).region := ⟨by rw [hzr]; exact hqR.trans_le hr, hzw⟩
  have hzreg := hregular j z (by rwa [hzr]) (by rwa [hzr]) hzw
  have hh := actual_collar_lift_eq (q.patch i) (q.patch j) hR hyi hov hw hyw
    (by rw [he]; exact q.source_smooth j z hzold) (q.source_smooth i y hyold)
    (by rw [he]; exact q.positive_eventually j hzold) (q.positive_eventually i hyold)
    (by rw [he]; exact q.source_symmetric j z hzold)
    (by rw [he]; exact physicalCollarGamma_pos_of_metric hzreg.metric_positive)
  rwa [hyx] at hh
lemma SourceCollarAtlas.local_eq {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {R : ℝ} (hR : 0 < R) (hqR : q.radius < R)
    (hregular : ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y)
    {x : E} (hr : R ≤ ‖x‖) (ht : ‖x‖ ≤ 3*R) {i : ι}
    (hi : x ∈ polarCone (q.patch i).patch (q.patch i).region) :
    q.metric R x = (q.patch i).metric R x ∧ q.tensor R x = (q.patch i).tensor R x := by
  exact q.compatible hR hqR hregular hr ht
    ⟨hi.1,Classical.choose_spec (q.covers (spatialDirection x))⟩ hi
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
local instance globalCollarEeNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance globalCollarEeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma collarAnnulus_open (R : ℝ) : IsOpen (collarAnnulus R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
lemma polarLift_symmetric (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → Matrix CKSMixedGeometry.I CKSMixedGeometry.I ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : (F y).IsHermitian) : ∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v := by
  intro v w
  unfold polarLift
  rw [polarInverse_param P hr hy]
  exact CKSTangentCoefficients.matrixBilinear_symm h _ _

theorem actual_global_collar {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R ≥ R₀,
      ContDiffOn ℝ ∞ (q.metric R) (collarAnnulus R) ∧
      ContDiffOn ℝ ∞ (q.tensor R) (collarAnnulus R) ∧
      (∀ x ∈ collarAnnulus R, (∀ v w, q.metric R x v w = q.metric R x w v) ∧
        (∀ v : E, v ≠ 0 → 0 < q.metric R x v v) ∧
        ∀ v w, q.tensor R x v w = q.tensor R x w v) ∧
      (∀ i x, x ∈ collarAnnulus R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
        q.metric R x = (q.patch i).metric R x ∧ q.tensor R x = (q.patch i).tensor R x) ∧
      ∀ i y, R < y 0 → y 0 < 3*R → angularProjection y ∈ (q.patch i).region →
        physicalDEC (fun z => fun a b => polarTensorComponents (q.patch i).patch (q.metric R) a b z)
          (fun z => fun a b => polarTensorComponents (q.patch i).patch (q.tensor R) a b z)
          (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  obtain ⟨R₀,hR₀,hq₀,hpoint⟩ := q.eventually_pointwise
  refine ⟨R₀,hR₀,?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hR₀.trans hR)
  have hqR := hq₀.trans_le hR
  have hreg := fun i y hr ht hw => (hpoint R hR i y hr ht hw).1
  have hlocal : ∀ i x, x ∈ collarAnnulus R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
      q.metric R x = (q.patch i).metric R x ∧ q.tensor R x = (q.patch i).tensor R x := by
    intro i x hx hi
    exact q.local_eq hRpos hqR hreg hx.1.le hx.2.le hi
  have hs : ∀ x ∈ collarAnnulus R, ContDiffAt ℝ ∞ (q.metric R) x ∧
      ContDiffAt ℝ ∞ (q.tensor R) x ∧
      (∀ v w, q.metric R x v w = q.metric R x w v) ∧
      (∀ v : E, v ≠ 0 → 0 < q.metric R x v v) ∧
      ∀ v w, q.tensor R x v w = q.tensor R x w v := by
    intro x hx
    let i := q.localIndex x
    have hx0 : x ≠ 0 := norm_pos_iff.mp (hRpos.trans hx.1)
    have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
      ⟨hx0,Classical.choose_spec (q.covers (spatialDirection x))⟩
    have he : ∀ᶠ z in 𝓝 x, q.metric R z = (q.patch i).metric R z ∧
        q.tensor R z = (q.patch i).tensor R z := by
      filter_upwards [(collarAnnulus_open R).mem_nhds hx,
        (polarCone_open _ (q.patch i).region_open).mem_nhds hc] with z hz hzc
      exact hlocal i z hz hzc
    obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
    have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
    have hg := hreg i (polarInverse (q.patch i).patch x) (by rw [hyr]; exact hx.1.le)
      (by rw [hyr]; exact hx.2.le) hyw
    obtain ⟨hsm,hsym,hpos⟩ := polarLift_smooth_positive (q.patch i).patch _ hy0 hyt hg.metric_smooth hg.metric_positive
    have hst := polarLift_smoothAt (q.patch i).patch _ hy0 hyt hg.tensor_smooth
    have hsyk := polarLift_symmetric (q.patch i).patch _ hy0 hyt hg.tensor_symmetric
    rw [hyx] at hsm hsym hpos hst hsyk
    refine ⟨hsm.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
      hst.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
    · rw [he.self_of_nhds.1]; exact hsym
    · rw [he.self_of_nhds.1]; exact hpos
    · rw [he.self_of_nhds.2]; exact hsyk
  refine ⟨fun x hx => (hs x hx).1.contDiffWithinAt,
    fun x hx => (hs x hx).2.1.contDiffWithinAt,fun x hx => (hs x hx).2.2,hlocal,?_⟩
  intro i y hr ht hw
  have he : ∀ᶠ z in 𝓝 y,
      (fun a b => polarTensorComponents (q.patch i).patch (q.metric R) a b z) =
        physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) z ∧
      (fun a b => polarTensorComponents (q.patch i).patch (q.tensor R) a b z) =
        physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields) z := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr,
      (isOpen_lt (continuous_apply 0) continuous_const).mem_nhds ht,
      angularProjection.continuous.continuousAt.preimage_mem_nhds ((q.patch i).region_open.mem_nhds hw)] with z hzR hzT hzw
    have hz0 := hRpos.trans hzR
    have hzt := (q.patch i).region_target hzw
    have hn := polarParam_norm (q.patch i).patch hz0.le
    have hzann : polarParam (q.patch i).patch z ∈ collarAnnulus R := ⟨by rwa [hn],by rwa [hn]⟩
    have hzcone := polarCone_param (q.patch i).patch hzw hzt hz0
    have ⟨hgm,hkt⟩ := hlocal i _ hzann hzcone
    constructor
    · ext a b
      change q.metric R (polarParam (q.patch i).patch z) _ _ = _
      rw [hgm]
      exact polarLift_components (q.patch i).patch _ hz0 hzt a b
    · ext a b
      change q.tensor R (polarParam (q.patch i).patch z) _ _ = _
      rw [hkt]
      exact polarLift_components (q.patch i).patch _ hz0 hzt a b
  exact (physicalDEC_congr (he.mono (fun z hz => hz.1)) (he.mono (fun z hz => hz.2))
    (Eventually.of_forall (fun _ _ => rfl))).mpr (hpoint R hR i y hr.le ht.le hw).2
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)
lemma cksSourceFields_gamma (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceGamma (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => A a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mg a.succ b.succ (angularProjection y) +
    (A a.succ b.succ y - ordinaryLeadingComponent 1 (mg a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_tangential (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceTangentialK (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => B a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mK a.succ b.succ (angularProjection y) +
    (B a.succ b.succ y - ordinaryLeadingComponent 1 (mK a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_radial (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceRadialMetric (cksSourceFields σ A B mr mg mK).base y =
      1/(1+(y 0)^2)+A 0 0 y := by
  simp only [sourceRadialMetric,cksSourceFields,ordinaryLeadingComponent]
  ring
lemma metricBlock_add_perturbation (a : ℝ) (q : Mat) (A : AmbientMat)
    (hA : A.IsHermitian) :
    metricBlock (a+A 0 0) (fun i => A 0 i.succ)
      (q+Matrix.of (fun i k : Fin 2 => A i.succ k.succ)) = metricBlock a 0 q+A := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [metricBlock]
  all_goals exact CKSAngularGeometry.hermitian_real_symmetry hA _ _

theorem cksSourceFields_reconstruct (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point)
    (hA : Matrix.IsHermitian (fun i k => A i k y)) (hB : Matrix.IsHermitian (fun i k => B i k y)) :
    sourceMetric (cksSourceFields σ A B mr mg mK).base y =
      cksReference σ y + Matrix.of (fun i k => A i k y) ∧
    sourceTensor (cksSourceFields σ A B mr mg mK) y =
      cksReference σ y + Matrix.of (fun i k => B i k y) := by
  constructor
  · unfold sourceMetric cksReference
    rw [cksSourceFields_gamma,cksSourceFields_radial]
    exact metricBlock_add_perturbation _ _ _ hA
  · unfold sourceTensor cksReference
    rw [cksSourceFields_tangential]
    exact metricBlock_add_perturbation _ _ _ hB
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixThreeJets_value_bound {q : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hq : ‖matrixThreeJets q x‖ ≤ B) : ‖q x‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr; intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr; intro j
  exact (norm_fst_le ((matrixThreeJets q x i j).1)).trans
    ((norm_fst_le (matrixThreeJets q x i j)).trans
      ((Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x)).trans hq))

lemma actualScalarJet_value_bound {q : Point → ℝ} {x : Point} {B : ℝ}
    (hq : ‖actualScalarJet q x‖ ≤ B) : |q x| ≤ B :=
  (norm_fst_le (actualScalarJet q x)).trans hq

theorem source_collar_metric_comparison {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R, R₀ ≤ R → 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.RegularAt (logRadiusChart (slice ρ x)) →
      ContDiffAt ℝ 3 f.base.mK (angularProjection (logRadiusChart (slice ρ x))) →
      ContDiffAt ℝ 3 f.base.ek (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      ∀ v : Fin 3 → ℝ,
      l R * CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.radialNormalize (Real.exp ρ) (sourceMetric f.base (logRadiusChart (slice ρ x)))) v ≤
      CKSAngularGeometry.quadratic3
        (CKSAngularGeometry.fieldNormalizedMetric (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f.logFields).angular ρ) x) v := by
  obtain ⟨Rc,hRc,C,hC,hmetric⟩ := source_actual_collar_metric hK hreg hB
  let val : MatrixThreeJet → CKSAngularGeometry.Mat := fun q i j => (q i j).1.1
  have hv : Continuous val := by unfold val; fun_prop
  obtain ⟨κ,hκ,hlower⟩ := CKSAngularGeometry.compact_background_lower (hK.image hv)
    (by rintro _ ⟨q,hq,rfl⟩; exact hreg q hq)
  let R₀ := max Rc (max 1 (3*C/κ+1))
  have hRone : 1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hsmall (R : ℝ) (hR : R₀ ≤ R) : 3*C ≤ κ*R^3 := by
    have h1 : 1 ≤ R := hRone.trans hR
    have hc : 3*C/κ ≤ R := (le_add_of_nonneg_right zero_le_one).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
    have hc' : 3*C ≤ R*κ := (div_le_iff₀ hκ).mp hc
    have h1' : R ≤ R^3 := by nlinarith [sq_nonneg (R-1)]
    nlinarith
  refine ⟨R₀,hRone,CKSAngularGeometry.comparisonFactor C B κ,
    CKSAngularGeometry.comparisonFactor_tendsto C B κ,?_,?_⟩
  · intro R hR
    exact ⟨CKSAngularGeometry.comparisonFactor_nonneg hB hκ (zero_lt_one.trans_le (hRone.trans hR)) (hsmall R hR),
      CKSAngularGeometry.comparisonFactor_le_one hC hB hκ (zero_lt_one.trans_le (hRone.trans hR))⟩
  intro R f ρ x hR hr htop hf hmk hek hp hσ hs hmg hmK hmr hb
  have hRcR : Rc ≤ R := (le_max_left _ _).trans hR
  have hG := hmetric R f ρ x hRcR hr htop hf hmk hek hp hσ hs hmg hmK hmr hb
  have hg0 : ‖f.base.mg (angularProjection (logRadiusChart (slice ρ x)))‖ ≤ B := by
    rw [angularProjection_logRadiusChart]
    exact matrixThreeJets_value_bound (q:=angularLift f.base.mg) (x:=slice ρ x) hB hmg
  have hmr0 : |f.base.mr (angularProjection (logRadiusChart (slice ρ x)))| ≤ B := by
    rw [angularProjection_logRadiusChart]
    exact actualScalarJet_value_bound (q:=angularLift f.base.mr) (x:=slice ρ x) hmr
  have hrad : logRadiusChart (slice ρ x) 0=Real.exp ρ := by simp [logRadiusChart]
  have hbase : f.base.sigma (angularProjection (logRadiusChart (slice ρ x)))=
      f.logFields.base.sigma (slice ρ x) := by rw [angularProjection_logRadiusChart]; rfl
  have hg := originalMetric_error (f:=f.base) (y:=logRadiusChart (slice ρ x))
    (by rw [hrad]; exact (hRone.trans hR).trans hr) hB hmr0 hg0 hb.base
  rw [hrad,hbase] at hg
  exact CKSAngularGeometry.metric_comparison_uniform hC hB hκ
    (zero_lt_one.trans_le (hRone.trans hR)) hr (hsmall R hR) hG hg
    (hlower _ ⟨_,hσ,rfl⟩)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarMetric_normalized (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
      (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a) :
    radialNormalize (Real.exp ρ) (physicalCollarMetric R f (slice (Real.exp ρ) a))=
      fieldNormalizedMetric (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  have hn : fieldNormalizedLapse (collarParams R (Real.exp ρ)) (f.angular ρ) a ≠ 0 := by
    unfold fieldNormalizedLapse
    rw [lapseNormalizedField_rad]
    exact div_ne_zero (Real.sqrt_pos.mpr hu).ne' hd.ne'
  unfold physicalCollarMetric
  rw [physicalCollarU_slice R ρ hf hσ hp, physicalCollarGamma_slice,
    physicalCollarShift_slice,physicalBaseLapse_eq (Real.exp_pos ρ)]
  have he : 1/Real.exp ρ^5=(1/Real.exp ρ)^5 := by simp
  rw [he,radialNormalize_foliation (Real.exp_pos ρ) hn]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_physical_collar_metric_comparison
    {K : Set CKSMixedGeometry.MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R, R₀ ≤ R → 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (a : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ a)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ a)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ a), (f.base.sigma (angularProjection y)).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ a) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ a)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ a)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ a)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ a)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ a)) →
      ∀ v : Fin 3 → ℝ,
      l R * quadratic3 (sourceMetric f.base (logRadiusChart (slice ρ a))) v ≤
      quadratic3 (physicalCollarMetric R (sourceCollarData f.logFields)
        (slice (Real.exp ρ) a)) v
 := by
  obtain ⟨R₁,hR₁,l,hl,hlb,hcomp⟩ := source_collar_metric_comparison hK hreg hB
  obtain ⟨R₂,hR₂,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),l,hl,?_,?_⟩
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R f ρ a hR hr htop hf hp hσ hmem hs hmg hmk hmr hb
  have hR₁R : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR₂R : R₂ ≤ R := (le_max_right _ _).trans hR
  have hsd : determinant (f.base.logFields.sigma (slice ρ a)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hsm := sourceCollarData_smoothAt hf hp hsd
  have hσD := sourceCollar_sigma_radial (f := f) hf.base.regularAt
  have he : ∀ᶠ y in 𝓝 (slice ρ a), ((sourceCollarData f.logFields).metricError y).IsHermitian := by
    filter_upwards [logRadiusChart_smooth.continuous.continuousAt.tendsto.eventually hp,hσ] with y hyp hys
    exact sourceCollar_metricError_hermitian hyp hys
  have hregions := (hfuture R f ρ a hR₂R hr htop hf hp hmem hs hmg hmk hmr hb).1
  obtain ⟨hγ,hd,hu⟩ := physical_collar_pivots hsm hσ he hσD hregions.1 hregions.2.1 hregions.2.2
  have hnormalize := physicalCollarMetric_normalized R ρ hsm.regularAt hσD hγ.self_of_nhds
    hregions.2.1 hregions.2.2
  have hmk' := hf.base.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hek' := hf.base.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have h := hcomp R f ρ a hR₁R hr htop hf.regularAt hmk' hek' hp hmem hs hmg hmk hmr hb
  rw [← hnormalize] at h
  exact radialNormalize_comparison (Real.exp_ne_zero ρ) h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma hyperbolicField_apply (x v w : E) : hyperbolicField x v w = hyperbolicMetric x v w := by
  change inner ℝ v w - (1/(1+‖x‖^2)) * (inner ℝ x v * inner ℝ x w) =
    inner ℝ v w - inner ℝ x v * inner ℝ x w / (1+‖x‖^2)
  ring
lemma polarParam_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (v : Point) :
    fderiv ℝ (polarParam P) y v = v 0 • P.param (angularProjection y) +
      y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) := by
  have hP := (P.param_contDiffAt hy).differentiableAt (by simp)
  have hp := (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).hasFDerivAt (x := y)
  have ha := hP.hasFDerivAt.comp y angularProjection.hasFDerivAt
  have hh := hp.smul ha
  change HasFDerivAt (polarParam P) _ y at hh
  rw [hh.fderiv]
  change y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) + v 0 • P.param (angularProjection y) = _
  exact add_comm _ _
lemma polarParam_fderiv_radial (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (polarParam P) y (basis 0) = P.param (angularProjection y) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis 0) = 0 := by ext a; simp [angularProjection,basis,Fin.succ_ne_zero]
  rw [ha]
  simp [basis]
lemma polarParam_fderiv_angular (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (a : Fin 2) :
    fderiv ℝ (polarParam P) y (basis a.succ) = y 0 • fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis a.succ) = CKSAngularGeometry.basis a := by
    ext b
    simp [angularProjection,basis,CKSAngularGeometry.basis,Pi.single_apply,Fin.succ_inj]
  rw [ha]
  simp [basis,Fin.succ_ne_zero]
lemma hyperbolicField_polar (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P hyperbolicField i j y) = cksReference (angularRoundMetric P.param) y := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy]
      unfold hyperbolicMetric
      rw [polarParam_norm P hr.le]
      simp only [polarParam,real_inner_smul_left,hi,mul_one]
      simp only [cksReference,CKSAngularGeometry.metricBlock]
      change 1 - y 0 * y 0/(1+(y 0)^2) = 1/(1+(y 0)^2)
      have hnz : 1 + (y 0)^2 ≠ 0 := by positivity
      field_simp
      ring
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases b <;> simp [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,cksReference,CKSAngularGeometry.metricBlock]
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      have hta : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases a <;> simp_all [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,cksReference,CKSAngularGeometry.metricBlock]
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,mul_zero,zero_div,sub_zero]
      fin_cases a <;> fin_cases b <;>
        simp [cksReference,CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry
lemma polarTensorComponents_hermitian (P : SmoothAngularPatch) (A : SpatialTensor)
    (y : CKSMixedGeometry.Point)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v) :
    Matrix.IsHermitian (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact hA _ _
lemma polar_sourceSpatial (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    cksReference (angularRoundMetric P.param) y + Matrix.of (fun i j => polarTensorComponents P A i j y) =
      (fun i j => polarTensorComponents P (sourceSpatial A) i j y) := by
  rw [← hyperbolicField_polar P hr hy]
  rfl

theorem spatial_source_reconstruction {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hA : ∀ v w, A (polarParam P.patch y) v w = A (polarParam P.patch y) w v)
    (hB : ∀ v w, B (polarParam P.patch y) v w = B (polarParam P.patch y) w v) :
    sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) ∧
    sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) ∧
    polarLift P.patch (sourceMetric P.fields.base) (polarParam P.patch y) = sourceSpatial A (polarParam P.patch y) ∧
    polarLift P.patch (sourceTensor P.fields) (polarParam P.patch y) = sourceSpatial B (polarParam P.patch y) := by
  obtain ⟨hg,hk⟩ := cksSourceFields_reconstruct (angularRoundMetric P.patch.param)
    (polarTensorComponents P.patch A) (polarTensorComponents P.patch B) P.mr P.mg P.mK y
    (polarTensorComponents_hermitian P.patch A y hA) (polarTensorComponents_hermitian P.patch B y hB)
  have heg : sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) :=
    hg.trans (polar_sourceSpatial P.patch A hr hy)
  have hek : sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) :=
    hk.trans (polar_sourceSpatial P.patch B hr hy)
  refine ⟨heg,hek,?_,?_⟩
  · apply (polarLift_reconstruction P.patch (sourceMetric P.fields.base) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) heg.symm
  · apply (polarLift_reconstruction P.patch (sourceTensor P.fields) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) hek.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma SourceCollarAtlas.eventually_local_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
        ∀ v : Fin 3 → ℝ,
        l R * quadratic3 (sourceMetric (q.patch i).fields.base y) v ≤
          quadratic3 (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) y) v := by
  obtain ⟨R₁,hR₁,l,hl,hlb,hcomp⟩ := source_physical_collar_metric_comparison
    q.jetSet_compact q.jetSet_positive q.bound_nonneg
  refine ⟨max R₁ (q.radius+1),hR₁.trans (le_max_left _ _),?_,l,hl,?_,?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R hR i y hr ht hw v
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans hR
  have hr0 : 0 < y 0 := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)) hr
  have hrad : q.radius < y 0 := lt_of_lt_of_le
    ((show q.radius < q.radius+1 by linarith).trans_le ((le_max_right _ _).trans hR)) hr
  have hx : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hw⟩
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hr0)
  have hf := q.source_smooth i y hx
  have hp := q.positive_eventually i hx
  have hσ := (q.patch i).sigma_eventually (y := slice (Real.log (y 0)) (angularProjection y))
    (by simpa only [angularProjection_slice] using hw)
  obtain ⟨hm,h1,h2,h3,h4,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hr0])
  rw [hlog] at hb'
  have h := hcomp R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR1
    (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
    (by rwa [hlog]) (by rwa [hlog]) hσ hm h1 h2 h3 h4 (by rwa [hlog]) v
  simpa only [hlog,slice_exp_log_projection hr0] using h
lemma polarLift_quadratic (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → AmbientMat)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (v : E) :
    polarLift P F (polarParam P y) v v = quadratic3 (F y) (fderiv ℝ (polarInverse P) (polarParam P y) v) := by
  unfold polarLift
  rw [polarInverse_param P hr hy]
  change CKSTangentCoefficients.matrixBilinear (F y)
    (fderiv ℝ (polarInverse P) (polarParam P y) v)
    (fderiv ℝ (polarInverse P) (polarParam P y) v) = _
  exact CKSTangentCoefficients.matrixBilinear_apply _ _ _

theorem actual_global_collar_source_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ x ∈ collarAnnulus R, ∀ v : E,
        l R * sourceSpatial A x v v ≤ q.metric R x v v := by
  obtain ⟨R₁,hR₁,hq₁,l,hl,hlb,hcomp⟩ := q.eventually_local_lower
  obtain ⟨R₂,hR₂,hq₂,hreg⟩ := q.eventually_pointwise
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),l,hl,?_,?_⟩
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R hR x hx v
  have hR1 := (le_max_left R₁ R₂).trans hR
  have hR2 := (le_max_right R₁ R₂).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)
  have hqx : q.radius < ‖x‖ := (hq₁.trans_le hR1).trans hx.1
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (hRpos.trans hx.1),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
  let y := polarInverse (q.patch i).patch x
  have hrec := spatial_source_reconstruction (q.patch i) hy hyt
    (by rw [hyx]; exact hA x hqx) (by rw [hyx]; exact hB x hqx)
  have hg := (q.local_eq hRpos (hq₂.trans_le hR2)
    (fun i y hr ht hw => (hreg R hR2 i y hr ht hw).1) hx.1.le hx.2.le hc).1
  have hlower := hcomp R hR1 i y (by dsimp [y]; rw [hyr]; exact hx.1.le)
    (by dsimp [y]; rw [hyr]; exact hx.2.le) hyw (fderiv ℝ (polarInverse (q.patch i).patch) x v)
  rw [hg,← hyx,← hrec.2.2.1,polarLift_quadratic _ _ hy hyt]
  change _ ≤ polarLift (q.patch i).patch _ (polarParam (q.patch i).patch y) v v
  rw [polarLift_quadratic _ _ hy hyt]
  simpa only [hyx] using hlower
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_rounding_initial_fields {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hR : 0 < R) (hr : 0 < x 0) (hi : x 0 ≤ 2*R) :
    physicalCollarGamma R (sourceCollarData f.logFields) x = sourceGamma f.base x ∧
    physicalCollarShift R (sourceCollarData f.logFields) x = sourceShift f.base x := by
  have hc := logRadiusChart_radiusLogPoint hr
  have he := radiusLogPoint_exp hr
  have hg := congrFun (sourceGamma_pullback f.base) (radiusLogPoint x)
  have hshift := congrFun (sourceShift_pullback f.base) (radiusLogPoint x)
  rw [hc] at hg hshift
  have he0 := roundingWeight_zero hR hi
  constructor
  · simp only [physicalCollarGamma,collarQ,radialLift,he,he0,sub_zero,one_smul]
    change (x 0)^2 • (f.logFields.base.sigma (radiusLogPoint x)+logQError f.logFields.base (radiusLogPoint x)) = _
    rw [logQError_scaled,he]
    have hh : f.logFields.base.sigma (radiusLogPoint x)+
        ((1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x)-f.logFields.base.sigma (radiusLogPoint x)) =
        (1/(x 0)^2) • logGamma f.logFields.base (radiusLogPoint x) := by abel
    rw [hh,smul_smul,mul_one_div_cancel (pow_ne_zero _ hr.ne'),one_smul]
    exact hg.symm
  · simp only [physicalCollarShift,collarShift,radialLift,he,he0,sub_zero,one_smul]
    exact hshift.symm

lemma source_rounding_initial_fields_eventually {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 < 2*R) :
    ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R (sourceCollarData f.logFields) y = sourceGamma f.base y ∧
      physicalCollarShift R (sourceCollarData f.logFields) y = sourceShift f.base y := by
  have hR : 0 < R := by linarith
  have hr' := ((continuous_apply 0).continuousAt (x := x)).eventually (Ioi_mem_nhds hr)
  have hi' := ((continuous_apply 0).continuousAt (x := x)).eventually (Iio_mem_nhds hi)
  filter_upwards [hr',hi'] with y hyr hyi
  exact source_rounding_initial_fields hR hyr hyi.le

lemma source_inner_collar_lapse_closed {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 ≤ R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x) :
    physicalCollarU R (sourceCollarData f.logFields) x=sourceLapse f.base x := by
  have hR : 0 < R := hr.trans_le hi
  have hi2 : x 0 < 2*R := by linarith
  have h := source_rounding_initial_fields_eventually (f := f) hr hi2
  have he := radialExpansion_congr (h.mono (fun _ hy => hy.1)) (h.mono (fun _ hy => hy.2))
  obtain ⟨_,_,ht,hF,_,_,_⟩ := source_inner_collar_fields hR hr hi hf hp.self_of_nhds
  unfold physicalCollarU radialMassLapse
  rw [he]
  unfold radialMassRadical
  rw [ht,hF]
  exact source_radialMassLapse_eq hr.ne' hp.self_of_nhds hd

theorem source_inner_collar_recovery_closed {R : ℝ} {f : SourceTensorFields} {x : Point}
    (hr : 0 < x 0) (hi : x 0 ≤ R) (hf : f.base.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (sourceMetric f.base y).PosDef)
    (hd : 0 < sourceExpansion f.base x)
    (hk : (sourceTangentialK f.base x).IsHermitian) :
    physicalCollarMetric R (sourceCollarData f.logFields) x=sourceMetric f.base x ∧
    physicalCollarTensor R (sourceCollarData f.logFields) x=sourceTensor f x ∧
    ∀ i, physicalCollarFrame R (sourceCollarData f.logFields) i x=sourceFrame f.base i x
 := by
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := source_inner_collar_fields (hr.trans_le hi) hr hi hf hp.self_of_nhds
  have hU := source_inner_collar_lapse_closed hr hi hf hp hd
  have hT : physicalCollarTangential R (sourceCollarData f.logFields) x=sourceTangentialK f.base x := by
    unfold physicalCollarTangential radialTangential
    rw [hγ,ht,hτ]
    exact source_radialTangential_eq hp.self_of_nhds
  refine ⟨?_,?_,?_⟩
  · unfold physicalCollarMetric
    rw [hU,hγ,hs]
    exact source_metric_foliation hp.self_of_nhds
  · unfold physicalCollarTensor
    rw [hU,hL,hη,hT,hs]
    exact source_tensor_foliation hp.self_of_nhds hk
  · intro i
    unfold physicalCollarFrame sourceFrame
    rw [hU,hγ,hs]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice CKSAngularGeometry CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma sourceExpansion_of_old_future {R ρ : ℝ} {f : SourceTensorFields} {x : AP}
    (hf : f.SmoothAt (logRadiusChart (slice ρ x)))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef)
    (hσ : ∀ᶠ y in 𝓝 (slice ρ x), (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceTangentialK f.base y).IsHermitian)
    (hs : determinant (f.base.logFields.sigma (slice ρ x)) ≠ 0)
    (hq : positiveAngular (fieldQ (oldParams (collarParams R (Real.exp ρ)))
      ((sourceCollarData f.logFields).angular ρ) x))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ))
      (fieldF (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (oldParams (collarParams R (Real.exp ρ))) ((sourceCollarData f.logFields).angular ρ)) x) :
    0 < sourceExpansion f.base (logRadiusChart (slice ρ x)) := by
  let S := 2*Real.exp ρ
  have hS : 0 < S := by dsimp [S]; positivity
  have hi : Real.exp ρ < S := by dsimp [S]; linarith [Real.exp_pos ρ]
  have heq : collarParams S (Real.exp ρ)=oldParams (collarParams R (Real.exp ρ)) :=
    collarParams_initial hS hi.le
  have hc := sourceCollarData_smoothAt hf hp hs
  obtain ⟨hσh,heh,hτh⟩ := sourceCollar_symmetries hp hσ hk
  have hσD := sourceCollar_sigma_radial_eventually hf.base.regularAt
  obtain ⟨hγ,hd',hu'⟩ := physical_collar_pivots (R:=S) hc hσh heh hσD.self_of_nhds
    (by rw [heq]; exact hq) (by rw [heq]; exact hu) (by rw [heq]; exact hd)
  have hr : 0 < (slice (Real.exp ρ) x) 0 := by simpa using Real.exp_pos ρ
  have hi' : (slice (Real.exp ρ) x) 0 < S := by simpa using hi
  have hf' : f.SmoothAt (slice (Real.exp ρ) x) := by simpa using hf
  have hp' : ∀ᶠ y in 𝓝 (slice (Real.exp ρ) x), (sourceMetric f.base y).PosDef := by simpa using hp
  have hfields := source_inner_collar_fields_eventually hr hi' hf'.base.regularAt hp'
  have hexp := radialExpansion_congr (hfields.mono (fun _ h => h.1)) (hfields.mono (fun _ h => h.2.1))
  rw [source_radialExpansion_eq] at hexp
  simpa only [logRadiusChart_slice,← hexp] using hd'
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma SourceCollarAtlas.eventually_sourceExpansion {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ S : ℝ, 1 ≤ S ∧ q.radius < S ∧ ∀ i y,
      S ≤ y 0 → angularProjection y ∈ (q.patch i).region →
      0 < sourceExpansion (q.patch i).fields.base y := by
  obtain ⟨R₀,hR₀,hfuture⟩ := source_actual_collar_future_regions
    q.jetSet_compact q.jetSet_positive q.bound_nonneg
  refine ⟨max R₀ (q.radius+1),hR₀.trans (le_max_left _ _),?_,?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  intro i y hr hw
  have hR : R₀ ≤ y 0 := (le_max_left _ _).trans hr
  have hr0 : 0 < y 0 := lt_of_lt_of_le zero_lt_one (hR₀.trans hR)
  have hrad : q.radius < y 0 := lt_of_lt_of_le
    ((show q.radius < q.radius+1 by linarith).trans_le (le_max_right _ _)) hr
  have hx : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hw⟩
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hr0)
  have hf := q.source_smooth i y hx
  have hp := q.positive_eventually i hx
  have hk := q.symmetric_eventually i hx
  have hσ := (q.patch i).sigma_eventually (y := slice (Real.log (y 0)) (angularProjection y))
    (by simpa only [angularProjection_slice] using hw)
  obtain ⟨hm,h1,h2,h3,h4,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hr0])
  have hu := (hfuture (y 0) (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR
    (by rw [Real.exp_log hr0]) (by rw [Real.exp_log hr0]; linarith)
    (by rwa [hlog]) (by rwa [hlog]) hm h1 h2 h3 h4 hb').2
  have hs : determinant ((q.patch i).fields.base.logFields.sigma
      (slice (Real.log (y 0)) (angularProjection y))) ≠ 0 := by
    exact (determinant_eq _).symm ▸ (q.jetSet_positive _ hm).det_pos.ne'
  have h := sourceExpansion_of_old_future (R := y 0) (by rwa [hlog] :
      (q.patch i).fields.SmoothAt (logRadiusChart (slice (Real.log (y 0)) (angularProjection y))))
    (by rwa [hlog]) hσ (by rwa [hlog]) hs hu.1 hu.2.1 hu.2.2
  rwa [hlog] at h
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma polarLift_congr_point (P : SmoothAngularPatch) (F G : CKSMixedGeometry.Point → AmbientMat)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : F y = G y) : polarLift P F (polarParam P y) = polarLift P G (polarParam P y) := by
  simp only [polarLift,polarInverse_param P hr hy,h]

theorem SourceCollarAtlas.eventually_inner_recovery {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S : ℝ, 1 ≤ S ∧ q.radius < S ∧ ∀ R i x,
      S ≤ ‖x‖ → ‖x‖ ≤ R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
      (q.patch i).metric R x = sourceSpatial A x ∧
      (q.patch i).tensor R x = sourceSpatial B x := by
  obtain ⟨S,hS,hqS,hpos⟩ := q.eventually_sourceExpansion
  refine ⟨S,hS,hqS,?_⟩
  intro R i x hs hx hc
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hyS : S ≤ y 0 := by rwa [hyr]
  have hyR : y 0 ≤ R := by rwa [hyr]
  have hrad : q.radius < y 0 := hqS.trans_le hyS
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hyw⟩
  have hold := source_inner_collar_recovery_closed hy0 hyR
    (q.source_smooth i y hy).base.regularAt (q.positive_eventually i hy)
    (hpos i y hyS hyw) (q.source_symmetric i y hy)
  have hsource := spatial_source_reconstruction (q.patch i) hy0 hyt
    (by rw [hyx]; exact hA x (by rwa [hyr] at hrad))
    (by rw [hyx]; exact hB x (by rwa [hyr] at hrad))
  have hgm : (q.patch i).metric R (polarParam (q.patch i).patch y) = sourceSpatial A (polarParam (q.patch i).patch y) := by
    exact (polarLift_congr_point (q.patch i).patch _ _ hy0 hyt hold.1).trans hsource.2.2.1
  have hkt : (q.patch i).tensor R (polarParam (q.patch i).patch y) = sourceSpatial B (polarParam (q.patch i).patch y) := by
    exact (polarLift_congr_point (q.patch i).patch _ _ hy0 hyt hold.2.1).trans hsource.2.2.2
  rw [hyx] at hgm hkt
  exact ⟨hgm,hkt⟩
end
end CKSLorentz

end

end OAI
