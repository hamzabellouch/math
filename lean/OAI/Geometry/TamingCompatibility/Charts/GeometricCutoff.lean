import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FramePairing
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiEnergy

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_sub_self_le (g : Metric E) {k : ℕ} (a b : Form E k) :
    pairing g (a-b) (a-b) ≤ 2*pairing g a a + 2*pairing g b b := by
  have h := pairing_self_nonneg g (a+b)
  have ha (c : Form E k) : pairing g c (a+b) = pairing g c a + pairing g c b := by
    rw [pairing_symm,pairing_add_left',pairing_symm g a c,pairing_symm g b c]
  rw [pairing_add_left',ha,ha,pairing_symm g b a] at h
  rw [pairing_sub_left,pairing_sub_right,pairing_sub_right,pairing_symm g b a]
  linarith
end TamingCompatibility.MetricForms

namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge GeometricAdjoint
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma antiInvariant_fun_smul (J : AlmostComplexStructure X) {a : TwoForm X}
    (ha : antiInvariantPart J a = a) (f : X → ℝ) :
    antiInvariantPart J (fun x => f x • a x) = fun x => f x • a x := by
  funext x
  ext v
  have h := congrArg (fun b => b x v) ha
  change (1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v) = a x v at h
  change (1/2:ℝ) * (f x * a x v - f x * (a x).compContinuousLinearMap (J.endomorphism x) v) = f x * a x v
  calc
    _ = f x * ((1/2:ℝ) * (a x v - (a x).compContinuousLinearMap (J.endomorphism x) v)) := by ring
    _ = _ := congrArg (f x * ·) h

lemma codifferential_fun_smul_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : Smooth a) (hanti : antiInvariantPart J a = a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    codifferential J α ht (fun x => f x • a x) =
      (fun x => f x • codifferential J α ht a x) -
        starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) := by
  rw [codifferential_anti J α ht (antiInvariant_fun_smul J hanti f),
    exteriorDerivative_fun_smul hf ha,ManifoldHodge.starThree_add]
  funext x
  have he := congrFun (codifferential_anti J α ht hanti) x
  let d : MetricForms.Form Space 3 := exteriorDerivative a x
  let q : MetricForms.Form Space 1 := codifferential J α ht a x
  let s : MetricForms.Form Space 1 := starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  change -(MetricHodge.starThree g F (f x • d) + s) = f x • q - s
  change q = -MetricHodge.starThree g F d at he
  rw [MetricHodge.starThree_smul,he]
  module

lemma pairing_star_wedge_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : antiInvariantPart J a = a) (ξ : ManifoldForms.Form X 1) (x : X) :
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ a))
      (starThree J α ht (ManifoldForms.wedgeOne ξ a)) x =
      (1/2:ℝ) * pairing J α ht ξ ξ x * pairing J α ht a a x := by
  let g := pointMetric J α ht x
  let Jx : Space →L[ℝ] Space := J.endomorphism x
  obtain ⟨b,hb,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis g Jx (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x) (by simp [Space])
  have hanti : (a x).compContinuousLinearMap Jx = -a x := by
    ext v
    have h := congrArg (fun b => b x v) ha
    change (1/2:ℝ) * (a x v - (a x).compContinuousLinearMap Jx v) = a x v at h
    change (a x).compContinuousLinearMap Jx v = -a x v
    linarith
  have he := AntiInvariantFrame.star_wedge_anti g (by simp [Space]) b hb Jx h0 h1 h2 h3
    (invariantPart J α x) (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)
    (ExteriorForms.oneLinear (E := Space) (ξ x)) (a x) hanti
  have hx : ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
      (ExteriorForms.oneLinear (E := Space) (ξ x)) = ξ x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply _
  rw [hx] at he
  exact he

lemma cutoff_delta_pointwise (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : Smooth a) (hanti : antiInvariantPart J a = a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (x : X) :
    pairing J α ht (codifferential J α ht (fun x => f x • a x))
      (codifferential J α ht (fun x => f x • a x)) x ≤
      2*(f x)^2*pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
        pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x := by
  rw [codifferential_fun_smul_anti J α ht ha hanti hf]
  let d : MetricForms.Form Space 1 := codifferential J α ht a x
  let s : MetricForms.Form Space 1 := starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  have hb := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • d) s
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right] at hb
  have he := pairing_star_wedge_anti J α ht hanti (scalarDifferential f) x
  change MetricForms.pairing (pointMetric J α ht x) s s = _ at he
  rw [he] at hb
  convert hb using 1 <;> simp only [GeometricAdjoint.pairing, d] <;> (first | rfl | ring)
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume ContinuousAlternatingMap
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

def localDelta (p : A.centers) (a : TwoForm X) : Space → MetricForms.Form Space 1 := fun x =>
  MetricHodge.starThree (coordinateMetric J α ht p.val x)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm x)
    (extDeriv (localizedFunction A p a) x)

lemma localizedFunction_eq_cutoff (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) : localizedFunction A p a z =
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm z := by
  unfold localizedFunction
  rw [indicator_of_mem hz]
  ext v
  rfl

lemma localDelta_eq (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    localDelta A J α ht p a z = -ManifoldForms.pullback
      (codifferential J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm z := by
  have he : localizedFunction A p a =ᶠ[𝓝 z]
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hz] with y hy
    exact localizedFunction_eq_cutoff A p a hy
  unfold localDelta
  rw [he.extDeriv_eq,pullback_codifferential_antiInvariant J α ht
    (cutoffForm_smooth A p ha) (cutoffForm_anti A J p hanti) p.val hz,neg_neg]
  rfl

lemma cutoffDelta_zero_off (p : A.centers) {a : TwoForm X}
    (hanti : antiInvariantPart J a = a) {x : X} (hx : x ∉ tsupport (A.partition p)) :
    codifferential J α ht (cutoffForm A p a) x = 0 := by
  rw [codifferential_anti J α ht (cutoffForm_anti A J p hanti)]
  let F : MetricForms.Form Space 2 := invariantPart J α x
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F
    (exteriorDerivative (fun y => A.partition p y • a y) x) = 0
  rw [exteriorDerivative_fun_smul_vanishes a hx]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F (0 : MetricForms.Form Space 3) = 0
  rw [MetricHodge.starThree_zero,neg_zero]

variable [CompactSpace X]
lemma localDelta_zero_off (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∉ coordinateSupport A p) : localDelta A J α ht p a z = 0 := by
  have he : localizedFunction A p a =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(coordinateSupport_compact A p).isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact localizedFunction_zero_off A p a hy
  unfold localDelta
  rw [he.extDeriv_eq]
  have hz : extDeriv (fun _ => (0 : MetricForms.Form Space 2)) z = 0 := by
    simp [extDeriv,← alternatizeUncurryFinCLM_apply]
  rw [hz,MetricHodge.starThree_zero]

omit [CompactSpace X] in
lemma cutoffDelta_pairing_tsupport (p : A.centers) {a : TwoForm X}
    (hanti : antiInvariantPart J a = a) :
    tsupport (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a))) ⊆ tsupport (A.partition p) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  apply hx
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (codifferential J α ht (cutoffForm A p a) x) (codifferential J α ht (cutoffForm A p a) x) = 0
  rw [cutoffDelta_zero_off A J α ht p hanti hn]
  exact (MetricForms.pairing_self_eq_zero _ _).mpr rfl

variable (hs : IsSmooth α)
include hs in
lemma localDelta_density_integrable (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) :
    Integrable (coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)))) := by
  apply coordinateIntegrand_integrable J α hs ht p.val
  · have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
    exact (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
  · exact (cutoffDelta_pairing_tsupport A J α ht p hanti).trans (A.subordinate p)

variable [MeasurableSpace X] [BorelSpace X]
include hs in
lemma integral_localDelta_density (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) :
    (∫ z, coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a))) z) =
    ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _
    (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
    ((cutoffDelta_pairing_tsupport A J α ht p hanti).trans (A.subordinate p)),
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
