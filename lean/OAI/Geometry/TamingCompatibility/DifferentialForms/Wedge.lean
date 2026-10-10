import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FunSmul
import OAI.Geometry.TamingCompatibility.DifferentialForms.SingleFamily

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

def wedgeOne (a : Form X 1) (b : Form X k) : Form X (k+1) :=
  fun x => ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (a x)) (b x)
def wedgeTwo (a b : Form X 2) : Form X 4 := fun x => ExteriorForms.wedgeTwo (E := Space) (a x) (b x)

omit [IsManifold Model ∞ X] in
lemma pullback_wedgeOne (a : Form X 1) (b : Form X k) (f : Space → X) :
    pullback (wedgeOne a b) f = fun z => ExteriorForms.wedgeOne (ExteriorForms.oneLinear (pullback a f z)) (pullback b f z) := by
  funext z
  change (ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (a (f z))) (b (f z))).compContinuousLinearMap _ = _
  exact (ExteriorForms.wedgeOne_comp (E := Space) (D := Space) _ _ _).trans
    (congrArg (fun L => ExteriorForms.wedgeOne L (pullback b f z))
      (ExteriorForms.oneLinear_comp (E := Space) (D := Space) (a (f z)) _).symm)

omit [IsManifold Model ∞ X] in
lemma Smooth.wedgeOne {a : Form X 1} {b : Form X k} (ha : Smooth a) (hb : Smooth b) :
    Smooth (wedgeOne a b) := by
  intro f U hU hf
  rw [pullback_wedgeOne]
  exact ((ExteriorForms.wedgeOneBilinear (E := Space) (k := k)).contDiff.comp_contDiffOn
    (ha f U hU hf)).clm_apply (hb f U hU hf)

lemma pullback_at_center (a : Form X k) (x : X) :
    pullback a (extChartAt Model x).symm ((extChartAt Model x) x) = a x := by
  have hd : mfderiv Model Model (extChartAt Model x).symm ((extChartAt Model x) x) =
      ContinuousLinearMap.id ℝ Space := by
    have h := mfderivWithin_range_extChartAt_symm (I := Model) (x := x)
    simp only [Model,modelWithCornersSelf_coe,Set.range_id,mfderivWithin_univ] at h
    ext v
    exact congrArg (fun L => L v) h
  ext v
  change (a ((extChartAt Model x).symm ((extChartAt Model x) x)))
    (fun i => mfderiv Model Model (extChartAt Model x).symm ((extChartAt Model x) x) (v i)) = (a x) v
  rw [hd,(extChartAt Model x).left_inv (mem_extChartAt_source x)]
  rfl

lemma exteriorDerivative_wedgeOne {a : Form X 1} {b : Form X 2} (ha : Smooth a) (hb : Smooth b) :
    exteriorDerivative (wedgeOne a b) = wedgeTwo (exteriorDerivative a) b - wedgeOne a (exteriorDerivative b) := by
  funext x
  change extDeriv (pullback (wedgeOne a b) (extChartAt Model x).symm) ((extChartAt Model x) x) = _
  have ha' := (((smooth_chart a ha x) _ (mem_extChartAt_target x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by simp)
  have hb' := (((smooth_chart b hb x) _ (mem_extChartAt_target x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by simp)
  rw [pullback_wedgeOne,ExteriorForms.extDeriv_wedgeOne ha' hb']
  rw [pullback_at_center,pullback_at_center]
  rfl

omit [IsManifold Model ∞ X] in
lemma pullback_wedgeTwo (a b : Form X 2) (f : Space → X) :
    pullback (wedgeTwo a b) f = fun z => ExteriorForms.wedgeTwo (pullback a f z) (pullback b f z) := by
  funext z
  exact ExteriorForms.wedgeTwo_comp (E := Space) (D := Space) (a (f z)) (b (f z)) _

omit [IsManifold Model ∞ X] in
lemma Smooth.wedgeTwo {a b : Form X 2} (ha : Smooth a) (hb : Smooth b) : Smooth (wedgeTwo a b) := by
  intro f U hU hf
  rw [pullback_wedgeTwo]
  exact ((ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis ((ha f U hU hf).add (hb f U hU hf))).sub
    (ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis (ha f U hU hf))).sub
    (ExteriorForms.volumeSquare_contDiffOn ManifoldTop.basis (hb f U hU hf))

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricAdjoint
open Bundle ContinuousAlternatingMap MeasureTheory ManifoldForms ManifoldHodge ManifoldTop ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def pointMetric (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (x : X) :
    MetricModel.Metric Space := tangentMetric J α ht x

def pairing (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {k : ℕ} (a b : ManifoldForms.Form X k) : X → ℝ :=
  fun x => MetricForms.pairing (E := Space) (pointMetric J α ht x) (a x) (b x)

lemma pairing_neg_right (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {k : ℕ} (a b : ManifoldForms.Form X k) (x : X) : pairing J α ht a (-b) x = -pairing J α ht a b x := by
  let g := pointMetric J α ht x
  let a' : MetricForms.Form Space k := a x
  let b' : MetricForms.Form Space k := b x
  change FormMetric.pairing (MetricHodge.formEquiv g k a') (MetricHodge.formEquiv g k (-b')) =
    -FormMetric.pairing (MetricHodge.formEquiv g k a') (MetricHodge.formEquiv g k b')
  rw [_root_.map_neg,← neg_one_smul ℝ (MetricHodge.formEquiv g k b'),
    FormMetric.pairing_smul_right,neg_one_mul]

lemma coefficient_wedgeTwo_star (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a b : ManifoldForms.Form X 2) :
    ManifoldTop.coefficient J α (ManifoldForms.wedgeTwo a (starTwo J α ht b)) = pairing J α ht a b := by
  funext x
  let a' : MetricForms.Form Space 2 := a x
  let b' : MetricForms.Form Space 2 := b x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  have he := MetricWedgePairing.wedgeTwo_star (E := Space) (pointMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)
  change TopForms.coefficient basis (ExteriorForms.volumeSquare F)
    (ExteriorForms.wedgeTwo a' (MetricHodge.starTwo g (J.endomorphism x) F b')) = MetricForms.pairing g a' b'
  exact (congrArg (TopForms.coefficient basis (ExteriorForms.volumeSquare F)) he).trans
    (TopForms.coefficient_smul_left basis (ExteriorForms.volumeSquare F)
      (TopForms.eval_ne_zero basis _ (volumeForm_ne_zero J α ht x)) _)

lemma coefficient_wedgeOne_three (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (a : ManifoldForms.Form X 1) (b : ManifoldForms.Form X 3) :
    ManifoldTop.coefficient J α (ManifoldForms.wedgeOne a b) = fun x => -pairing J α ht a (starThree J α ht b) x := by
  funext x
  let a' : MetricForms.Form Space 1 := a x
  let b' : MetricForms.Form Space 3 := b x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  have he := MetricWedgePairing.wedgeOne_three (E := Space) (pointMetric J α ht x) (J.endomorphism x) (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x)
    (by simp [Space]) (invariantPart J α x)
    (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm) (a x) (b x)
  change TopForms.coefficient basis (ExteriorForms.volumeSquare F)
    (ExteriorForms.wedgeOne (ExteriorForms.oneLinear a') b') = -MetricForms.pairing g a' (MetricHodge.starThree g F b')
  exact (congrArg (TopForms.coefficient basis (ExteriorForms.volumeSquare F)) he).trans
    (TopForms.coefficient_smul_left basis (ExteriorForms.volumeSquare F)
      (TopForms.eval_ne_zero basis _ (volumeForm_ne_zero J α ht x)) _)

lemma codifferential_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {b : TwoForm X} (hb : IsSmooth b) : Smooth (codifferential J α ht b) := by
  have he := (starThree_smooth J α hs ht (Smooth.exteriorDerivative (starTwo_smooth J α hs ht hb))).smul (-1)
  simpa only [codifferential,neg_one_smul] using he

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

theorem formal_adjoint (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {a : ManifoldForms.Form X 1} {b : TwoForm X}
    (ha : Smooth a) (hb : IsSmooth b) :
    (∫ x, pairing J α ht (exteriorDerivative a) b x ∂geometricVolume A J α) =
      ∫ x, pairing J α ht a (codifferential J α ht b) x ∂geometricVolume A J α := by
  let bstar := starTwo J α ht b
  have hbs : Smooth bstar := starTwo_smooth J α hs ht hb
  let γ : smoothForms X 3 := ⟨ManifoldForms.wedgeOne a bstar,ha.wedgeOne hbs⟩
  let η : smoothForms X 4 := ⟨ManifoldForms.wedgeTwo (exteriorDerivative a) bstar,ha.exteriorDerivative.wedgeTwo hbs⟩
  let ζ : smoothForms X 4 := ⟨ManifoldForms.wedgeOne a (exteriorDerivative bstar),ha.wedgeOne hbs.exteriorDerivative⟩
  have hd : d γ = η - ζ := Subtype.ext (exteriorDerivative_wedgeOne ha hbs)
  have hst := ManifoldStokes.stokes A J α hs ht γ
  rw [hd,_root_.map_sub] at hst
  have hη : ManifoldStokes.integral A J α hs ht η =
      ∫ x, pairing J α ht (exteriorDerivative a) b x ∂geometricVolume A J α := by
    change (∫ x, ManifoldTop.coefficient J α (ManifoldForms.wedgeTwo (exteriorDerivative a) (starTwo J α ht b)) x
      ∂geometricVolume A J α) = _
    rw [coefficient_wedgeTwo_star]
  have hζ : ManifoldStokes.integral A J α hs ht ζ =
      ∫ x, pairing J α ht a (codifferential J α ht b) x ∂geometricVolume A J α := by
    change (∫ x, ManifoldTop.coefficient J α (ManifoldForms.wedgeOne a (exteriorDerivative bstar)) x
      ∂geometricVolume A J α) = _
    rw [coefficient_wedgeOne_three]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (pairing_neg_right J α ht a (starThree J α ht (exteriorDerivative bstar)) x).symm
  rw [hη,hζ] at hst
  exact sub_eq_zero.mp hst
end TamingCompatibility.GeometricAdjoint

end

end OAI
