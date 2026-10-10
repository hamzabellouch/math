import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import OAI.Geometry.IsometricImmersion.Curvature.MetricCurvatureJet

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def metricCoefficientCLM (i j : Fin 2) : MetricMatrix →L[ℝ] ℝ where
  toFun A := A i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := (continuous_apply j).comp (continuous_apply i)

theorem supportedTensor_coeff_iteratedFDeriv (η : SupportedTensor) (k : ℕ)
    (p : Coord) (v : Fin k → Coord) (i j : Fin 2) :
    iteratedFDeriv ℝ k (fun q => η q i j) p v = (iteratedFDeriv ℝ k η p v) i j := by
  change iteratedFDeriv ℝ k (metricCoefficientCLM i j ∘ η) p v =
    metricCoefficientCLM i j (iteratedFDeriv ℝ k η p v)
  have he := (metricCoefficientCLM i j).iteratedFDeriv_comp_left (x := p) (i := k)
    η.contDiff.contDiffAt (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k))
  exact congrArg (fun L : Coord [×k]→L[ℝ] ℝ => L v) he

theorem supportedTensor_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d i j : Fin 2) :
    coordPartial d (fun q => η q i j) p =
      (iteratedFDeriv ℝ 1 η p (fun _ => Pi.single d 1)) i j := by
  rw [← supportedTensor_coeff_iteratedFDeriv]
  simp only [iteratedFDeriv_one_apply, coordPartial]

theorem supportedTensor_second_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => η q i j)) p =
      (iteratedFDeriv ℝ 2 η p ![Pi.single d 1, Pi.single e 1]) i j := by
  have hs : ContDiff ℝ ∞ (fun q => η q i j) :=
    (metricCoefficientCLM i j).contDiff.comp η.contDiff
  rw [← supportedTensor_coeff_iteratedFDeriv, iteratedFDeriv_two_apply,
    second_coordPartial_eq_fderiv hs.contDiffOn isOpen_univ (mem_univ p)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem supportedTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord => a.1 a.2 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_eval)

theorem supportedTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (fun q => a.1 q i j) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 1).eval
    (continuous_const (y := ((fun _ : Fin 1 => Pi.single d (1 : ℝ)) : Fin 1 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_coordPartial_eq_jet]
  exact he

theorem supportedTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (coordPartial e (fun q => a.1 q i j)) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 2).eval
    (continuous_const (y := (![Pi.single d 1, Pi.single e 1] : Fin 2 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_second_coordPartial_eq_jet]
  exact he

theorem perturbationTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord => perturbationTensor a.1 a.2 i j) :=
  (supportedTensor_coeff_eval_joint_continuous i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbationTensor a.1 q i j) a.2) :=
  (supportedTensor_coordPartial_joint_continuous d i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbationTensor a.1 q i j)) a.2) :=
  (supportedTensor_second_coordPartial_joint_continuous d e i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbedMetric_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => perturbedMetric g0 η q i j) p =
      coordPartial d (fun q => g0 q i j) p +
        coordPartial d (fun q => perturbationTensor η q i j) p := by
  apply HessianCalculus.coordPartial_add_at
  · exact (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  · exact (perturbationTensor_coeff_contDiff η i j).differentiable (by simp) p

theorem perturbedMetric_second_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p =
      coordPartial d (coordPartial e (fun q => g0 q i j)) p +
        coordPartial d (coordPartial e (fun q => perturbationTensor η q i j)) p := by
  have heq : coordPartial e (fun q => perturbedMetric g0 η q i j) =ᶠ[𝓝 p]
      (fun q => coordPartial e (fun q => g0 q i j) q +
        coordPartial e (fun q => perturbationTensor η q i j) q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact perturbedMetric_coordPartial hg0 hU η hq e i j
  change fderiv ℝ _ p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  apply HessianCalculus.coordPartial_add_at
  · exact (((partial_contDiffOn (hg0.1 i j) hU e) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  · exact (((partial_contDiffOn (perturbationTensor_coeff_contDiff η i j).contDiffOn
      isOpen_univ e) p (mem_univ p)).contDiffAt (by simp)).differentiableAt (by simp)

section JointMetric
variable {g0 : MetricField} {U : Set Coord}
variable (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
variable {η : SymmetricPerturbation} {p : Coord} (hp : p ∈ U)
include hg0 hU hp

theorem perturbedMetric_coeff_joint_continuousAt (i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j)
      (η, p) := by
  have hbg := (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  exact (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coeff_eval_joint_continuous i j).continuousAt

theorem perturbedMetric_coordPartial_joint_continuousAt (d i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbedMetric g0 a.1 q i j) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (hg0.1 i j) hU d) p hp).contDiffAt
    (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coordPartial_joint_continuous d i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_coordPartial hg0 hU a.1 ha d i j

theorem perturbedMetric_second_coordPartial_joint_continuousAt (d e i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbedMetric g0 a.1 q i j)) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (partial_contDiffOn (hg0.1 i j) hU e) hU d)
    p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_second_coordPartial_joint_continuous d e i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_second_coordPartial hg0 hU a.1 ha d e i j

end JointMetric

def perturbedCurvatureJet (g0 : MetricField) (η : SymmetricPerturbation) (p : Coord) : ℝ :=
  curvatureJet (perturbedMetric g0 η p)
    (fun d i j => coordPartial d (fun q => perturbedMetric g0 η q i j) p)
    (fun d e i j => coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p)

theorem perturbedCurvatureJet_joint_continuousAt {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) {η : SymmetricPerturbation}
    {p : Coord} (hp : p ∈ U) (hdet : (perturbedMetric g0 η p).det ≠ 0) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedCurvatureJet g0 a.1 a.2)
      (η, p) :=
  curvatureJet_continuousAt (perturbedMetric_coeff_joint_continuousAt hg0 hU hp)
    (perturbedMetric_coordPartial_joint_continuousAt hg0 hU hp)
    (perturbedMetric_second_coordPartial_joint_continuousAt hg0 hU hp) hdet

theorem gaussianCurvature_perturbedMetric_eq_jet {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (perturbedMetric g0 η) p = perturbedCurvatureJet g0 η p :=
  gaussianCurvature_eq_curvatureJet (perturbedMetric_smoothPositiveOn hg0 η hpos) hU hp

end SmoothLocal.Perturbation

end

end OAI
