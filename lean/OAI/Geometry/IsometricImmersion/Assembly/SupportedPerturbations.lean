import OAI.Geometry.IsometricImmersion.Coordinates.PatchGeometry
import OAI.Geometry.IsometricImmersion.Metrics.ModelMetric
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Matrix.Normed

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

def patchCompact : Compacts Coord := ⟨patchBox, isCompact_Icc⟩

abbrev SupportedTensor :=
  ContDiffMapSupportedIn Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact

theorem supportedTensor_eval_continuous (p : Coord) (i j : Fin 2) :
    Continuous (fun η : SupportedTensor => η p i j) := by
  have hjet : Continuous (fun η : SupportedTensor =>
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 η p) :=
    (continuous_eval_const p).comp (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous
  have hval : Continuous (fun η : SupportedTensor => η p) := by
    have h := (continuousMultilinearCurryFin0 ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)).continuous.comp hjet
    simp only [Function.comp_def, ContDiffMapSupportedIn.structureMapCLM_zero_apply,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.uncurry0_apply] at h
    exact h
  exact (continuous_apply j).comp ((continuous_apply i).comp hval)

def symmetricSupportedSubmodule : Submodule ℝ SupportedTensor where
  carrier := {η | ∀ p i j, η p i j = η p j i}
  zero_mem' := by
    change ∀ p i j, (0 : SupportedTensor) p i j = (0 : SupportedTensor) p j i
    intros
    rfl
  add_mem' := by
    intro η θ hη hθ p i j
    change η p i j + θ p i j = η p j i + θ p j i
    rw [hη p i j, hθ p i j]
  smul_mem' := by
    intro a η hη p i j
    change a * η p i j = a * η p j i
    rw [hη p i j]

theorem symmetricSupportedSubmodule_isClosed :
    IsClosed (symmetricSupportedSubmodule : Set SupportedTensor) := by
  change IsClosed {η : SupportedTensor | ∀ p i j, η p i j = η p j i}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun p => isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (supportedTensor_eval_continuous p i j) (supportedTensor_eval_continuous p j i))))

abbrev SymmetricPerturbation := symmetricSupportedSubmodule

def perturbationTensor (η : SymmetricPerturbation) : MetricField := η.val

theorem perturbationTensor_symmetric (η : SymmetricPerturbation) (p : Coord) (i j : Fin 2) :
    perturbationTensor η p i j = perturbationTensor η p j i := η.property p i j

theorem perturbationTensor_contDiff (η : SymmetricPerturbation) :
    ContDiff ℝ ∞ (perturbationTensor η) := η.val.contDiff

theorem perturbationTensor_coeff_contDiff (η : SymmetricPerturbation) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => perturbationTensor η p i j) :=
  (contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (perturbationTensor_contDiff η))

theorem perturbationTensor_tsupport_subset (η : SymmetricPerturbation) :
    tsupport (perturbationTensor η) ⊆ patchBox := η.val.tsupport_subset

theorem perturbationTensor_zero_off_patch (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∉ patchBox) : perturbationTensor η p = 0 := η.val.zero_on_compl hp

def perturbationSeminorm (k : ℕ) (η : SymmetricPerturbation) : ℝ :=
  ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k η.val

theorem perturbationSeminorm_continuous (k : ℕ) : Continuous (perturbationSeminorm k) :=
  ((ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)
    ⊤ patchCompact).continuous_seminorm k).comp continuous_subtype_val

theorem perturbation_derivative_norm_le (η : SymmetricPerturbation) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (perturbationTensor η) p‖ ≤ perturbationSeminorm k η :=
  ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ

theorem supportedTensor_iteratedFDeriv_eval_continuous (k : ℕ) :
    Continuous (fun a : SupportedTensor × Coord => iteratedFDeriv ℝ k a.1 a.2) := by
  have h := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k).continuous.comp
    (continuous_fst : Continuous (Prod.fst : SupportedTensor × Coord → SupportedTensor))).eval
      continuous_snd
  simpa only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply] using h

def perturbedMetric (g0 : MetricField) (η : SymmetricPerturbation) : MetricField :=
  g0 + perturbationTensor η

def metricPatchSet (g0 : MetricField) (kappa : ℝ) : Set SymmetricPerturbation :=
  {η | (∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) ∧
    ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2}

theorem perturbedMetric_zero (g0 : MetricField) : perturbedMetric g0 0 = g0 := by
  funext p
  change g0 p + 0 = g0 p
  exact add_zero _

theorem zero_mem_metricPatchSet {g0 : MetricField} {kappa : ℝ}
    (hg : ∀ p ∈ modelSquare, (g0 p).PosDef)
    (hK : ∀ p ∈ centralBox, gaussianCurvature g0 p < -kappa / 2) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet g0 kappa := by
  change (∀ p ∈ modelSquare, (perturbedMetric g0 0 p).PosDef) ∧ _
  rw [perturbedMetric_zero]
  exact ⟨hg, hK⟩

theorem patchBox_subset_modelSquare : patchBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem perturbedMetric_smoothPositiveOn {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) :
    SmoothPositiveOn (perturbedMetric g0 η) U := by
  constructor
  · intro i j
    exact (hg0.1 i j).add (perturbationTensor_coeff_contDiff η i j).contDiffOn
  · intro p hp
    by_cases hP : p ∈ patchBox
    · exact hpos p (patchBox_subset_modelSquare hP)
    · simpa only [perturbedMetric, Pi.add_apply, perturbationTensor_zero_off_patch η hP,
        add_zero] using hg0.2 p hp

theorem constructedModel_zero_mem {kappa : ℝ}
    (hk : 0 < kappa) (hkSmall : kappa ≤ (1 : ℝ) / 31000) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet (constructedModelMetric kappa) kappa := by
  apply zero_mem_metricPatchSet
  · intro p hp
    exact (constructedModelMetric_spec hk hkSmall).1.2 p
      (modelMetricDomain_contains_model_square hp)
  · intro p hp
    exact constructedModelMetric_central_curvature hk hkSmall (fun i => ⟨hp.1 i, hp.2 i⟩)

end SmoothLocal.Perturbation

end

end OAI
