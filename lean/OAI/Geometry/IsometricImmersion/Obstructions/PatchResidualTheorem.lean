import OAI.Geometry.IsometricImmersion.Obstructions.BoundedClassNowhereDense
import OAI.Geometry.IsometricImmersion.Obstructions.PatchObstructionSet
import OAI.Geometry.IsometricImmersion.Metrics.MetricPatchOpen

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem patchObstructionSet_dense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    Dense (patchObstructionSet g0 kappa) := by
  let : BaireSpace (metricPatchSet g0 kappa) := metricPatchSet_baire hg0 hV hSV kappa
  change Dense (⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ)
  apply dense_iInter_of_isOpen (fun _ => isClosed_closure.isOpen_compl)
  intro index
  exact (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure,
    (boundedHeightClass_isNowhereDense hg0 hV hSV hkappa hbackground index.1 index.2).closure⟩).2

theorem no_admissible_height_residual
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    {eta : metricPatchSet g0 kappa |
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z} ∈
        residual (metricPatchSet g0 kappa) := by
  let : BaireSpace (metricPatchSet g0 kappa) := metricPatchSet_baire hg0 hV hSV kappa
  apply mem_residual.mpr
  refine ⟨patchObstructionSet g0 kappa,?_,patchObstructionSet_isGdelta g0 kappa,
    patchObstructionSet_dense hg0 hV hSV hkappa hbackground⟩
  intro eta heta
  exact patchObstructionSet_has_no_admissible_height heta

theorem exists_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ eta ∈ O,
      SmoothPositiveOn (perturbedMetric g0 eta.val) V ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa/2) ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  obtain ⟨eta,hetaGood,hetaO⟩ :=
    (patchObstructionSet_dense hg0 hV hSV hkappa hbackground).exists_mem_open hO hne
  exact ⟨eta,hetaO,perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2,patchObstructionSet_has_no_admissible_height hetaGood⟩

theorem exists_patch_obstruction_in_neighborhood
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {etaCenter : metricPatchSet g0 kappa} {O : Set (metricPatchSet g0 kappa)}
    (hO : O ∈ 𝓝 etaCenter) :
    ∃ eta ∈ O, ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  obtain ⟨W,hWO,hW,hcenter⟩ := mem_nhds_iff.mp hO
  obtain ⟨eta,hetaW,_,_,hno⟩ :=
    exists_patch_obstruction_in_open hg0 hV hSV hkappa hbackground hW ⟨etaCenter,hcenter⟩
  exact ⟨eta,hWO hetaW,hno⟩

end SmoothLocal.Perturbation

end

end OAI
