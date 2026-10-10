import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Space
import OAI.Geometry.TamingCompatibility.Elliptic.BilinearCoercivePos

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped Manifold ContDiff
noncomputable section
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
noncomputable section
open scoped Manifold ContDiff Topology
open Bundle Filter Set
noncomputable section
open Set
namespace TamingCompatibility
open Bundle Set
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def metricCoords (J : AlmostComplexStructure X) (α : TwoForm X) (x y : X) :
    Space →L[ℝ] Space →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates Space (TangentSpace Model)
    (Space →L[ℝ] ℝ) (fun z => TangentSpace Model z →L[ℝ] ℝ)
    x y x y (associatedBilinear J α y)

lemma metricCoords_chart_apply (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) {z : Space} (hz : z ∈ (extChartAt Model x).target) (u v : Space) :
    metricCoords J α x ((extChartAt Model x).symm z) u v =
      ManifoldForms.pullback α (extChartAt Model x).symm z
        ![u, SmoothAlmostComplex.coord
          (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X)
          (trivializationAt Space (TangentSpace Model) x)
          ((extChartAt Model x).symm z) v] := by
  let e := extChartAt Model x
  let te := trivializationAt Space (TangentSpace Model) x
  have hs : e.symm z ∈ (chartAt Space x).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  have hd : mfderiv Model Model e.symm z = te.symmL ℝ (e.symm z) := by
    rw [TangentBundle.symmL_trivializationAt hs]
    change mfderiv Model Model e.symm z =
      mfderivWithin Model Model e.symm (Set.range Model) (e (e.symm z))
    rw [e.right_inv hz]
    simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]
  unfold metricCoords
  rw [inCoordinates_apply_eq₂ ht ht (Set.mem_univ _)]
  rw [associatedBilinear_apply]
  change (Bundle.Trivial.trivialization X ℝ).linearMapAt ℝ (e.symm z) _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
  change (α (e.symm z)) ![te.symm (e.symm z) u,
    J.endomorphism (e.symm z) (te.symm (e.symm z) v)] = _
  change _ = (α (e.symm z)) (fun i => mfderiv Model Model e.symm z
    (![u, te.continuousLinearMapAt ℝ (e.symm z) (J.endomorphism (e.symm z)
      (te.symmL ℝ (e.symm z) v))] i))
  rw [hd]
  apply congrArg (α (e.symm z))
  ext i
  fin_cases i
  · change te.symm (e.symm z) u = te.symmL ℝ (e.symm z) u
    exact (te.symmL_apply ht u).symm
  · change J.endomorphism (e.symm z) (te.symm (e.symm z) v) =
      te.symmL ℝ (e.symm z) (te.continuousLinearMapAt ℝ (e.symm z)
        (J.endomorphism (e.symm z) (te.symmL ℝ (e.symm z) v)))
    rw [te.symmL_continuousLinearMapAt ht, te.symmL_apply ht]

lemma IsSmooth.metricCoords {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) (x : X) :
    ContDiffOn ℝ ∞ (fun z => metricCoords J α x ((extChartAt Model x).symm z))
      (extChartAt Model x).target := by
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v
  have ha := ManifoldForms.smooth_chart α hα x
  have hJ := SmoothAlmostComplex.contDiffOn_coord_chart
    (⟨J.endomorphism, J.square, J.smooth⟩ : SmoothAlmostComplex.AlmostComplexStructure X) x
  have hC : ContDiff ℝ ∞ (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
      (E := Space) (F := ℝ) (n := 1)).toContinuousLinearMap := by
    exact ContinuousLinearMap.contDiff _
  have hc := hC.comp_contDiffOn ha
  have hcu := hc.clm_apply (contDiffOn_const (c := u))
  have hf := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space)
    (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hcu
  apply (hf.clm_apply (hJ.clm_apply (contDiffOn_const (c := v)))).congr
  intro z hz
  rw [metricCoords_chart_apply J α x hz]
  change (ManifoldForms.pullback α (extChartAt Model x).symm z) ![u, _] =
    (ManifoldForms.pullback α (extChartAt Model x).symm z) (Matrix.vecCons u (fun _ : Fin 1 => _))
  congr 1
  ext i
  fin_cases i <;> rfl

theorem IsSmooth.associatedBilinear {α : TwoForm X} (hα : IsSmooth α)
    (J : AlmostComplexStructure X) :
    ContMDiff Model (Model.prod 𝓘(ℝ, Space →L[ℝ] Space →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (Space →L[ℝ] Space →L[ℝ] ℝ) x (associatedBilinear J α x)) := by
  intro x
  rw [contMDiffAt_section, contMDiffAt_iff_source]
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt, Function.comp_def, hom_trivializationAt_apply]
  exact (hα.metricCoords J x).contDiffAt (extChartAt_target_mem_nhds x)

def hermitianMetric (J : AlmostComplexStructure X) (α : TwoForm X)
    (hα : IsSmooth α) (ht : Tames α J) :
    ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type) := by
  letI (x : X) : NormedAddCommGroup (TangentSpace Model x) :=
    inferInstanceAs (NormedAddCommGroup Space)
  letI (x : X) : NormedSpace ℝ (TangentSpace Model x) :=
    inferInstanceAs (NormedSpace ℝ Space)
  letI (x : X) : FiniteDimensional ℝ (TangentSpace Model x) :=
    inferInstanceAs (FiniteDimensional ℝ Space)
  letI (x : X) : Nontrivial (TangentSpace Model x) :=
    inferInstanceAs (Nontrivial Space)
  exact {
    inner := fun x => associatedBilinear J (invariantPart J α) x
    symm := (invariantPart_isInvariant J α).associatedBilinear_symm
    pos := (tames_invariantPart ht).associatedBilinear_pos
    isVonNBounded := fun x => bilinear_unitBall_isVonNBounded _
      ((tames_invariantPart ht).associatedBilinear_pos x)
    contMDiff := (hα.invariantPart J).associatedBilinear J }

end TamingCompatibility

noncomputable section
open Bundle Set Filter
open scoped Topology

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
