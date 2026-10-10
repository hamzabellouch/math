import OAI.Geometry.SurfaceImmersion.Atlas.PhaseCovectorRead
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseDependence
import OAI.Geometry.SurfaceImmersion.Geometry.CompactParameterC1

namespace OAI

/-! Compact parameter bounds for the actual circular phase differentials,
including their first spatial derivatives. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def phaseCovectorRead (i : B.centers) (phi : M → ℝ) (y : JetPolynomial.Base) : Plane →L[ℝ] ℝ :=
  (fderiv ℝ (phi ∘ (chart (i : M)).symm) y).comp
    (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap

omit [CompactSpace M] [T2Space M] in
lemma phaseCovectorRead_smoothOn (i : B.centers) (phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ContDiffOn ℝ ∞ (B.phaseCovectorRead i phi) (chart (i : M)).target := by
  have h := (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  exact (h.fderiv_of_isOpen (chart (i : M)).open_target (m := ∞) (by simp)).clm_comp contDiffOn_const

def circularCovectorJoint (i j : B.centers) (L : ℝ) (z : Base × JetPolynomial.Base) : Plane →L[ℝ] ℝ :=
  B.phaseCovectorRead j (B.circularPhase i 0 L) z.2+
    z.1.1 • B.phaseCovectorRead j (B.circularPhase i (1,0) 0) z.2+
    z.1.2 • B.phaseCovectorRead j (B.circularPhase i (0,1) 0) z.2

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_smoothOn (i j : B.centers) (L : ℝ) :
    ContDiffOn ℝ ∞ (B.circularCovectorJoint i j L)
      (univ ×ˢ (chart (j : M)).target) := by
  have h0 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i 0 L)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h1 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (1,0) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h2 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (0,1) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have he1 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.1) := contDiff_fst.fst
  have he2 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.2) := contDiff_fst.snd
  exact (h0.add (he1.contDiffOn.smul h1)).add (he2.contDiffOn.smul h2)

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_eq (i j : B.centers) (ell : Base) (L : ℝ)
    {y : JetPolynomial.Base} (hy : y ∈ (chart (j : M)).target) :
    B.phaseCovectorRead j (B.circularPhase i ell L) y = B.circularCovectorJoint i j L (ell,y) := by
  let p := (chart (j : M)).symm y
  have hp : p ∈ (chart (j : M)).source := (chart (j : M)).map_target hy
  have hpy : chart (j : M) p = y := (chart (j : M)).right_inv hy
  have h := B.circularPhase_mfderiv_sub i ell 0 L p
  have hh := congrArg (fun v : Plane →L[ℝ] ℝ => B.covectorFrame j p v) h
  unfold covectorFrame at hh
  erw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp] at hh
  change B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i 0 L) p) =
    (ell.1-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
    (ell.2-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) at hh
  rw [B.covectorFrame_mfderiv _ (B.circularPhase_smooth i ell L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i 0 L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (1,0) 0) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (0,1) 0) j hp,hpy] at hh
  change B.phaseCovectorRead j (B.circularPhase i ell L) y-
      B.phaseCovectorRead j (B.circularPhase i 0 L) y =
    (ell.1-0) • B.phaseCovectorRead j (B.circularPhase i (1,0) 0) y+
    (ell.2-0) • B.phaseCovectorRead j (B.circularPhase i (0,1) 0) y at hh
  simp only [sub_zero] at hh
  have hh' := congrArg (fun v => v+B.phaseCovectorRead j (B.circularPhase i 0 L) y) hh
  rw [sub_add_cancel] at hh'
  rw [hh']
  unfold circularCovectorJoint
  abel

omit [T2Space M] in
theorem circular_covector_parameter_bound (i j : B.centers) (L : ℝ)
    {P : Set Base} (hP : IsCompact P) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ell ∈ P, ∀ y ∈ (B.chartWeightCompact j : Set JetPolynomial.Base),
      ‖B.phaseCovectorRead j (B.circularPhase i ell L) y‖ ≤ D ∧
      ‖fderiv ℝ (B.phaseCovectorRead j (B.circularPhase i ell L)) y‖ ≤ D := by
  have hK := (B.chartWeightCompact j).isCompact
  have hsub : (B.chartWeightCompact j : Set JetPolynomial.Base) ⊆ (chart (j : M)).target := by
    rintro y ⟨p,hp,rfl⟩
    exact (chart (j : M)).map_source (B.weight_support j hp)
  have hj := B.circularCovectorJoint_smoothOn i j L
  obtain ⟨D,hD,hbound⟩ := compact_parameter_C1 hP hK
    (fun z hz => hj.contDiffAt ((isOpen_univ.prod (chart (j : M)).open_target).mem_nhds
      ⟨mem_univ _,hsub hz.2⟩))
  refine ⟨D,hD,?_⟩
  intro ell hell y hy
  have he : B.phaseCovectorRead j (B.circularPhase i ell L) =ᶠ[𝓝 y]
      (fun x => B.circularCovectorJoint i j L (ell,x)) := by
    filter_upwards [(chart (j : M)).open_target.mem_nhds (hsub hy)] with x hx
    exact B.circularCovectorJoint_eq i j ell L hx
  rw [he.self_of_nhds,he.fderiv_eq]
  exact hbound ell hell y hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
