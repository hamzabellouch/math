import OAI.Geometry.SurfaceImmersion.Geometry.UniformCorrectedTermC1
import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceBoundaryStartingFamily
import OAI.Geometry.SurfaceImmersion.Geometry.UniformScaledPathBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CycleCorrectedGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularRealization
import OAI.Geometry.SurfaceImmersion.Whitney.WhitneyStartingGeometry

namespace OAI

/-! Smooth isometric immersions constructed from spherical immersions,
and from the compact surface case of Whitney (1944), Theorem 8, p.274. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]
local instance mainFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance mainFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance mainDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance mainDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance mainSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance mainSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

omit [SecondCountableTopology M] in
/-- The construction starting from a smooth unit spherical immersion. All
primitive amplitudes and the starting scale are chosen uniformly before
selecting the finite crossings. -/
theorem isometric_immersion_of_spherical_immersion (g : SmoothMetric M)
    {I : M → Space} (hI : ContMDiff planeModel spaceModel ∞ I)
    (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M g W := by
  classical
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨r,D,c,hr,hr1,hD,hc,_hIb,_hIm,hIs,hstart⟩ :=
    A.reference_circular_starting_family g hI hunit hImm zero_lt_one
  let gref := A.shortRemainderMetric g (space_smul_contMDiff hI r) hIs
  have href : gref.inner = g.inner-inducedTensor (r • I) := rfl
  obtain ⟨C,hC,hpath⟩ := A.uniform_scaled_path_bound g r hD
  obtain ⟨d⟩ := A.exists_reference_circular_atlas gref g hc (show 0 ≤ C+1 by linarith)
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hterm⟩ := d.uniform_corrected_term_C1 hI r href hD
  let m := Fintype.card (d.B.centers × Fin 3)
  let e : Fin m ≃ (d.B.centers × Fin 3) := (Fintype.equivFin _).symm
  obtain ⟨mapTol,delta,W,hmapTol,hmapLe,_hdelta,_hdeltaR,hW,hcycles⟩ :=
    d.corrected_cycles hI r href hpt hwt hmt e
  obtain ⟨E,hE,hterms⟩ := hterm (W 1) (hW 1)
  obtain ⟨N,hN,hrealize⟩ := A.independent_circular_realization g c C d.B
    d.radius d.L (fun i => ‖(d.P i).ξ‖+1) d.L_pos d.region
    d.weight_nonneg d.weight_positive d.convex m E hE
  obtain ⟨q,hindex,houter,_hchart,hpart,hell,hphase,hweights,hweightClose,hcorrect⟩ :=
    hcycles N hN
  obtain ⟨G,g₀,normal,hG,_hu,hG₀,hg₀,⟨good⟩,_hn,hnear,hGb,hlower,_hgm,hshort,hgeom⟩ :=
    hstart (N*m) d.B q mapTol hmapTol
  obtain ⟨f,dCirc,hamp,hphi,hcurves,_hrad,_houter',_hchart',hlinear,hconvex,hcycle,hcyclePhase,_htotal⟩ :=
    hcorrect G hG hnear
  have hnear' : A.WeightedBound 1 1 mt (G-I) :=
    fun i => (hnear i).mono_const hmapLe
  have hcopy (k : Fin N) (b : d.B.centers × Fin 3) :
      (finProdFinEquiv (k,e.symm b)).divNat = k ∧
        e (finProdFinEquiv (k,e.symm b)).modNat = b := by
    have hh := Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,e.symm b))
    exact ⟨hh.1,by rw [hh.2,e.apply_symm_apply]⟩
  have hell' (k : Fin N) (i : d.B.centers) (j : Fin 3) :
      ‖d.cycleLinearParts e q k i j-(d.P i).ξ j‖ < pt := by
    have h := hphase (finProdFinEquiv (k,e.symm (i,j)))
    simpa only [ReferenceCircularAtlas.cycleLinearParts,
      (hcopy k (i,j)).2] using h
  have htermBound (k : Fin N) (a : Fin m) :
      A.TensorWeightedBound 1 1 E ((f k).term a) := by
    let f' := (f k).reindex e.symm
    have hp' : f'.phase = d.perturbedPhases (d.cycleLinearParts e q k) := by
      funext b
      exact (hphi k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have ha' : f'.amplitude = d.B.correctedPrimitiveAmplitude d.basis
        (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
        (g.inner-inducedTensor (r • G)) := by
      funext b
      exact (hamp k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have hnon (b : d.B.centers × Fin 3) :
        ContMDiff planeModel 𝓘(ℝ) ∞ (d.cycleWeights e q k b) := by
      let a : Fin (N*m) := finProdFinEquiv (k,e.symm b)
      have hh : e a.modNat = b := (hcopy k b).2
      have hrsmall : (q.radius a)^2 < (d.radius b.1)^2 := by
        have hrpos := q.radius_pos a
        have hro := q.radius_outer a
        rw [houter a,hh] at hro
        nlinarith [d.radius_pos b.1]
      exact (shrinkingCircularWeight_smooth (b.1 : M) (d.B.weight b.1)
        (d.B.weight_smooth b.1) (d.region b.1) hrsmall).1
    have hsupp (b : d.B.centers × Fin 3) :
        tsupport (d.cycleWeights e q k b) ⊆ tsupport (d.B.weight b.1) := by
      apply closure_mono
      intro p hp
      change d.cycleWeights e q k b p ≠ 0 at hp
      change d.B.weight b.1 p ≠ 0
      intro hz
      exact hp (by simp only [ReferenceCircularAtlas.cycleWeights,shrinkingCircularWeight,hz,zero_mul])
    have hb := hterms (d.cycleLinearParts e q k) (d.cycleWeights e q k) (hell' k)
      hnon hsupp (hweightClose k) (fun b => hweights k b 1) G hG hnear' hGb f' hp' ha' (e a)
    change A.TensorWeightedBound 1 1 E ((f k).term (e.symm (e a))) at hb
    simpa only [e.symm_apply_apply] using hb
  have hshort' : ∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
    intro p v
    change inducedTensor (r • G) p v v ≤ _
    rw [← hg₀]
    exact hshort p v
  have hpBound (k : Fin N) : A.TensorWeightedBound 1 1 C
      (g₀.inner+((k.val : ℝ)/(N : ℝ)) • (g.inner-inducedTensor (r • G))) := by
    rw [hg₀]
    exact hpath G hG hGb (hG₀.mfderiv_injective) hshort' _
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ((div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast k.isLt.le))
  have hcv (a : Fin (N*m)) : dCirc.convexPart a = d.L (dCirc.curves a).index := by
    rw [hconvex,hpart,hcurves,hindex]
  have hlin (a : Fin (N*m)) : ‖dCirc.linearPart a‖ ≤ ‖(d.P (dCirc.curves a).index).ξ‖+1 := by
    rw [hlinear,hcurves,hindex]
    exact hell a
  have htarget : g.inner = g₀.inner+(g.inner-inducedTensor (r • G)) := by
    rw [hg₀]
    abel
  have hgeom' : FiniteBoundaryGeometry dCirc.curves
      (boundaryCrossingSet dCirc.curves univ) (r • G) normal := by
    rw [hcurves]
    exact hgeom
  obtain ⟨F,hF,_hgood⟩ := hrealize g₀ hlower _ f htermBound hpBound dCirc
    hcycle hcyclePhase hcv hlin g htarget (r • G) normal hG₀ good hgeom'
  exact ⟨F,hF⟩

/-- Main theorem of paper 094-01. The sole published hypothesis is Whitney
(1944), Theorem 8, p.274, specialized to a closed smooth surface. -/
theorem smooth_isometric_immersion_conditional (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F := by
  obtain ⟨I,hI,hunit,hImm,_⟩ := metricPhaseData_of_whitney g hW
  exact isometric_immersion_of_spherical_immersion g hI hunit hImm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
