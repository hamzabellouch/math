import Mathlib
import OAI.Analysis.Conductivity.Variational.L2TranslationAverage
import OAI.Analysis.Conductivity.Geometry.BoxCoordinateBridge
import OAI.Analysis.Conductivity.Flux.CentralDistributionLaplacian

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

def centralEuclideanCLE : R3 ≃L[ℝ] Box3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).trans boxCoordinates

lemma centralEuclidean_volume : MeasurePreserving centralEuclideanCLE :=
  boxCoordinates_volume.comp (PiLp.volume_preserving_ofLp (Fin 3))

lemma centralEuclidean_integral (f : Box3 → ℝ) :
    (∫ x,f (centralEuclideanCLE x))=(∫ x,f x) :=
  centralEuclidean_volume.integral_comp centralEuclideanCLE.toHomeomorph.measurableEmbedding f

lemma centralEuclidean_direction (i : Fin 3) :
    centralEuclideanCLE.symm (centralDirection i)=EuclideanSpace.basisFun (Fin 3) ℝ i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [centralEuclideanCLE,centralDirection,
    boxCoordinates,EuclideanSpace.basisFun_apply] <;> rfl

lemma centralEuclidean_partial {f : R3 → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : Box3) :
    cubePartial (fun y => f (centralEuclideanCLE.symm y)) (centralDirection i) x=
      fderiv ℝ f (centralEuclideanCLE.symm x) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  change (fderiv ℝ (f ∘ centralEuclideanCLE.symm) x) (centralDirection i)=_
  rw [fderiv_comp x (hf _) centralEuclideanCLE.symm.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,centralEuclidean_direction]

lemma centralEuclidean_laplacian {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Box3) :
    centralLaplacian (fun y => f (centralEuclideanCLE.symm y)) x=
      Δ f (centralEuclideanCLE.symm x) := by
  rw [centralLaplacian,laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have hfirst : cubePartial (fun y => f (centralEuclideanCLE.symm y)) (centralDirection i)=
      fun y => fderiv ℝ f (centralEuclideanCLE.symm y) (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
    funext (centralEuclidean_partial (hf.differentiable (by simp)) i)
  have hdf : ContDiff ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hfirst,centralEuclidean_partial ((hdf.differentiable (by simp)).clm_apply (differentiable_const _))]
  rw [iteratedFDeriv_two_apply]
  rw [fderiv_clm_apply (hdf.differentiable (by simp) _) (differentiableAt_const _)]
  simp

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

def centralHarmonicRegion : Set R3 := {x | centralEuclideanCLE x∈centralClosed ∧
  ∀ (i : Fin 3) y,centralEuclideanCLE x≠centralBoundary i y}

def centralZeroExtension (f : CentralL2) : R3 → ℝ :=
  fun x => centralClosed.indicator f (centralEuclideanCLE x)

lemma centralZeroExtension_memLp (f : CentralL2) : MemLp (centralZeroExtension f) 2 volume :=
  ((memLp_indicator_iff_restrict centralClosed_compact.measurableSet).mpr
    (Lp.memLp f)).comp_measurePreserving centralEuclidean_volume

def centralWholeL2 (f : CentralL2) : WholeL2 :=
  (centralZeroExtension_memLp f).toLp (centralZeroExtension f)

lemma centralWholeL2_ae (f : CentralL2) : centralWholeL2 f=ᵐ[volume] centralZeroExtension f :=
  (centralZeroExtension_memLp f).coeFn_toLp

theorem central_variational_euclidean_weak (s slopes : Fin 3 → ℝ)
    (hs : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,centralM s p=0 ∧ CentralVariationalEquation s slopes p ∧
      WeaklyHarmonicOn (centralWholeL2 (centralAmbientComponent s 0 p.val)) centralHarmonicRegion := by
  obtain ⟨p,hp,hvar,hweak⟩ := central_variational_distributional_laplacian s slopes hs
  refine ⟨p,hp,hvar,?_⟩
  intro ψ hψ hc hsp
  let φ : centralSmoothFunctions := ⟨fun x => ψ (centralEuclideanCLE.symm x),
    hψ.comp centralEuclideanCLE.symm.contDiff⟩
  have hφc : HasCompactSupport φ := hc.comp_homeomorph centralEuclideanCLE.symm.toHomeomorph
  have hφs : tsupport φ⊆centralClosed := by
    intro x hx
    have hpre := tsupport_comp_subset_preimage ψ centralEuclideanCLE.symm.continuous hx
    have hmem := (hsp hpre).1
    simpa only [centralEuclideanCLE.apply_symm_apply] using hmem
  have hφb (i : Fin 3) x : φ (centralBoundary i x)=0 := by
    by_contra hz
    have hmem : centralEuclideanCLE.symm (centralBoundary i x)∈tsupport ψ :=
      subset_tsupport ψ hz
    have he := (hsp hmem).2 i x
    exact he (centralEuclideanCLE.apply_symm_apply _)
  have hz := hweak φ hφc hφs hφb
  let f := centralAmbientComponent s 0 p.val
  calc
    (∫ x,centralWholeL2 f x*Δ ψ x)=∫ x,centralZeroExtension f x*Δ ψ x := by
      apply integral_congr_ae
      filter_upwards [centralWholeL2_ae f] with x hx
      rw [hx]
    _ = ∫ x,centralClosed.indicator f (centralEuclideanCLE x)*centralLaplacian φ (centralEuclideanCLE x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have he := centralEuclidean_laplacian hψ (centralEuclideanCLE x)
      simpa only [centralEuclideanCLE.symm_apply_apply,centralZeroExtension] using
        congrArg (fun t => centralClosed.indicator f (centralEuclideanCLE x)*t) he.symm
    _ = ∫ x,centralClosed.indicator f x*centralLaplacian φ x := centralEuclidean_integral (fun x => centralClosed.indicator f x*centralLaplacian φ x)
    _ = ∫ x,f x*centralLaplacian φ x ∂centralMeasure := by
      change _=∫ x in centralClosed,f x*centralLaplacian φ x
      rw [←integral_indicator centralClosed_compact.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈centralClosed <;> simp [hx]
    _ = 0 := hz

end ScalarConductivity

end
end

end OAI
