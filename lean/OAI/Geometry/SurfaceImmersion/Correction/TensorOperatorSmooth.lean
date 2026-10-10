import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveOperator
import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothingSymmetry
import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCorrectionLimit
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

namespace OAI

/-! Smoothness of the actual finite primitive operator, derived from its
supported coefficients and the smooth phase differentials. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance operatorSmoothFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance operatorSmoothFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance operatorSmoothFiberComplete : CompleteSpace TensorFiber := inferInstance
private lemma completedPrimitiveOperator_rankOne {ι : Type*} [Fintype ι]
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      (∑ a, ((psi a)^2 * q a (tensorSymmetrizer B)) • (xi a).smulRight (xi a)) +
        (B - tensorSymmetrizer B) := by
  rw [completedPrimitiveOperator_apply,finitePrimitiveOperator_apply]
  abel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance operatorSmoothDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance operatorSmoothDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance operatorSmoothSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance operatorSmoothSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance operatorSmoothSectionGroup (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (operatorSmoothSectionNormed p).toAddCommGroup

omit [CompactSpace M] [IsManifold planeModel ∞ M] in
private lemma smooth_clm_of_evaluation {F : M → TensorFiber →L[ℝ] TensorFiber} {p : M}
    (h : ∀ v, ContMDiffAt planeModel 𝓘(ℝ,TensorFiber) ∞ (fun x => F x v) p) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber) ∞ F p := by
  let d := Module.finrank ℝ TensorFiber
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : TensorFiber ≃L[ℝ] TensorFiber)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp F, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.contMDiffAt.comp p
    (contMDiffAt_pi_space.mpr fun i => h _)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Testing a field on smooth sections suffices for smoothness of the
endomorphism field. The atlas cutoffs provide the local constant frames. -/
theorem tensorOperator_smooth_of_apply
    (L : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hL : ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (L p (u p)))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (L p)) := by
  intro p
  obtain ⟨i,hi⟩ := A.exists_weight_ne_zero p
  have hp := subset_tsupport _ hi
  have hpS := A.weight_support i hp
  let e := A.tensorTriv i
  let eL := e.continuousLinearMap (RingHom.id ℝ) e
  have he : p ∈ e.baseSet := A.tensorTriv_domain i hpS
  apply (eL.contMDiffAt_section_iff (show p ∈ eL.baseSet from ⟨he,he⟩)).mpr
  apply smooth_clm_of_evaluation
  intro v
  let u := A.bundleRestore A.tensorTriv i (fun _ => v)
  have hu := A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (contDiff_const : ContDiff ℝ ∞ (fun _ : JetPolynomial.Base => v))
  have hLu := (A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain i (hL u hu)
    p hpS).contMDiffAt ((chart (i : M)).open_source.mem_nhds hpS)
  apply hLu.congr_of_eventuallyEq
  filter_upwards [houter i p hp, (chart (i : M)).open_source.mem_nhds hpS] with x hx hxS
  simp only [eL, Trivialization.continuousLinearMap_apply]
  change e.continuousLinearMapAt ℝ x (L x (e.symmL ℝ x v)) =
    e.continuousLinearMapAt ℝ x (L x (u x))
  congr 2
  change e.symmL ℝ x v = A.outer i x • e.symmL ℝ x v
  rw [hx,one_smul]

include A in
/-- Transposition and symmetrization are smooth operations on genuine tensor
sections, with no symmetry assumption on the input. -/
lemma tensorSymmetrizer_smooth (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (show CovariantTwoTensor p from tensorSymmetrizer (u p))) := by
  have ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (tensorTranspose (u p))) := by
    have henc := A.tensorEncode_smooth hu
    have hflip : ContDiff ℝ ∞ (fun y => A.tensorEncode (fun p => tensorTranspose (u p)) y) := by
      apply contDiff_pi.mpr
      intro i
      have h := (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearMap.contDiff.comp
        (contDiff_pi.mp henc i)
      simpa only [tensorEncode,A.tensorLocalize_flip,Function.comp_def] using! h
    simpa only [A.tensorDecode_encode] using A.tensorDecode_smooth hflip
  change ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
    (fun p => TotalSpace.mk' TensorFiber p ((1 / 2 : ℝ) • (u p + tensorTranspose (u p))))
  exact (hu.add_section ht).const_smul_section (a := (1 / 2 : ℝ))

def phaseDifferentialSquare (phi : M → ℝ) (p : M) : CovariantTwoTensor p :=
  (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) phi p).smulRight
    (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) phi p)

include A in
/-- The square of a smooth scalar differential is a smooth covariant tensor. -/
lemma phaseDifferentialSquare_smooth (phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (phaseDifferentialSquare phi p)) := by
  let v : Space := EuclideanSpace.single 0 1
  let e : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have he : ContMDiff 𝓘(ℝ) spaceModel ∞ e := e.contDiff.contMDiff
  have hF := he.comp hphi
  have hEq : inducedTensor (e ∘ phi) =
      fun p => phaseDifferentialSquare phi p := by
    funext p
    ext a b
    change inner ℝ (mfderiv planeModel spaceModel (e ∘ phi) p a)
      (mfderiv planeModel spaceModel (e ∘ phi) p b) = _
    rw [mfderiv_comp p (he.mdifferentiable (by simp)).mdifferentiableAt
      (hphi.mdifferentiable (by simp)).mdifferentiableAt,
      mfderiv_eq_fderiv,e.fderiv]
    change inner ℝ ((show ℝ from mfderiv planeModel 𝓘(ℝ) phi p a) • v)
      ((show ℝ from mfderiv planeModel 𝓘(ℝ) phi p b) • v) =
        (show ℝ from mfderiv planeModel 𝓘(ℝ) phi p a) *
          (show ℝ from mfderiv planeModel 𝓘(ℝ) phi p b)
    have hv : inner ℝ v v = 1 := by
      simp [v]
    have hinner (s t : ℝ) : inner ℝ (s • v) (t • v) = s*t := by
      rw [real_inner_smul_left,real_inner_smul_right,hv,mul_one]
    exact hinner _ _
  simpa only [hEq] using A.inducedTensor_smooth hF

omit [CompactSpace M] in
/-- The cutoff absorbs all coefficient chart boundaries. -/
lemma supportedPrimitiveCoefficient_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞
      (fun p => (psi a p)^2 * A.primitiveCoefficientField P a p (u p)) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hp2 : p ∈ tsupport (fun x => (psi a x)^2) := tsupport_mul_subset_left hp
  have hps : p ∈ tsupport (psi a) := by
    apply (closure_mono (show Function.support (fun x => (psi a x)^2) ⊆
      Function.support (psi a) from ?_)) hp2
    intro x hx
    exact fun hz => hx (by simp [hz])
  have hpchart := hsupport a hps
  have hc := ((chart_smooth (a.1 : M)) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hq := (hQ a p hps).contMDiffAt.comp p hc
  have hb := ((A.bundleComponent_smooth_on A.tensorTriv A.tensorTriv_domain a.1 hu) p hpchart).contMDiffAt
    ((chart (a.1 : M)).open_source.mem_nhds hpchart)
  have hf := (fiberToThree.contDiff (n := ∞)).contDiffAt.contMDiffAt.comp p hb
  exact ((hpsi a p).pow 2).mul (hq.clm_apply hf)

/-- Smoothness of the actual independent-cutoff correction operator follows
from the smooth input coefficients and phases. -/
theorem primitiveFullOperator_smooth
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber →L[ℝ] TensorFiber)) ∞
      (fun p => TotalSpace.mk' (TensorFiber →L[ℝ] TensorFiber) p (A.primitiveFullOperator P psi phi p)) := by
  apply A.tensorOperator_smooth_of_apply _ houter
  intro u hu
  have hs := A.tensorSymmetrizer_smooth u hu
  have hfinite : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p
        (show CovariantTwoTensor p from
          ∑ a : A.centers × Fin 3, ((psi a p)^2 * A.primitiveCoefficientField P a p
            (tensorSymmetrizer (u p))) • (A.primitivePhaseCovector phi a p).smulRight
              (A.primitivePhaseCovector phi a p))) := by
    apply ContMDiff.sum_section
    intro a _
    exact (A.supportedPrimitiveCoefficient_smooth P psi hpsi hsupport hQ _ hs a).smul_section
      (A.phaseDifferentialSquare_smooth (phi a) (hphi a))
  have h := hfinite.add_section (hu.sub_section hs)
  have he (p : M) : A.primitiveFullOperator P psi phi p (u p) =
      (show CovariantTwoTensor p from ∑ a : A.centers × Fin 3,
        ((psi a p)^2 * A.primitiveCoefficientField P a p (tensorSymmetrizer (u p))) •
          (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) +
            (u p - (show CovariantTwoTensor p from tensorSymmetrizer (u p))) := by
    exact completedPrimitiveOperator_rankOne (fun a => A.primitiveCoefficientField P a p)
      (fun a => psi a p) (fun a => A.primitivePhaseCovector phi a p) (u p)
  simpa only [he,Pi.add_apply,Pi.sub_apply] using! h


/-- The corrected amplitudes are smooth from their genuine coefficient,
cutoff and phase data; no operator-smoothness hypothesis remains. -/
theorem correctedPrimitiveAmplitude_smooth_of_data
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.correctedPrimitiveAmplitude P psi phi u a) :=
  A.correctedPrimitiveAmplitude_smooth P psi phi hpsi hsupport hQ
    (A.primitiveFullOperator_smooth P psi phi hpsi hphi hsupport hQ houter) hinv u hu hpos a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
