import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPairRegularity
import OAI.Analysis.Conductivity.Fourier.TorusSpectralContinuation
import OAI.Analysis.Conductivity.Branching.TorusEndingCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

variable {E : Type*} [AddCommGroup E]

def branchNormalize (i : Fin 3) (u : Fin 2 → E) : Fin 2 → E :=
  if i=0 then ![-u 0,u 1-u 0] else if i=1 then u else ![u 1,u 0]

lemma branchNormalize_involutive (i : Fin 3) : Function.Involutive (branchNormalize (E:=E) i) := by
  intro u
  ext j
  fin_cases i <;> fin_cases j <;> simp [branchNormalize]

lemma branchNormalize_add (i : Fin 3) (u v : Fin 2 → E) :
    branchNormalize i (u+v)=branchNormalize i u+branchNormalize i v := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [branchNormalize] <;> abel

variable [Module ℝ E]

def branchNormalizeLinear (i : Fin 3) : (Fin 2 → E) →ₗ[ℝ] (Fin 2 → E) where
  toFun := branchNormalize i
  map_add' := branchNormalize_add i
  map_smul' c u := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [branchNormalize,smul_sub]

def branchNormalizeEquiv (i : Fin 3) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ({ toLinearMap := branchNormalizeLinear i
     invFun := branchNormalize i
     left_inv := branchNormalize_involutive i
     right_inv := branchNormalize_involutive i } :
        (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)).toContinuousLinearEquiv

@[simp] lemma branchNormalizeEquiv_apply (i : Fin 3) (u : Fin 2 → ℝ) :
    branchNormalizeEquiv i u=branchNormalize i u := rfl

lemma branchNormalize_basis_slopes (i : Fin 3) :
    branchNormalize i (fun j => centralBasisSlopes j i)=normalizedSlope := by
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [branchNormalize,centralBasisSlopes,normalizedSlope]

lemma branchNormalize_normalized_slope (i : Fin 3) :
    branchNormalize i normalizedSlope=(fun j => centralBasisSlopes j i) := by
  rw [←branchNormalize_basis_slopes i,branchNormalize_involutive i]

lemma branchNormalize_affineField {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (κ : Fin 2 → ℝ) (f : Fin 2 → TorusL2) {x : Coord3} (hx : 0<x 0) :
    branchNormalize i (fun j => torusAffineField s (κ j) (f j) x)=
      fun j => torusAffineField s (branchNormalize i κ j) (branchNormalize i f j) x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [branchNormalize,torusAffineField,torusRealContinuation_neg,
      torusRealContinuation_sub hs _ _ hx] <;> ring

lemma branchNormalize_means (i : Fin 3) (f : Fin 2 → TorusL2) :
    branchNormalize i (fun j => (mFourierCoeff (f j) 0).re)=
      fun j => (mFourierCoeff (branchNormalize i f j : TorusL2) 0).re := by
  fin_cases i
  · ext j
    fin_cases j
    · change -(mFourierCoeff (f 0) 0).re=(mFourierCoeff (-f 0 : TorusL2) 0).re
      rw [mFourierCoeff_Lp_neg,Complex.neg_re]
    · change (mFourierCoeff (f 1) 0).re-(mFourierCoeff (f 0) 0).re=
        (mFourierCoeff (f 1-f 0 : TorusL2) 0).re
      simp only [sub_eq_add_neg]
      rw [mFourierCoeff_Lp_add,mFourierCoeff_Lp_neg,Complex.add_re,Complex.neg_re]
  · rfl
  · ext j
    fin_cases j <;> rfl

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

namespace TorusEndingData
variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (z : TorusEndingData s f)

lemma terminal_component (j : Fin 2) (x : Coord3) (hx : z.R≤x 0) :
    z.w.v x j=normalizedSlope j*x 0+(mFourierCoeff (f j) 0).re := by
  rw [z.terminal_v x hx]
  fin_cases j <;> simp [normalizedSlope]

lemma terminal_gradient (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    (gradientColumns (fderiv ℝ z.w.v x)).col j=normalizedSlope j • Pi.single 0 1 := by
  have he : (fun x => z.w.v x j)=ᶠ[𝓝 x]
      (fun x => normalizedSlope j*x 0+(mFourierCoeff (f j) 0).re) := by
    filter_upwards [(axial_halfspace_open z.R).mem_nhds hx] with y hy
    exact z.terminal_component j y hy.le
  have hd := (((ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ).hasFDerivAt
    (x:=x)).const_mul (normalizedSlope j)).add_const ((mFourierCoeff (f j) 0).re)
  ext i
  change fderiv ℝ z.w.v x (Pi.single i 1) j=normalizedSlope j*((Pi.single (0:Fin 3) (1:ℝ) : Coord3) i)
  rw [←potential_component_fderiv (z.w.smooth.differentiable (by norm_num)) j,
    he.fderiv_eq (𝕜 := ℝ)]
  change fderiv ℝ (fun x => normalizedSlope j *
    (ContinuousLinearMap.proj (0 : Fin 3) : Coord3 →L[ℝ] ℝ) x +
      (mFourierCoeff (f j) 0).re) x (Pi.single i 1)=_
  rw [hd.fderiv]
  fin_cases i <;> simp

lemma terminal_flux (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    (z.w.G x).col j=normalizedSlope j • Pi.single 0 1 := by
  have ha : (fun x => (z.w.G x).col j)=ᵐ[volume.restrict {x : Coord3 | z.R<x 0}]
      (fun _ => normalizedSlope j • Pi.single 0 1) := by
    filter_upwards [ae_restrict_of_ae z.w.constitution,
      ae_restrict_mem (axial_halfspace_open z.R).measurableSet] with y hy hyR
    rw [←hy]
    change z.w.E y*ᵥ(gradientColumns (fderiv ℝ z.w.v y)).col j=_
    rw [z.terminal_gradient j y hyR,Matrix.mulVec_smul,z.terminal_E y hyR.le]
  exact (Measure.eqOn_open_of_ae_eq ha (axial_halfspace_open z.R)
    (z.w.component_flux_C1 j).continuous.continuousOn continuous_const.continuousOn) hx

lemma fluxCorrection_at_zero
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0=0) : z.fluxCorrection j x=0 := by
  exact (torusEndingFluxCorrection_initial_zero z.e_pos (fun y hy => z.initial_flux hs j y hy)
    (by rw [hx]; linarith [z.d_pos,z.e_pos])).eq_of_nhds

lemma fluxCorrection_at_terminal (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    z.fluxCorrection j x=normalizedSlope j • Pi.single 0 1-
      flatModeFlux s (torusAffineField s (normalizedSlope j) (f j)) x := by
  rw [show z.fluxCorrection j x=(z.w.G x).col j-
      flatModeFlux s (torusAffineField s (normalizedSlope j) (f j)) x from
    (torusEndingFluxCorrection_terminal (by linarith [z.e_pos,z.overlap_lt] : z.d+z.e/2<x 0)).eq_of_nhds,
    z.terminal_flux j x hx]

end TorusEndingData
end ScalarConductivity

end

end OAI
