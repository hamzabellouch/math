import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakPairOverlap
import OAI.Analysis.Conductivity.Branching.BranchOutputNormalization

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

def branchFinitePair {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) : WeakFiniteTensorPair {x : Coord3 | z.d<x 0} :=
  z.w.output (branchNormalizeEquiv i) 0

lemma branchFinitePair_v {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) :
    (branchFinitePair i z).v x=branchNormalize i (z.w.v x) := by
  simp [branchFinitePair]

lemma branchFinitePair_flux {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (j : Fin 2) :
    ((branchFinitePair i z).G x).col j=branchNormalize i (fun k => (z.w.G x).col k) j := by
  change (linearColumnsPullback (ContinuousLinearEquiv.refl ℝ Coord3)
    (branchNormalizeEquiv i) z.w.G (x-0)).col j=_
  rw [sub_zero,linearColumnsPullback_col]
  ext k
  fin_cases i <;> fin_cases j <;>
    simp [operatorMatrix,branchNormalizeEquiv_apply,branchNormalize,linearFluxPullback,
      Fin.sum_univ_two,Pi.single_apply,Matrix.col_apply]
  ring

lemma branchFinitePair_initial {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {f : Fin 2 → TorusL2} (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    (branchFinitePair i z).v x=fun j => torusAffineField s (centralBasisSlopes j i) (f j) x := by
  rw [branchFinitePair_v,z.initial_field x hx]
  change branchNormalize i (fun j => torusAffineField s (normalizedSlope j)
    (branchNormalize i f j) x)=_
  rw [branchNormalize_affineField hs i normalizedSlope (branchNormalize i f) (z.d_pos.trans hx.1),
    branchNormalize_normalized_slope,branchNormalize_involutive]

lemma branchFinitePair_terminal {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (hx : z.R≤x 0) :
    (branchFinitePair i z).v x=fun j => centralBasisSlopes j i*x 0+(mFourierCoeff (f j) 0).re := by
  rw [branchFinitePair_v]
  have he : z.w.v x=(fun j => normalizedSlope j*x 0)+
      (fun j => (mFourierCoeff (branchNormalize i f j : TorusL2) 0).re) := by
    ext j
    exact z.terminal_component j x hx
  rw [he,branchNormalize_add]
  have hm := (branchNormalize_means i (branchNormalize i f)).trans
    (by rw [branchNormalize_involutive])
  rw [hm]
  have hs : branchNormalize i (fun j => normalizedSlope j*x 0)=
      fun j => centralBasisSlopes j i*x 0 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [branchNormalize,normalizedSlope,centralBasisSlopes]
  rw [hs]
  rfl

lemma branchFinitePair_terminal_flux {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i f)) (x : Coord3) (hx : z.R<x 0) (j : Fin 2) :
    ((branchFinitePair i z).G x).col j=centralBasisSlopes j i • Pi.single 0 1 := by
  rw [branchFinitePair_flux]
  have he : (fun k => (z.w.G x).col k)=(fun k => normalizedSlope k • Pi.single 0 1) :=
    funext fun k => z.terminal_flux k x hx
  rw [he]
  fin_cases i <;> fin_cases j <;> simp [branchNormalize,normalizedSlope,centralBasisSlopes]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

lemma branchFinitePair_periodic_v : AngularPeriodic (2*Real.pi) (branchFinitePair i z).v := by
  intro n x
  simp only [branchFinitePair_v,z.periodic_v n x]

lemma branchFinitePair_initial_E (x : Coord3) (hx : x 0∈Icc z.d (z.d+z.e)) :
    (branchFinitePair i z).E x=flatBackgroundTensor s := by
  simpa only [branchFinitePair,WeakFiniteTensorPair.output_E] using z.initial_E x hx

lemma branchFinitePair_periodic_E : AngularPeriodic (2*Real.pi) (branchFinitePair i z).E := by
  simpa only [branchFinitePair,WeakFiniteTensorPair.output_E] using z.periodic_E

lemma branchFinitePair_initial_flux
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0∈Ioo z.d (z.d+z.e)) :
    ((branchFinitePair i z).G x).col j=
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x := by
  apply (branchFinitePair i z).flux_on_flat_patch
    (V:={x : Coord3 | x 0∈Ioo z.d (z.d+z.e)})
    (isOpen_Ioo.preimage (continuous_apply 0)) s
    (fun x hx => branchFinitePair_initial_E i z x ⟨hx.1.le,hx.2.le⟩)
    (fun x j => torusAffineField s (centralBasisSlopes j i) (f j) x)
    (contDiffOn_pi.mpr fun j => ((torusAffineField_smooth hs _ _).of_le
      (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun y hy => z.d_pos.trans hy.1))
    (fun x hx => branchFinitePair_initial hs i z x hx) j x hx

def branchCorrection (j : Fin 2) : Coord3 → ℝ :=
  torusEndingCorrection z.d z.e (fun x => (branchFinitePair i z).v x j)
    (torusAffineField s (centralBasisSlopes j i) (f j))

def branchFluxCorrection (j : Fin 2) : Coord3 → Coord3 :=
  torusEndingFluxCorrection z.d z.e (fun x => ((branchFinitePair i z).G x).col j)
    (flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)))

lemma branchCorrection_C2
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 2 (branchCorrection i z j) := by
  exact torusEndingCorrection_C2 z.e_pos (contDiff_pi.mp (branchFinitePair i z).smooth j)
    (((torusAffineField_smooth hs _ _).of_le
      (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => congrFun (branchFinitePair_initial hs i z x hx) j)

lemma branchCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchCorrection i z j) := by
  exact torusEndingCorrection_periodic
    (fun n x => congrFun (branchFinitePair_periodic_v i z n x) j)
    (torusAffineField_periodic _ _ _)

lemma branchCorrection_zero
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0<z.d) : branchCorrection i z j x=0 := by
  exact (torusEndingCorrection_initial_zero z.e_pos
    (fun y hy => congrFun (branchFinitePair_initial hs i z y hy) j)
    (by linarith [z.e_pos] : x 0<z.d+3*z.e/4)).eq_of_nhds

lemma branchFluxCorrection_C1
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) : ContDiff ℝ 1 (branchFluxCorrection i z j) := by
  exact torusEndingFluxCorrection_C1 z.e_pos ((branchFinitePair i z).component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => branchFinitePair_initial_flux i z hs j x hx)

lemma branchFluxCorrection_periodic (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (branchFluxCorrection i z j) := by
  exact torusEndingFluxCorrection_periodic
    (fun n x => congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j)
      ((branchFinitePair i z).flux_periodic (branchFinitePair_periodic_v i z)
        (branchFinitePair_periodic_E i z) n x))
    (flatModeFlux_periodic (torusAffineField_periodic _ _ _))

lemma branchFluxCorrection_divergence
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) : coordinateDivergence (branchFluxCorrection i z j) x=0 := by
  exact torusEndingFluxCorrection_divergence z.e_pos ((branchFinitePair i z).component_flux_C1 j)
    (((flatModeFlux_smoothOn (axial_halfspace_open 0) (torusAffineField_smooth hs _ _)).of_le
      (show (1 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).mono
        (fun x hx => z.d_pos.trans hx))
    (fun x hx => branchFinitePair_initial_flux i z hs j x hx)
    (fun x hx => (branchFinitePair i z).flux_divergence (axial_halfspace_open z.d) j x hx)
    (fun x hx => torusAffineField_flux_divergence hs _ _ (z.d_pos.trans hx)) x

lemma branchFluxCorrection_zero
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (x : Coord3) (hx : x 0=0) : branchFluxCorrection i z j x=0 := by
  exact (torusEndingFluxCorrection_initial_zero z.e_pos
    (fun y hy => branchFinitePair_initial_flux i z hs j y hy)
    (by rw [hx]; linarith [z.d_pos,z.e_pos])).eq_of_nhds

lemma branchFluxCorrection_terminal (j : Fin 2) (x : Coord3) (hx : z.R<x 0) :
    branchFluxCorrection i z j x=centralBasisSlopes j i • Pi.single 0 1-
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x := by
  rw [show branchFluxCorrection i z j x=((branchFinitePair i z).G x).col j-
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x from
    (torusEndingFluxCorrection_terminal (by linarith [z.e_pos,z.overlap_lt] : z.d+z.e/2<x 0)).eq_of_nhds,
    branchFinitePair_terminal_flux i z x hx j]

end ScalarConductivity

end

end OAI
