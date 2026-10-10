import Mathlib
import OAI.Analysis.Conductivity.Branching.BranchFiniteEnding

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

local instance flatEndingSpliceMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance flatEndingSpliceBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

variable {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2} (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i f))

def branchSplicedField (j : Fin 2) (x : Coord3) : ℝ :=
  torusAffineField s (centralBasisSlopes j i) (f j) x+branchCorrection i z j x

def branchSplicedFlux (j : Fin 2) (x : Coord3) : Coord3 :=
  flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) x+
    branchFluxCorrection i z j x

def branchSplicedTensor (x : Coord3) : Mat3 :=
  if x 0<z.d+5*z.e/8 then flatBackgroundTensor s else (branchFinitePair i z).E x

lemma branchSplicedField_initial
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {x : Coord3} (hx : x 0<z.d+3*z.e/4) :
    branchSplicedField i z j=ᶠ[𝓝 x] torusAffineField s (centralBasisSlopes j i) (f j) := by
  filter_upwards [torusEndingCorrection_initial_zero z.e_pos
    (fun y hy => congrFun (branchFinitePair_initial hs i z y hy) j) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy,add_zero]

lemma branchSplicedFlux_initial
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {x : Coord3} (hx : x 0<z.d+3*z.e/4) :
    branchSplicedFlux i z j=ᶠ[𝓝 x]
      flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) := by
  filter_upwards [torusEndingFluxCorrection_initial_zero z.e_pos
    (fun y hy => branchFinitePair_initial_flux i z hs j y hy) hx] with y hy
  change _+torusEndingFluxCorrection _ _ _ _ y=_
  rw [hy,add_zero]

lemma branchSplicedField_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedField i z j=ᶠ[𝓝 x] (fun y => (branchFinitePair i z).v y j) := by
  filter_upwards [torusEndingCorrection_terminal
    (v:=fun y => (branchFinitePair i z).v y j)
    (f:=torusAffineField s (centralBasisSlopes j i) (f j)) hx] with y hy
  change _+torusEndingCorrection _ _ _ _ y=_
  rw [hy]
  change torusAffineField s (centralBasisSlopes j i) (f j) y+
    ((branchFinitePair i z).v y j-torusAffineField s (centralBasisSlopes j i) (f j) y)=_
  ring

lemma branchSplicedFlux_final (j : Fin 2) {x : Coord3} (hx : z.d+z.e/2<x 0) :
    branchSplicedFlux i z j=ᶠ[𝓝 x] (fun y => ((branchFinitePair i z).G y).col j) := by
  filter_upwards [torusEndingFluxCorrection_terminal
    (G:=fun y => ((branchFinitePair i z).G y).col j)
    (F:=flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j))) hx] with y hy
  change _+torusEndingFluxCorrection _ _ _ _ y=_
  rw [hy]
  change flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) y+
    (((branchFinitePair i z).G y).col j-flatModeFlux s (torusAffineField s (centralBasisSlopes j i) (f j)) y)=_
  abel

lemma branchSplicedTensor_measurable : Measurable (branchSplicedTensor i z) := by
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const)
    measurable_const (branchFinitePair i z).measurable

lemma branchSplicedTensor_symm (x : Coord3) : (branchSplicedTensor i z x).IsSymm := by
  unfold branchSplicedTensor
  split
  · exact flatBackgroundTensor_symm s
  · exact (branchFinitePair i z).symm x

lemma branchSplicedTensor_periodic : AngularPeriodic (2*Real.pi) (branchSplicedTensor i z) := by
  intro n x
  have hzero : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  simp only [branchSplicedTensor,hzero,branchFinitePair_periodic_E i z n x]

lemma branchSplicedTensor_elliptic
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,
      c*(v ⬝ᵥ v)≤v ⬝ᵥ(branchSplicedTensor i z x*ᵥv) ∧
        v ⬝ᵥ(branchSplicedTensor i z x*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨c,C,hc,hcC,hb⟩ := (branchFinitePair i z).elliptic
  refine ⟨min c (1/2),max C (3*‖flatBackgroundTensor s‖+1),
    lt_min hc (by norm_num),(min_le_left _ _).trans (hcC.trans (le_max_left _ _)),?_⟩
  intro x v
  have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun k _ => mul_self_nonneg (v k))
  unfold branchSplicedTensor
  split
  · constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hv).trans
        (flatBackgroundTensor_lower hs v)
    · exact ((le_abs_self _).trans (matrix_quadratic_elementwise_bound _ v)).trans
        (mul_le_mul_of_nonneg_right
          ((le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans (le_max_right _ _)) hv)
  · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hv).trans (hb x v).1,
      (hb x v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)⟩

lemma branchSplicedField_smooth
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (j : Fin 2) :
    ContDiffOn ℝ 2 (branchSplicedField i z j) {x | 0<x 0} :=
  ((torusAffineField_smooth hs _ _).of_le
    (show (2 : WithTop ℕ∞)≤↑(⊤:ℕ∞) from WithTop.coe_le_coe.mpr le_top)).add
      (branchCorrection_C2 i z hs j).contDiffOn

lemma branchSpliced_constitution
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (j : Fin 2) :
    ∀ᵐ x : Coord3,branchSplicedTensor i z x*ᵥ
      (fun k => fderiv ℝ (branchSplicedField i z j) x (Pi.single k 1))=
        branchSplicedFlux i z j x := by
  filter_upwards [(branchFinitePair i z).constitution] with x hx
  by_cases ht : x 0<z.d+5*z.e/8
  · have ht' : x 0<z.d+3*z.e/4 := by linarith [z.e_pos]
    rw [branchSplicedTensor,ite_eq_left ht,
      (branchSplicedField_initial i z hs j ht').fderiv_eq,
      (branchSplicedFlux_initial i z hs j ht').eq_of_nhds,flatModeFlux_tensor]
  · have ht' : z.d+z.e/2<x 0 := by linarith [z.e_pos,not_lt.mp ht]
    rw [branchSplicedTensor,ite_eq_right ht,
      (branchSplicedField_final i z j ht').fderiv_eq,
      (branchSplicedFlux_final i z j ht').eq_of_nhds]
    have hj := congrArg (fun M : Matrix (Fin 3) (Fin 2) ℝ => M.col j) hx
    change _*ᵥ((gradientColumns (fderiv ℝ (branchFinitePair i z).v x)).col j)=_ at hj
    have he : (gradientColumns (fderiv ℝ (branchFinitePair i z).v x)).col j=
        (fun k => fderiv ℝ (branchFinitePair i z).v x (Pi.single k 1) j) := by
      ext k
      rfl
    rw [he] at hj
    simpa only [potential_component_fderiv
      ((branchFinitePair i z).smooth.differentiable (by norm_num)) j] using hj

end ScalarConductivity

end

end OAI
