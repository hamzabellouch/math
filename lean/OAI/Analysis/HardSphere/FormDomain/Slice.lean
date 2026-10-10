import Mathlib
import OAI.Analysis.HardSphere.Geometry.CoordinateLine
import OAI.Analysis.HardSphere.Geometry.NormSqIntegral

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Filter Set

lemma smooth_insertNth {n : ℕ} (j : Fin (n+1)) (x : Fin 3 → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Y : LiftedConfiguration n ↦ Fin.insertNth (α := fun _ ↦ Fin 3 → ℝ) j x Y) := by
  apply contDiff_pi.mpr
  intro i
  induction i using j.succAboveCases with
  | x => simpa only [Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : LiftedConfiguration n ↦ x))
  | p i => simpa only [Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ (Fin 3 → ℝ) i)

lemma smooth_slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Y : LiftedConfiguration n ↦ f.toFun (j.insertNth x (project n L Y))) := by
  have h := f.smooth.comp (smooth_insertNth j (representative 1 L (fun _ ↦ x) 0))
  convert h using 1
  funext Y
  congr 1
  ext i q
  induction i using j.succAboveCases with
  | x =>
    simp only [project,Fin.insertNth_apply_same]
    exact (congr_fun (congr_fun (project_representative 1 L (fun _ ↦ x)) 0) q).symm
  | p i => simp only [project,Fin.insertNth_apply_succAbove]

lemma insertNth_coordinateLine {n : ℕ} {L : Length} (j : Fin (n+1)) (x : Torus L)
    (Y : Configuration n L) (p : Direction n) (t : AddCircle L.val) :
    j.insertNth x (coordinateLine Y p t)=coordinateLine (j.insertNth x Y) (j.succAbove p.1,p.2) t := by
  ext i q
  induction i using j.succAboveCases with
  | x => simp [coordinateLine]
  | p i => simp [coordinateLine,Pi.single_apply,Fin.succAbove_inj]

lemma coordDerivative_slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) (p : Direction n) :
    coordDerivative n L (fun Y ↦ f.toFun (j.insertNth x Y)) p=
      fun Y ↦ coordDerivative (n+1) L f.toFun (j.succAbove p.1,p.2) (j.insertNth x Y) := by
  funext Y
  have h1 := hasDerivAt_coordinateLine (f := fun Y ↦ f.toFun (j.insertNth x Y)) ((smooth_slice f j x).differentiable (by simp)) Y p 0
  have h2 := hasDerivAt_coordinateLine (f.smooth.differentiable (by simp))
    (j.insertNth x Y) (j.succAbove p.1,p.2) 0
  simp only [insertNth_coordinateLine] at h1
  have h := h1.unique h2
  simpa [coordinateLine] using h

def SmoothTest.slice {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest (n+1) L a)
    (j : Fin (n+1)) (x : Torus L) : SmoothTest n L a where
  toFun Y := f.toFun (j.insertNth x Y)
  smooth := smooth_slice f j x
  compact := HasCompactSupport.of_compactSpace _
  support_allowed := by
    intro Y hY i k hik
    have h := f.support_allowed (tsupport_comp_subset_preimage f.toFun
      (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id) hY)
    simpa only [Fin.insertNth_apply_succAbove,id_eq] using h (j.succAbove i) (j.succAbove k)
      (Fin.strictMono_succAbove j hik)
  memLp := (f.continuous.comp (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  partial_memLp := fun p ↦ by
    rw [coordDerivative_slice]
    exact ((f.continuous_partial (j.succAbove p.1,p.2)).comp
      (Continuous.finInsertNth j (continuous_const : Continuous (fun _ : Configuration n L ↦ x)) continuous_id)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma smoothTest_norm_sq {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a) :
    ‖f.jet.1‖^2=∫ X : Configuration n L, ‖f.toFun X‖^2 := by
  rw [IndicatorStrong.norm_sq_integral]
  exact integral_congr_ae ((MemLp.coeFn_toLp f.memLp).fun_comp (fun z : ℂ ↦ ‖z‖^2))

lemma smoothTest_partial_norm_sq {n : ℕ} {L : Length} {a : ℝ} (f : SmoothTest n L a)
    (p : Direction n) :
    ‖f.jet.2 p‖^2=∫ X : Configuration n L, ‖coordDerivative n L f.toFun p X‖^2 := by
  rw [IndicatorStrong.norm_sq_integral]
  exact integral_congr_ae ((MemLp.coeFn_toLp (f.partial_memLp p)).fun_comp (fun z : ℂ ↦ ‖z‖^2))

end HardSphere

end

end OAI
