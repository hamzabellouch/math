import Mathlib
import OAI.Analysis.HardSphere.Orbitals.Chi
import OAI.Analysis.HardSphere.Geometry.LabelLift

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
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

def chiOne (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier 1 L :=
  (raw L (8*δ) x).mul (raw L (8*δ) x)

lemma chiOne_apply (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration 1 L) :
    (chiOne L δ x).toFun X=(chi L δ x (X 0) : ℂ) := by
  simp only [chiOne,SmoothMultiplier.mul,Pi.mul_apply,raw,SmoothMultiplier.ofSmooth,chi]
  rw [Complex.ofReal_pow,pow_two]

def countMultiplier (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) : SmoothMultiplier n L :=
  SmoothMultiplier.sum (fun i : Fin n ↦ (chiOne L δ x).liftLabel n i)

lemma countMultiplier_apply (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) :
    (countMultiplier n L δ x).toFun X=(count L δ x X : ℂ) := by
  change (∑ i : Fin n, (chiOne L δ x).toFun (fun _ ↦ X i)) = _
  simp_rw [chiOne_apply]
  exact (Complex.ofReal_sum _ _).symm

lemma countMultiplier_real (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) :
    conj ((countMultiplier n L δ x).toFun X)=(countMultiplier n L δ x).toFun X := by
  rw [countMultiplier_apply,Complex.conj_ofReal]

lemma count_nonneg {n : ℕ} (L : Length) (δ : ℝ) (x : Torus L) (X : Configuration n L) :
    0 ≤ count L δ x X := Finset.sum_nonneg fun _ _ ↦ (chi_bounds _ _ _ _).1

lemma chiOne_partial (L : Length) (δ : ℝ) (x y : Torus L) (j : Fin 3) :
    coordDerivative 1 L (chiOne L δ x).toFun (0,j) (fun _ ↦ y)=
      2*(bump L (8*δ) x y : ℂ)*coordDerivative 1 L (raw L (8*δ) x).toFun (0,j) (fun _ ↦ y) := by
  have he := congrFun (coordDerivative_mul ((raw L (8*δ) x).smooth.differentiable (by simp))
    ((raw L (8*δ) x).smooth.differentiable (by simp)) (0,j)) (fun _ ↦ y)
  change coordDerivative 1 L ((raw L (8*δ) x).toFun * (raw L (8*δ) x).toFun) (0,j) _ = _
  rw [he]
  change (bump L (8*δ) x y : ℂ)*_+(bump L (8*δ) x y : ℂ)*_=_
  ring

lemma countMultiplier_partial (n : ℕ) (L : Length) (δ : ℝ) (x : Torus L)
    (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (countMultiplier n L δ x).toFun p X=
      coordDerivative 1 L (chiOne L δ x).toFun (0,p.2) (fun _ ↦ X p.1) := by
  classical
  rw [countMultiplier,SmoothMultiplier.partial_sum]
  simp_rw [SmoothMultiplier.partial_liftLabel]
  simp

lemma chiOne_partial_sq_le {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x y : Torus L) (j : Fin 3) :
    ‖coordDerivative 1 L (chiOne L δ x).toFun (0,j) (fun _ ↦ y)‖^2 ≤
      (4*(24*Real.pi^2*M^2/(8*δ)^2))*chi L δ x y := by
  rw [chiOne_partial,norm_mul,norm_mul,mul_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  have h := mul_le_mul_of_nonneg_left (raw_partial_sq_le (by positivity : 0<8*δ) hM hb x y j)
    (show 0 ≤ 4*(bump L (8*δ) x y)^2 by positivity)
  dsimp [chi]
  nlinarith

lemma countMultiplier_gradient_le {n : ℕ} {L : Length} {δ M : ℝ} (hδ : 0<δ) (hM : 0 ≤ M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M) (x : Torus L) (X : Configuration n L) :
    (∑ p : Direction n, ‖coordDerivative n L (countMultiplier n L δ x).toFun p X‖^2) ≤
      (3*(4*(24*Real.pi^2*M^2/(8*δ)^2)))*count L δ x X := by
  simp_rw [countMultiplier_partial]
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin n, ∑ _j : Fin 3, (4*(24*Real.pi^2*M^2/(8*δ)^2))*chi L δ x (X i) := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ chiOne_partial_sq_le hδ hM hb x (X i) j
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,count,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end HardSphere.CellOrbital

end

end OAI
