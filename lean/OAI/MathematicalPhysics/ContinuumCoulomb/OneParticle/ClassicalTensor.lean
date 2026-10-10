import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalH1
import OAI.Analysis.CoulombRadii.FormDomain.CubeGradient

namespace OAI

/-! C1 tensor products and their actual weak-H1 partials. Fubini supplies
L2 membership for decaying orbitals; compact support is unnecessary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem tensorOrbital_C1 {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s)) (p : Fin n → α) (s : SpinConfiguration n) :
    ContDiff ℝ 1 (Coulomb.tensorOrbital v p s) := by
  unfold Coulomb.tensorOrbital
  apply contDiff_prod
  intro i _
  exact (hv (p i) (s i)).comp (Coulomb.positionCLM i).contDiff

theorem tensorOrbital_C1_fderiv {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s)) (p : Fin n → α)
    (s : SpinConfiguration n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1) =
      (fderiv ℝ (fun y => v (p i) y (s i)) (Coulomb.position x i) (EuclideanSpace.single b 1)) *
        ∏ j ∈ Finset.univ.erase i, v (p j) (Coulomb.position x j) (s j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n =>
      v (p j) (Coulomb.position y j) (s j)) x :=
    by
      change DifferentiableAt ℝ ((fun y => v (p j) y (s j)) ∘ Coulomb.positionCLM j) x
      exact ((hv (p j) (s j)).differentiable (by norm_num) (Coulomb.positionCLM j x)).comp x
        (Coulomb.positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => v (p j) (Coulomb.position y j) (s j)) x =
      (fderiv ℝ (fun y => v (p j) y (s j)) (Coulomb.position x j)).comp (Coulomb.positionCLM j) :=
    by
      change fderiv ℝ ((fun y => v (p j) y (s j)) ∘ Coulomb.positionCLM j) x = _
      exact (((hv (p j) (s j)).differentiable (by norm_num) (Coulomb.positionCLM j x)).hasFDerivAt.comp x
        (Coulomb.positionCLM j).hasFDerivAt).fderiv
  unfold Coulomb.tensorOrbital
  rw [fderiv_finsetProd (fun j _ => hd j), sum_apply]
  simp only [smul_apply, smul_eq_mul, he, ContinuousLinearMap.comp_apply, Coulomb.positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _ hji
    simp only [ite_eq_right hji, map_zero, mul_zero]
  · simp

theorem tensorOrbital_partial_memLp {n : ℕ} {α : Type*} (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1)) 2)
    (p : Fin n → α) (s : SpinConfiguration n) (i : Fin n) (b : Fin 3) :
    MemLp (fun x => fderiv ℝ (Coulomb.tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1)) 2 := by
  let f : Fin n → Position → ℂ := fun j y => v (p j) y (s j)
  let d : Fin n → Position → ℂ := fun j x => fderiv ℝ (fun y => v (p j) y (s j)) x (EuclideanSpace.single b 1)
  have h := (Coulomb.slotTensor_memLp f d (fun j => hL2 (p j) (s j))
    (fun j => hpartial (p j) (s j) b) (Equiv.refl (Fin n)) i).comp_measurePreserving
    (Coulomb.configurationMeasurableEquiv_measurePreserving n)
  convert h using 1
  funext x
  simp only [Function.comp_apply]
  rw [tensorOrbital_C1_fderiv v hv, Coulomb.slotTensor_factor]
  rfl

end ContinuumCoulomb

end

end OAI
