import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Laplacian

namespace OAI

/-! Finite linear combinations commute with the actual weak-form coordinate
Laplacian. These identities are used only for Gram-corrected orbitals. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem configurationRealPartial_sum {m : ℕ} (c : Fin m → ℝ)
    (f : Fin m → Configuration 1 → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (a : Fin 1 × Fin 3) (x : Configuration 1) :
    configurationRealPartial (fun y => ∑ j, c j*f j y) a x =
      ∑ j, c j*configurationRealPartial (f j) a x := by
  unfold configurationRealPartial
  have hd (j : Fin m) := (hf j).differentiable (by norm_num) x
  rw [fderiv_fun_sum (fun j _ => (hd j).const_mul (c j))]
  simp only [sum_apply,fderiv_const_mul (hd _),smul_apply,smul_eq_mul]

theorem configurationRealLaplacian_sum {m : ℕ} (c : Fin m → ℝ)
    (f : Fin m → Configuration 1 → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => ∑ j, c j*f j y) x =
      ∑ j, c j*configurationRealLaplacian (f j) x := by
  have hfirst (a : Fin 1 × Fin 3) :
      configurationRealPartial (fun y => ∑ j, c j*f j y) a =
        (fun y => ∑ j, c j*configurationRealPartial (f j) a y) :=
    funext (configurationRealPartial_sum c f (fun j => (hf j).of_le (by norm_num)) a)
  unfold configurationRealLaplacian
  simp_rw [hfirst,configurationRealPartial_sum c _ (fun j => configurationRealPartial_C1 (hf j) _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
