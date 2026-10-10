import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedDomain
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLaplacianDomain
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SemigroupGeneratorEigenvector
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeLinearization

namespace OAI

/-! # Physical eigenvectors with two extra orders are semigroup eigenvectors -/

open Set
open scoped Laplacian ZeroAtInfty NNReal

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
attribute [local irreducible] homogeneousLinearizedStep

theorem homogeneousLinearized_eigenvector_of_physical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q u : HomogeneousY a k) (uH : HomogeneousY a (k + 2)) (lam : ℝ)
    (hH : ∀ x, homogeneousPhysicalCLM a (k + 2) ha ha1 (by linarith) uH x =
      homogeneousPhysicalCLM a k ha ha1 hk u x)
    (he : ∀ x, similarityLinearization a b m
      (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y)
      (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x =
        (lam : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk u x) (t : ℝ≥0) :
    homogeneousLinearizedStep a b k ha ha1 hk m q t u = Real.exp (lam * (t : ℝ)) • u := by
  obtain ⟨uL, hL⟩ := exists_homogeneous_laplacian_of_higher_order a k ha ha1 hk uH
  have hEq : (fun y : E => homogeneousPhysicalCLM a (k + 2) ha ha1 (by linarith) uH y) =
      (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) := funext hH
  simp only [hEq] at hL
  have hd := homogeneousLinearized_hasDerivWithinAt_of_classical a b k ha ha1 hk m q u uL
    (lam • u) hL (fun x => by
      have hp := he x
      dsimp only [similarityLinearization] at hp
      simp only [ContinuousLinearMap.map_smul_of_tower,
        ZeroAtInftyContinuousMap.smul_apply, Complex.real_smul]
      rw [map_smul] at hp
      simp only [Complex.real_smul] at hp
      push_cast at hp
      linear_combination -hp)
  apply semigroup_eigenvector_of_generator
    (homogeneousLinearizedStep a b k ha ha1 hk m q)
    (fun v => (continuous_homogeneousLinearizedStep_apply a b k ha ha1 hk m q).comp
      (continuous_id.prodMk continuous_const))
    (homogeneousLinearizedStep_zero a b k ha ha1 hk m q)
    (fun s t => by rw [add_comm, homogeneousLinearizedStep_add]) u lam hd t

end DefocusingNLS

end OAI
