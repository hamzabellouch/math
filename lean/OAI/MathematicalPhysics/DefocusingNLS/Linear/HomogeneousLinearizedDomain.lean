import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeDomain
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorPerturbation

namespace OAI

/-! # The reverse domain inclusion for the actual linearized evolution -/

open Set
open scoped Laplacian ZeroAtInfty

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
attribute [local irreducible] homogeneousFreeOperator homogeneousLinearizedStep

theorem homogeneousLinearized_derivWithin_of_free (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      v (Ici 0) 0) :
    HasDerivWithinAt (fun t : ℝ => homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal u)
      (v + homogeneousLinearizedPotential a k ha ha1 hk m q u) (Ici 0) 0 := by
  have hD := (hasDerivAt_homogeneousDuhamel_zero a b k ha ha1 hk
    (homogeneousLinearizedHistory a b k ha ha1 hk m q u)
    (continuous_homogeneousLinearizedHistory a b k ha ha1 hk m q u)).hasDerivWithinAt
      (s := Ici 0)
  rw [homogeneousLinearizedHistory_zero] at hD
  apply (hu.add hD).congr_of_mem _ (by simp only [mem_Ici]; exact le_rfl)
  intro t ht
  have he := homogeneousLinearizedStep_duhamel a b k ha ha1 hk m q t.toNNReal u
  simpa only [Pi.add_apply, Real.coe_toNNReal t ht] using he

theorem homogeneousLinearized_hasDerivWithinAt_of_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q u uL v : HomogeneousY a k)
    (hL : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk uL x =
      Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x)
    (hv : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk v x =
      Complex.I * Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * homogeneousPhysicalCLM a k ha ha1 hk u x -
        Complex.I * oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q x)
          (homogeneousPhysicalCLM a k ha ha1 hk u x)) :
    HasDerivWithinAt (fun t : ℝ => homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal u)
      v (Ici 0) 0 := by
  let B := homogeneousLinearizedPotential a k ha ha1 hk m q
  let g := v - B u - Complex.I • uL - (Complex.I * (b : ℂ)) • u
  have hg (x : E) : homogeneousPhysicalCLM a k ha ha1 hk g x =
      -(a : ℂ) * homogeneousPhysicalCLM a k ha ha1 hk u x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x := by
    simp only [g, B, map_sub, map_smul, ZeroAtInftyContinuousMap.sub_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul,
      homogeneousLinearizedPotential_physical, hv, hL]
    ring
  have h := homogeneousLinearized_derivWithin_of_free a b k ha ha1 hk m q u _
    (homogeneousFree_hasDerivWithinAt_of_classical a b k ha ha1 hk u uL g hL hg)
  convert h using 1
  dsimp only [g, B]
  module

end DefocusingNLS

end OAI
