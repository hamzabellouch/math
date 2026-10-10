import OAI.Analysis.CircleDomains.Sobolev.LocalPairChainWitness
import OAI.Analysis.CircleDomains.Sobolev.BarrierL2Error
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! The joint weak chain rule expressed as an actual linear differential.
Its norm is exactly the norm of the scalar weak gradient, so the
three-term barrier estimate applies to the constructed Sobolev witness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def weakPairDifferential (a b : EuclideanPlane) : EuclideanPlane →L[ℝ] EuclideanPlane :=
  (innerSL ℝ a).smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
    (innerSL ℝ b).smulRight (EuclideanSpace.single (1 : Fin 2) 1)

 theorem plane_inner_basis (a : EuclideanPlane) (i : Fin 2) :
    innerSL ℝ a (EuclideanSpace.single i 1) = a i := by
  fin_cases i <;> simp [innerSL_apply_apply, PiLp.inner_apply ]

 theorem weakPairDifferential_basis (a b : EuclideanPlane) (i : Fin 2) :
    weakPairDifferential a b (EuclideanSpace.single i 1) = planePair (a i) (b i) := by
  simp only [weakPairDifferential, add_apply, ContinuousLinearMap.smulRight_apply,
    plane_inner_basis, planePair]

 theorem plane_covector_of_basis (L : EuclideanPlane →L[ℝ] ℝ) :
    L = innerSL ℝ (planePair (L (EuclideanSpace.single (0 : Fin 2) 1))
      (L (EuclideanSpace.single (1 : Fin 2) 1))) := by
  ext x
  rw [← planePair_coordinates x, planePair_covector, planePair_covector]
  simp only [plane_inner_basis, planePair_zero, planePair_one]

 theorem weakPairDifferential_chain (L : EuclideanPlane →L[ℝ] ℝ) (a b : EuclideanPlane) :
    L.comp (weakPairDifferential a b) =
      innerSL ℝ (L (EuclideanSpace.single (0 : Fin 2) 1) • a+
        L (EuclideanSpace.single (1 : Fin 2) 1) • b) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, weakPairDifferential, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    smul_apply, smul_eq_mul]
  ring

 theorem weakPairDifferential_chain_norm_sub
    (L K : EuclideanPlane →L[ℝ] ℝ) (a b c d : EuclideanPlane) :
    ‖L.comp (weakPairDifferential a b)-K.comp (weakPairDifferential c d)‖ =
      ‖(L (EuclideanSpace.single (0 : Fin 2) 1) • a+
        L (EuclideanSpace.single (1 : Fin 2) 1) • b)-
        (K (EuclideanSpace.single (0 : Fin 2) 1) • c+
        K (EuclideanSpace.single (1 : Fin 2) 1) • d)‖ := by
  rw [weakPairDifferential_chain, weakPairDifferential_chain, ← map_sub, innerSL_apply_norm]

 theorem localPairChainWitness_gradient {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (x : EuclideanPlane) :
    (localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd).weakGrad x =
      fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1) • Wu.weakGrad x+
      fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1) • Wv.weakGrad x := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  rfl

end CircleDomainRigidity

end

end OAI
