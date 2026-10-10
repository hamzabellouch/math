import OAI.Analysis.CircleDomains.Sobolev.WeakPairDifferential

namespace OAI

/-! Exact conversion between planar scalar covectors and their two
coordinate gradients. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def planeCovectorGradient (L : EuclideanPlane →L[ℝ] ℝ) : EuclideanPlane :=
  planePair (L (EuclideanSpace.single (0 : Fin 2) 1)) (L (EuclideanSpace.single (1 : Fin 2) 1))

 theorem planeCovectorGradient_inner (a : EuclideanPlane) :
    planeCovectorGradient (innerSL ℝ a) = a := by
  simp only [planeCovectorGradient, plane_inner_basis, planePair_coordinates]

 theorem planeCovectorGradient_sub (L K : EuclideanPlane →L[ℝ] ℝ) :
    planeCovectorGradient (L-K) = planeCovectorGradient L-planeCovectorGradient K := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [planeCovectorGradient, sub_apply]

 theorem planeCovectorGradient_norm (L : EuclideanPlane →L[ℝ] ℝ) :
    ‖planeCovectorGradient L‖ = ‖L‖ := by
  have he : L = innerSL ℝ (planeCovectorGradient L) := plane_covector_of_basis L
  calc
    _ = ‖innerSL ℝ (planeCovectorGradient L)‖ := (innerSL_apply_norm ℝ (planeCovectorGradient L)).symm
    _ = ‖L‖ := congrArg norm he.symm

 theorem continuous_planeCovectorGradient : Continuous planeCovectorGradient :=
  continuous_planePair (continuous_id.clm_apply continuous_const)
    (continuous_id.clm_apply continuous_const)

 theorem localPairChainWitness_covector {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (x : EuclideanPlane) :
    (localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd).weakGrad x =
      planeCovectorGradient ((fderiv ℝ Φ (planePair (u x) (v x))).comp
        (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))) := by
  rw [weakPairDifferential_chain, planeCovectorGradient_inner]
  exact localPairChainWitness_gradient hU hUf hu hv Wu Wv hΦ hB hC hΦb hΦd x

end CircleDomainRigidity

end

end OAI
