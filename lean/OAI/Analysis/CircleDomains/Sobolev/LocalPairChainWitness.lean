import OAI.Analysis.CircleDomains.Sobolev.LocalPairChainRule

namespace OAI

/-! A genuine local Sobolev witness for each smooth saved barrier
composed with the two actual source coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def localPairChainWitness {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) :
    DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u x) (v x))) U where
  memLp := by
    let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUf
    exact MemLp.of_bound ((hΦ.continuous.comp (continuous_planePair hu hv)).aestronglyMeasurable.restrict) B
      (Eventually.of_forall (fun x => hΦb _))
  weakGrad := fun x => WithLp.toLp 2 (fun i =>
    fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
    fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
  weakGrad_component_memLp := by
    intro i
    have hcoef (j : Fin 2) : Continuous (fun x => fderiv ℝ Φ
        (planePair (u x) (v x)) (EuclideanSpace.single j 1)) :=
      ((hΦ.continuous_fderiv one_ne_zero).comp (continuous_planePair hu hv)).clm_apply continuous_const
    have hbound (j : Fin 2) (x : EuclideanPlane) :
        ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)‖ ≤ C := by
      have h := (fderiv ℝ Φ (planePair (u x) (v x))).le_opNorm (EuclideanSpace.single j 1)
      have hh : ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)‖ ≤
          ‖fderiv ℝ Φ (planePair (u x) (v x))‖ := by
        simpa only [PiLp.norm_single, norm_one, mul_one] using h
      exact hh.trans (hΦd _)
    have hmul (j : Fin 2) {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict U)) :
        MemLp (fun x => fderiv ℝ Φ (planePair (u x) (v x))
          (EuclideanSpace.single j 1)*g x) 2 (volume.restrict U) := by
      apply hg.of_le_mul (c := C) ((hcoef j).aestronglyMeasurable.restrict.mul hg.aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        change ‖fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single j 1)*g x‖ ≤ C*‖g x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound j x) (norm_nonneg _)
    exact (hmul 0 (Wu.weakGrad_component_memLp i)).add (hmul 1 (Wv.weakGrad_component_memLp i))
  isWeakGrad := local_pair_weak_chain hU hu hv Wu Wv hΦ hB hC hΦb hΦd

end CircleDomainRigidity

end

end OAI
