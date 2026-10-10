import OAI.Analysis.CircleDomains.Sobolev.WeakCovectorGradient

namespace OAI

/-! The quantitative saved-barrier estimate for the actual joint
Sobolev witness, retaining the separate exceptional-support term. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_barrier_estimate {U : Set EuclideanPlane} (hU : IsOpen U)
    (hUf : volume U ≠ ∞) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (Wu : DeGiorgi.MemW1pWitness 2 u U) (Wv : DeGiorgi.MemW1pWitness 2 v U)
    (S : Set EuclideanPlane) (hS : MeasurableSet S)
    (H : EuclideanPlane → EuclideanPlane) (DH : EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hbound : ∀ y, ‖fderiv ℝ Φ y‖ ≤ M₁)
    (hlip : ∀ y z, ‖fderiv ℝ Φ y-fderiv ℝ Φ z‖ ≤ M₂*‖y-z‖)
    (hclose : ∀ x ∉ S, ‖planePair (u x) (v x)-H x‖ ≤ e)
    (hD : AEStronglyMeasurable (fun x =>
      (fderiv ℝ Φ (planePair (u x) (v x))).comp (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-
      (fderiv ℝ Φ (H x)).comp (DH x)) (volume.restrict U))
    (herror : MemLp (fun x => weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)-DH x)
      2 (volume.restrict U)) (hH : MemLp DH 2 (volume.restrict U)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => Φ (planePair (u x) (v x))) U,
      MemLp (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
        2 (volume.restrict U) ∧
      (eLpNorm (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
        2 (volume.restrict U)).toReal ≤
      M₁*(eLpNorm (fun x => ‖weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)-DH x‖)
        2 (volume.restrict U)).toReal +
      (M₂*e)*(eLpNorm (fun x => ‖DH x‖) 2 (volume.restrict U)).toReal +
      (2*M₁)*(eLpNorm (S.indicator (fun x => ‖DH x‖)) 2 (volume.restrict U)).toReal := by
  let W := localPairChainWitness hU hUf hu hv Wu Wv hΦ hB hM₁ hΦb hbound
  let D := fun x => (fderiv ℝ Φ (planePair (u x) (v x))).comp
    (weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x))-(fderiv ℝ Φ (H x)).comp (DH x)
  obtain ⟨hLp, hn⟩ := barrier_L2_error S hS (fun x => planePair (u x) (v x)) H
    (fun x => weakPairDifferential (Wu.weakGrad x) (Wv.weakGrad x)) DH Φ
    hM₁ hM₂ he hbound hlip hclose hD herror hH
  have hid (x : EuclideanPlane) :
      W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)) =
        planeCovectorGradient (D x) := by
    rw [planeCovectorGradient_sub]
    rw [localPairChainWitness_covector hU hUf hu hv Wu Wv hΦ hB hM₁ hΦb hbound]
  have hnorm (x : EuclideanPlane) :
      ‖W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x))‖ = ‖D x‖ := by
    rw [hid, planeCovectorGradient_norm]
  have hgrad : MemLp (fun x => W.weakGrad x-planeCovectorGradient ((fderiv ℝ Φ (H x)).comp (DH x)))
      2 (volume.restrict U) := by
    apply hLp.of_le
    · exact (continuous_planeCovectorGradient.comp_aestronglyMeasurable hD).congr
        (Eventually.of_forall (fun x => (hid x).symm))
    · exact Eventually.of_forall (fun x => (hnorm x).le)
  refine ⟨W,hgrad,?_⟩
  have hnorms := eLpNorm_congr_norm_ae hgrad.aestronglyMeasurable hLp.aestronglyMeasurable (Eventually.of_forall hnorm) (p := 2)
  rw [hnorms]
  exact hn

end CircleDomainRigidity

end

end OAI
