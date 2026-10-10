import OAI.Analysis.CircleDomains.Sobolev.WeakBarrierMeasurability

namespace OAI

/-! The local three-term barrier bound from four actual scalar Sobolev
witnesses. Measurability and joint differential integrability are derived. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_weak_barrier_bound
    {U S : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    (hS : MeasurableSet S) {p q x y : EuclideanPlane → ℝ}
    (hp : Continuous p) (hq : Continuous q)
    (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (hclose : ∀ z ∈ U, z ∉ S → ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ e) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
      MemLp (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) 2 (volume.restrict U) ∧
      (eLpNorm (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) 2 (volume.restrict U)).toReal ≤
      M₁*((eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal+
        (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal)+
      (M₂*e)*(eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
        2 (volume.restrict U)).toReal+
      (2*M₁)*(eLpNorm (S.indicator (fun z => ‖weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)‖))
        2 (volume.restrict U)).toReal := by
  let T := S ∪ Uᶜ
  let H := fun z => planePair (x z) (y z)
  let DH := fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)
  have hH : AEStronglyMeasurable H (volume.restrict U) :=
    (continuous_planePair continuous_fst continuous_snd).comp_aestronglyMeasurable
      (Wx.memLp.aestronglyMeasurable.prodMk Wy.memLp.aestronglyMeasurable)
  have hDH := (weakPairDifferential_memLp Wx.weakGrad_memLp Wy.weakGrad_memLp).1
  have herror := weakPairDifferential_error_memLp
    (Wp.weakGrad_memLp.sub Wx.weakGrad_memLp) (Wq.weakGrad_memLp.sub Wy.weakGrad_memLp)
  have ht : ∀ z ∉ T, ‖planePair (p z) (q z)-H z‖ ≤ e := by
    intro z hz
    have hzU : z ∈ U := not_not.mp (fun h => hz (Or.inr h))
    exact hclose z hzU (fun h => hz (Or.inl h))
  obtain ⟨W,hW,hn⟩ := local_sobolev_barrier_estimate hU hUf hp hq Wp Wq T
    (hS.union hU.measurableSet.compl) H DH hΦ hB hM₁ hM₂ he hΦb hbound hlip ht
    (joint_barrier_differential_measurable hp hq Wp Wq hH hDH.aestronglyMeasurable hΦ)
    herror.1 hDH
  have hi : eLpNorm (T.indicator (fun z => ‖DH z‖)) 2 (volume.restrict U) =
      eLpNorm (S.indicator (fun z => ‖DH z‖)) 2 (volume.restrict U) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    by_cases hs : z ∈ S
    · simp [T, hs]
    · have ht : z ∉ T := fun h => h.elim hs (fun h => h hz)
      simp only [indicator_of_notMem hs, indicator_of_notMem ht]
  rw [hi, eLpNorm_norm _ herror.1.aestronglyMeasurable,
    eLpNorm_norm _ hDH.aestronglyMeasurable] at hn
  refine ⟨W,hW,hn.trans ?_⟩
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left herror.2 hM₁) le_rfl) le_rfl

end CircleDomainRigidity

end

end OAI
