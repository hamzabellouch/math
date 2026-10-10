import OAI.Analysis.CircleDomains.Sobolev.LocalWeakBarrierBound

namespace OAI

/-! Quantitative stability of a saved barrier under changes to its two
source tests. Its Sobolev witness is retained. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem saved_barrier_energy_stability
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ ∞)
    {p q x y : EuclideanPlane → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hx : Continuous x) (hy : Continuous y)
    (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ e : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (he : 0 ≤ e)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (hclose : ∀ z ∈ U, ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ e)
    (V : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (x z) (y z))) U) :
    ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
      (eLpNorm (fun z => W.weakGrad z-V.weakGrad z) 2 (volume.restrict U)).toReal ≤
        M₁*((eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal+
          (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal)+
        (M₂*e)*(eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
          2 (volume.restrict U)).toReal := by
  let V' := localPairChainWitness hU hUf hx hy Wx Wy hΦ hB hM₁ hΦb hbound
  have hv := V.ae_eq hU V'
  obtain ⟨W,hW,hn⟩ := local_weak_barrier_bound (S := ∅) hU hUf MeasurableSet.empty hp hq Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ he hΦb hbound hlip (fun z hz _ => hclose z hz)
  have heq : (fun z => W.weakGrad z-V.weakGrad z) =ᵐ[volume.restrict U]
      (fun z => W.weakGrad z-planeCovectorGradient
        ((fderiv ℝ Φ (planePair (x z) (y z))).comp
          (weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z)))) := by
    filter_upwards [hv] with z hz
    rw [hz, localPairChainWitness_covector hU hUf hx hy Wx Wy hΦ hB hM₁ hΦb hbound]
  refine ⟨W,?_⟩
  rw [eLpNorm_congr_ae heq]
  simpa only [indicator_empty, eLpNorm_fun_zero, ENNReal.toReal_zero, mul_zero, add_zero] using hn

end CircleDomainRigidity

end

end OAI
