import OAI.Analysis.CircleDomains.Sobolev.SavedBarrierEnergy
import OAI.Analysis.CircleDomains.Sobolev.BarrierEnergyAssembly

namespace OAI

/-! Positive energy slack yields a positive perturbation tolerance for a
fixed saved barrier, by quantitative comparison. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_saved_barrier_energy_tolerance
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUf : volume U ≠ (⊤ : ℝ≥0∞))
    {x y : EuclideanPlane → ℝ} (hx : Continuous x) (hy : Continuous y)
    (Wx : DeGiorgi.MemW1pWitness 2 x U) (Wy : DeGiorgi.MemW1pWitness 2 y U)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B M₁ M₂ η : ℝ} (hB : 0 ≤ B) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hΦb : ∀ z, ‖Φ z‖ ≤ B) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ M₁)
    (hlip : ∀ z w, ‖fderiv ℝ Φ z-fderiv ℝ Φ w‖ ≤ M₂*‖z-w‖)
    (V : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (x z) (y z))) U)
    (hV : (eLpNorm V.weakGrad 2 (volume.restrict U)).toReal < η) :
    ∃ t > 0, ∀ (p q : EuclideanPlane → ℝ), Continuous p → Continuous q →
      ∀ (Wp : DeGiorgi.MemW1pWitness 2 p U) (Wq : DeGiorgi.MemW1pWitness 2 q U),
      (∀ z ∈ U, ‖planePair (p z) (q z)-planePair (x z) (y z)‖ ≤ t) →
      (eLpNorm (fun z => Wp.weakGrad z-Wx.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      (eLpNorm (fun z => Wq.weakGrad z-Wy.weakGrad z) 2 (volume.restrict U)).toReal ≤ t →
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun z => Φ (planePair (p z) (q z))) U,
        (eLpNorm W.weakGrad 2 (volume.restrict U)).toReal < η := by
  let N := (eLpNorm (fun z => weakPairDifferential (Wx.weakGrad z) (Wy.weakGrad z))
    2 (volume.restrict U)).toReal
  let C := 2*M₁+M₂*N+1
  have hC : 0 < C := by dsimp only [C,N]; positivity
  let t := (η-(eLpNorm V.weakGrad 2 (volume.restrict U)).toReal)/C
  have ht : 0 < t := div_pos (sub_pos.mpr hV) hC
  have heq : t*C = η-(eLpNorm V.weakGrad 2 (volume.restrict U)).toReal := div_mul_cancel₀ _ hC.ne'
  refine ⟨t,ht,?_⟩
  intro p q hp hq Wp Wq hclose hpE hqE
  obtain ⟨W,hW⟩ := saved_barrier_energy_stability hU hUf hp hq hx hy Wp Wq Wx Wy
    hΦ hB hM₁ hM₂ ht.le hΦb hbound hlip hclose V
  have herr : (eLpNorm (fun z => W.weakGrad z-V.weakGrad z) 2 (volume.restrict U)).toReal ≤
      M₁*(t+t)+(M₂*t)*N := hW.trans (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add hpE hqE) hM₁) le_rfl)
  have hnorm := (l2_norm_le_error_add W.weakGrad_memLp V.weakGrad_memLp).trans
    (add_le_add herr le_rfl)
  have he : M₁*(t+t)+(M₂*t)*N = t*C-t := by dsimp only [C]; ring
  rw [he,heq] at hnorm
  exact ⟨W,by linarith⟩

end CircleDomainRigidity

end

end OAI
