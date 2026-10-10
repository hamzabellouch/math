import OAI.Analysis.CircleDomains.Sobolev.SobolevRangeBound
import OAI.Analysis.CircleDomains.Topology.BoundedCompactCutoff

namespace OAI

/-! A range bound on the smooth region propagates across the set where
the weak gradient is zero. Cutoff transitions lie in the smooth region. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem localized_sobolev_range
    {f : EuclideanPlane → ℝ} {G : EuclideanPlane → EuclideanPlane}
    (hm : AEStronglyMeasurable f volume) (hf : ∀ x, f x ∈ Icc 0 1)
    (hG : ∀ i : Fin 2, MemLp (fun x => G x i) 2 volume)
    (hw : DeGiorgi.HasWeakGrad G f univ)
    {D : Set EuclideanPlane}
    (hz : ∀ i : Fin 2, ∀ᵐ x ∂volume, x ∉ D → G x i = 0)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : HasCompactSupport η) (hηunit : ∀ x, η x ∈ Icc 0 1)
    (hηd : ∀ x, x ∉ D → fderiv ℝ η x = 0)
    {b : ℝ} (hb : 0 ≤ b)
    (hrange : ∀ᵐ x ∂volume, x ∈ D → η x ≠ 0 → f x ≤ b) :
    ∀ᵐ x ∂volume, η x = 1 → f x ≤ b := by
  let W := boundedCompactCutoffWitness hm hf hG hw hη hs
  have hunit (x : EuclideanPlane) : η x * f x ∈ Icc 0 1 :=
    ⟨mul_nonneg (hηunit x).1 (hf x).1,
      (mul_le_mul (hηunit x).2 (hf x).2 (hf x).1 zero_le_one).trans_eq (one_mul 1)⟩
  have hzero (i : Fin 2) : ∀ᵐ x ∂volume,
      b < η x * f x → W.weakGrad x i = 0 := by
    filter_upwards [hz i, hrange] with x hx hr hex
    have hηne : η x ≠ 0 := by
      intro h
      rw [h, zero_mul] at hex
      exact (not_lt_of_ge hb) hex
    have hfb : b < f x := hex.trans_le (by
      calc η x * f x ≤ 1 * f x := mul_le_mul_of_nonneg_right (hηunit x).2 (hf x).1
           _ = f x := one_mul _)
    have hout : x ∉ D := fun hin => (not_lt_of_ge (hr hin hηne)) hfb
    change η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * f x = 0
    simp only [hx hout, hηd x hout, zero_apply, mul_zero, zero_mul, add_zero]
  have hbound := ae_le_of_compact_sobolev_gradient_zero_above W hs.mul_right hunit hb hzero
  filter_upwards [hbound] with x hx hηx
  simpa only [hηx, one_mul] using hx

end CircleDomainRigidity

end

end OAI
