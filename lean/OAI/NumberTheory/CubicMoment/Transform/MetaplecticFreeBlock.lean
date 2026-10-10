import OAI.NumberTheory.CubicMoment.Transform.MetaplecticFreeMean
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Fixed supported parameters only rescale the positive rational
frequencies of the free primary polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_scaled_free_norm (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b) (v : Eisenstein → ℂ)
    {c : ℝ} (hc : 0 < c) (ℓ : ℤ) (t : ℝ) :
    ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase t (c*norm b)‖ =
      ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase t (norm b)‖ := by
  have he : (∑ b ∈ S, v b*theta ℓ b*mellinPhase t (c*norm b)) =
      mellinPhase t c*(∑ b ∈ S, v b*theta ℓ b*mellinPhase t (norm b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [mellinPhase_mul_pos t hc (norm_pos_of_ne_zero (primary_ne_zero (hS b hb)))]
    ring
  rw [he,norm_mul,mellinPhase_norm,one_mul]

theorem metaplectic_scaled_free_meanAbsolute {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : Finset Eisenstein), (∀ b ∈ S, primary b) →
      ∀ (v : Eisenstein → ℂ) (L K T u c : ℝ) (ℓ : ℤ),
      1 ≤ L → 0 ≤ K → 0 < T → 0 < c →
      (∀ b ∈ S, L/2 ≤ norm b ∧ norm b ≤ L) →
      (∀ b ∈ S, ‖v b‖^2 ≤ K^2/norm b) →
      (∫ t in T..2*T, ‖∑ b ∈ S, v b*theta ℓ b*mellinPhase (t+u) (c*norm b)‖)/T ≤
        Real.sqrt (C*D)*L^(ε/2)*K*(1+Real.sqrt (2*L/T)) := by
  obtain ⟨D,hD,hbound⟩ := metaplectic_free_meanAbsolute_sq hε hMV hC
  refine ⟨D,hD,?_⟩
  intro S hS v L K T u c ℓ hL hK hT hc hsize hv
  simp_rw [metaplectic_scaled_free_norm S hS v hc]
  have hb := hbound S hS v L K T u ℓ hL hT hsize hv
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hq : 0 ≤ 2*L/T := div_nonneg (by positivity) hT.le
  have hpow : (L^(ε/2))^2 = L^ε := by
    rw [←Real.rpow_mul_natCast hLp.le]
    congr 1
    norm_num
  have hs : (Real.sqrt (C*D)*L^(ε/2)*K)^2 = C*D*L^ε*K^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hC hD.le),hpow]
  have hroot : 1+2*L/T ≤ (1+Real.sqrt (2*L/T))^2 := by
    nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg (2*L/T)]
  apply le_of_sq_le_sq _ (by positivity)
  apply hb.trans
  rw [mul_pow,hs]
  calc
    _ = (C*D*L^ε*K^2)*(1+2*L/T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)

end CubicFirstMoment

end

end OAI
