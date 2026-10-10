import OAI.NumberTheory.JointDickman.Amplification.CanonicalTypicalDensity
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalSieveScale

namespace OAI

/-! # A fixed logarithmic-ratio auxiliary band misses few integers -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_band_missing_bound : ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
    ∀ P Q R : ℝ, 2 ≤ P → P ≤ Q → 1 ≤ R → Real.log Q=R*Real.log P →
    ∀ (A N : ℕ) [NeZero N] (r : ℕ),
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A+j.val)) ≤
        C/R+Real.exp (2*(Real.log R+M))/(2:ℝ)^(2*r+1)+
        ((2*r+1:ℕ):ℝ)*2^(2*r)*Q^(4*r)/(N:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mrt_missing_band_probability
  obtain ⟨M,hM,hmass⟩ := mrt_prime_band_mertens
  refine ⟨C,M,hC,hM,?_⟩
  intro P Q R hP hPQ hR hrel A N _ r
  have hP0 : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR0 : 0 < R := by linarith
  have hlP : 0 < Real.log P := Real.log_pos (by linarith)
  have he : Real.log (Real.log Q)-Real.log (Real.log P)=Real.log R := by
    rw [hrel,Real.log_mul hR0.ne' hlP.ne']
    ring
  have hm : (∑ p ∈ mrtPrimeBand P Q,1/(p:ℝ)) ≤ Real.log R+M := by
    have hh := (abs_le.mp (hmass P Q hP hPQ)).2
    rw [he] at hh
    linarith
  have hmain : C*Real.log P/Real.log Q=C/R := by
    rw [hrel]
    field_simp
  have hb : ((mrtPrimeBand P Q).card:ℝ)*Q+1 ≤ 2*Q^2 := by
    have hc := mrt_prime_band_card_le P Q (by linarith)
    have hh := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ Q)
    nlinarith [sq_nonneg (Q-1)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ((mrtPrimeBand P Q).card:ℝ)*Q+1) hb (2*r)
  have hpow' : (((mrtPrimeBand P Q).card:ℝ)*Q+1)^(2*r) ≤ 2^(2*r)*Q^(4*r) := by
    convert hpow using 1
    rw [mul_pow,← pow_mul]
    congr 2
    omega
  have hh := hbound P Q hP hPQ A N r
  rw [hmain] at hh
  apply hh.trans
  apply add_le_add
  · exact add_le_add le_rfl
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  · have hp := mul_le_mul_of_nonneg_left hpow'
      (by positivity : 0 ≤ 1/(N:ℝ)*((2*r+1:ℕ):ℝ))
    convert hp using 1; ring

end JointDickman

end OAI
