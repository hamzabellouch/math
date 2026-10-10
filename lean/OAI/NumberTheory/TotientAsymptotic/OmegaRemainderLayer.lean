import OAI.NumberTheory.TotientAsymptotic.RestrictedPrimeLayer
import OAI.NumberTheory.TotientAsymptotic.OmegaPrimeMass
import OAI.NumberTheory.TotientAsymptotic.OmegaFailureReduction

namespace OAI

/-! The exceptional shifted-prime moment applied to actual remainder layers. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def omegaExceptionalRemainders (x : ℝ) (H i j : ℕ) : Finset (RemainderDatum (L x H)) :=
  (basicRemainderFinset x H).filter (fun η =>
    fordBandScale x i/(2*((m x-i : ℕ) : ℝ)^9) < ((remainderPrime η j-1).primeFactorsList.length : ℝ))

lemma collision_last_scale_ge_two : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, 2 ≤ fordBandScale x (collisionLastIndex x i) := by
  filter_upwards [eventually_collision_indices,eventually_ge_atTop 8] with H hind hH
  filter_upwards [ford_band_lower,m_tendsto.eventually (eventually_ge_atTop H)] with x hl hm
  intro i hi
  obtain ⟨hHi,hJ,hk⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hkm : collisionLastIndex x i < m x := by unfold collisionLastIndex; omega
  have hrem : 4 ≤ m x-collisionLastIndex x i := by unfold collisionLastIndex; omega
  have hremR : (4 : ℝ) ≤ (m x-collisionLastIndex x i : ℕ) := by exact_mod_cast hrem
  have hnum : 2 ≤ (99/100 : ℝ)*lam*(m x-collisionLastIndex x i : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hremR (show 0 ≤ (99/100 : ℝ)*lam by have := lam_pos; positivity)
    nlinarith [collision_lambda_bounds.1]
  have hpow : rho^(m x-collisionLastIndex x i) ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  apply le_trans _ (hl _ hkm)
  apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
  linarith

theorem omega_remainder_layer_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ i j : ℕ, i ≤ R x H → collisionLastIndex x i < j → j ≤ L x H →
      let b := fordBandScale x i
      let d := fordBandScale x (collisionLastIndex x i)
      (∑ η ∈ omegaExceptionalRemainders x H i j, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (C*Real.exp (6*d-b/(2*((m x-i : ℕ) : ℝ)^9)*Real.log (3/2)))*
        (D*(2*b+2))^(L x H-i-1) := by
  obtain ⟨C,hC,hbad⟩ := omega_prime_mass hmertens
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [restricted_prime_layer_mass hbox hren,collision_last_scale_ge_two,
    ford_band_polynomial_lower 1,eventually_ge_atTop 2] with H hmass hcut hpoly hH
  filter_upwards [hmass,hcut,hpoly,basic_suffix_discard_bound,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hm hd hp hbound hHm hBx
  intro i j hi hj hjL
  dsimp only
  let b := fordBandScale x i
  let d := fordBandScale x (collisionLastIndex x i)
  let T := b/(2*((m x-i : ℕ) : ℝ)^9)
  let S := omegaExceptionalRemainders x H i j
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hb : 2 ≤ b := by
    have hh := hp i him hHi
    simp only [pow_one] at hh
    exact (show (2 : ℝ) ≤ (m x-i : ℕ) by exact_mod_cast hH.trans hHi).trans hh
  have hd2 : 2 ≤ d := hd i hi
  have hki : i ≤ collisionLastIndex x i := by unfold collisionLastIndex; omega
  have hkm : collisionLastIndex x i < m x := by unfold L at hjL; omega
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hU : ∀ η ∈ S, ∀ l ∈ Finset.Icc (i+1) (L x H),
      remainderPrime η l ∈ Nat.primesLE (discardPrimeBound b) := by
    intro η hη l hl
    obtain ⟨hli,hlL⟩ := Finset.mem_Icc.mp hl
    exact hbound H i l (by omega) (by omega) hlL him hb η (hS η hη)
  have hV : ∀ η ∈ S, remainderPrime η j ∈ omegaExceptionalPrimes (discardPrimeBound d) T := by
    intro η hη
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp hη).2.le⟩
    exact hbound H (collisionLastIndex x i) j (by omega) hj.le hjL hkm hd2 η (hS η hη)
  have hh := hm S i j hi (by omega) hjL _ _ hS hU hV
  have hbadmass := hbad d hd2 T
  have hgoodmass : (∑ p ∈ Nat.primesLE (discardPrimeBound b), ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(2*b+2) := by
    obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
    exact (hall _ (by omega) hBN).trans (mul_le_mul_of_nonneg_left (by linarith) hD.le)
  apply hh.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hbadmass
      (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (G_pos hBx _).le)
  · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hgoodmass _
  · positivity
  · exact mul_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (G_pos hBx _).le)
      (by positivity)

end TotientAsymptotic

end

end OAI
