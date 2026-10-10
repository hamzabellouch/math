import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount
import OAI.NumberTheory.TotientAsymptotic.NormalDiscardDecay
import OAI.NumberTheory.TotientAsymptotic.ExtractTail

namespace OAI

/-! A residual factor-count failure forces an exceptional shifted prime
strictly after the collision cutoff. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma basic_cofactor_log_small : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      Real.log (η.cofactor : ℝ) ≤ 2*H := by
  filter_upwards [cofactor_envelope_le_self (2*(lam/rho)),eventually_ge_atTop 2] with H hcost hH
  filter_upwards [theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H)] with x hs hm
  intro η hη
  have hc := (witness_cofactor_bound hs (extractTail_isWitness hη (P_lt_self hH) hm)).2
  have hT : 0 ≤ (2*(lam/rho))*cofactorScale H :=
    mul_nonneg (mul_nonneg (by norm_num) (div_pos lam_pos rho_pos).le) (cofactorScale_nonneg H)
  have hb := (exponentialCofactorCap_bounds hT).2
  have he : exponentialCofactorCap ((2*(lam/rho))*cofactorScale H)=tailCofactorBound H := by
    unfold exponentialCofactorCap tailCofactorBound cofactorScale
    congr 3
    ring
  rw [he] at hb
  have hpos : (0 : ℝ) < η.cofactor := by exact_mod_cast hη.1
  calc
    _ ≤ Real.log (tailCofactorBound H : ℝ) := Real.log_le_log hpos (by exact_mod_cast hc)
    _ ≤ 2*Real.exp ((2*(lam/rho))*cofactorScale H) := hb
    _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by norm_num)

lemma omega_failure_large_shift : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      fordBandScale x i/((m x-i : ℕ) : ℝ)^8 < (collisionResidual η i).primeFactorsList.length →
      ∃ j ∈ Finset.Icc (collisionLastIndex x i+1) (L x H),
        fordBandScale x i/(2*((m x-i : ℕ) : ℝ)^9) <
          ((remainderPrime η j-1).primeFactorsList.length : ℝ) := by
  filter_upwards [basic_cofactor_log_small,eventually_collision_indices,ford_band_polynomial_lower 10,
    P_tendsto.eventually (eventually_ge_atTop 1),eventually_ge_atTop 10] with H hcof hind hpoly hP hH
  filter_upwards [hcof,hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hc hp hm
  intro i hi η hη hfail
  obtain ⟨hHi,_,hk⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hL : L x H < m x := by unfold L; omega
  let h := m x-i
  let b := fordBandScale x i
  let k := collisionLastIndex x i
  have hh : (10 : ℝ) ≤ h := by exact_mod_cast hH.trans hHi
  have hh0 : (0 : ℝ) < h := by linarith
  have hb : (h : ℝ)^10 ≤ b := hp i him hHi
  have hb0 : 0 ≤ b := (pow_nonneg hh0.le _).trans hb
  have hcofBound : 2*Real.log (η.cofactor : ℝ)+1 ≤ b/(2*(h : ℝ)^8) := by
    have hl := hc η hη
    have hHh : (H : ℝ) ≤ h := by exact_mod_cast hHi
    have hhsmall : 4*(h : ℝ)+1 ≤ (h : ℝ)^2/2 := by nlinarith
    apply (le_div_iff₀ (by positivity : 0 < 2*(h : ℝ)^8)).mpr
    calc
      _ ≤ (4*(h : ℝ)+1)*(2*(h : ℝ)^8) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ ((h : ℝ)^2/2)*(2*(h : ℝ)^8) := mul_le_mul_of_nonneg_right hhsmall (by positivity)
      _ = (h : ℝ)^10 := by ring
      _ ≤ b := hb
  by_contra hn
  push Not at hn
  have hsum : (∑ j ∈ Finset.Icc (k+1) (L x H),
      ((remainderPrime η j-1).primeFactorsList.length : ℝ)) ≤ b/(2*(h : ℝ)^8) := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc (k+1) (L x H), b/(2*(h : ℝ)^9) :=
        Finset.sum_le_sum (fun j hj => hn j hj)
      _ = ((L x H-k : ℕ) : ℝ)*(b/(2*(h : ℝ)^9)) := by simp
      _ ≤ (h : ℝ)*(b/(2*(h : ℝ)^9)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show L x H-k ≤ h by dsimp [h,k,collisionLastIndex]; unfold L; omega)
      _ = _ := by field_simp
  have hbcount := basic_suffix_factor_count hη hL hk
  change ((suffixPreimage η k).totient.primeFactorsList.length : ℝ) ≤
    2*Real.log (η.cofactor : ℝ)+1+
      ∑ j ∈ Finset.Icc (k+1) (L x H), ((remainderPrime η j-1).primeFactorsList.length : ℝ) at hbcount
  change b/(h : ℝ)^8 < ((suffixPreimage η k).totient.primeFactorsList.length : ℝ) at hfail
  have he : b/(2*(h : ℝ)^8)+b/(2*(h : ℝ)^8)=b/(h : ℝ)^8 := by ring
  linarith

end TotientAsymptotic

end

end OAI
