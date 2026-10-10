import OAI.NumberTheory.TotientAsymptotic.AbnormalIntervalMass
import OAI.NumberTheory.TotientAsymptotic.SmallFactorTail

namespace OAI

/-! Both failures of prime normality have small reciprocal cofactor mass. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def AbnormalCofactor (S x : ℝ) (n : ℕ) : Prop :=
  2*B S-1 < (omegaIn n 1 S:ℝ) ∨ ∃ U T : ℝ,
    S ≤ U ∧ U < T ∧ T ≤ x ∧
    Real.sqrt (B S*B T)-1 ≤ |(omegaIn n U T:ℝ)-(B T-B U)|

 theorem abnormal_cofactor_mass : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → 4 ≤ B S →
    ∀ N : ℕ, Real.exp 1 ≤ N → 1 ≤ B N → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ AbnormalCofactor S N n) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hsmall⟩ := small_factor_tail_mass
  obtain ⟨D,hD,hinterval⟩ := abnormal_interval_mass
  refine ⟨C+D,by positivity,?_⟩
  intro S hS hBS N hN hBN Q hQ
  let Q₁ := Q.filter (fun n => 2*B S-1 < (omegaIn n 1 S:ℝ))
  let Q₂ := Q.filter (fun n => ¬2*B S-1 < (omegaIn n 1 S:ℝ))
  have hN2 : 2 ≤ N := by
    have he := Real.add_one_le_exp (1:ℝ)
    have hh : (2:ℝ) ≤ N := by linarith
    exact_mod_cast hh
  have hs := hsmall N hN2 S hS.le (by linarith) Q₁ (by
    intro n hn
    obtain ⟨hn,hb⟩ := Finset.mem_filter.mp hn
    exact ⟨(hQ n hn).1,(hQ n hn).2.1,hb⟩)
  have hi := hinterval S N (by linarith) hBS hN hBN Q₂ (by
    intro n hn
    obtain ⟨hn,hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0,hnN,hbad⟩ := hQ n hn
    refine ⟨hn0,by exact_mod_cast hnN,?_⟩
    exact hbad.resolve_left hb)
  have heq : (∑ n ∈ Q,(n:ℝ)⁻¹) = (∑ n ∈ Q₁,(n:ℝ)⁻¹)+(∑ n ∈ Q₂,(n:ℝ)⁻¹) :=
    (Finset.sum_filter_add_sum_filter_not Q (fun n => 2*B S-1 < (omegaIn n 1 S:ℝ)) _).symm
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrpow : 0 < (Real.log S)^(-1/6:ℝ) := Real.rpow_pos_of_pos hlogS _
  have hscale : 1 ≤ (B N)^2 := by nlinarith
  have hs' : C*Real.log N*(Real.log S)^(-1/6:ℝ) ≤
      C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hscale
      (show 0 ≤ C*Real.log N*(Real.log S)^(-1/6:ℝ) by positivity)
    nlinarith
  rw [heq]
  calc
    _ ≤ C*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ)+
        D*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ) := add_le_add (hs.trans hs') hi
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
