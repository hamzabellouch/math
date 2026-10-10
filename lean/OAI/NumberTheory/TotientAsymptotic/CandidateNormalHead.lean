import OAI.NumberTheory.TotientAsymptotic.CandidateUpperCount
import OAI.NumberTheory.TotientAsymptotic.SubpowerCandidate
import OAI.NumberTheory.TotientAsymptotic.NormalHeadCount
import OAI.NumberTheory.TotientAsymptotic.NormalityInput

namespace OAI

/-! Normality exclusion for the head prime on each actual tail interval. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def nonNormalHeadPairs {n : ℕ} (x S : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) :
    Finset (Σ _p : Fin n → ℕ,ℕ) :=
  Q.sigma (fun p => (primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
    (x/((d*(∏ i,p i).totient:ℕ):ℝ))).filter (fun q => ¬IsNormalPrime S q))

theorem non_normal_head_pair_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ S : ℝ,2 < S → ∀ d : ℕ,0 < d →
      ∀ n : ℕ,∀ Q : Finset (Fin n → ℕ),
      (∀ p ∈ Q,(∀ i,(p i).Prime) ∧ StrictAnti p ∧
        Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ)) →
      ((nonNormalHeadPairs x S d Q).card:ℝ) ≤
        (C*x/(d*Real.log x))*(1+B x)^5*(Real.log S)^(-1/6:ℝ)*
          (∑ p ∈ Q,reciprocalShiftWeight p) := by
  obtain ⟨C,hC,hcount⟩ := non_normal_head_count fordLemma26Input
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,subpower_head_lower (by norm_num : (0:ℝ)<1/10),
    eventually_gt_atTop (1:ℝ)] with x hx hhead hx1
  intro S hS d hd n Q hQ
  have hbound (p) (hp : p ∈ Q) :
      (((primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
        (x/((d*(∏ i,p i).totient:ℕ):ℝ))).filter
          (fun q => ¬IsNormalPrime S q)).card:ℝ) ≤
      ((C*x/(d*Real.log x))*(1+B x)^5*(Real.log S)^(-1/6:ℝ))*
        reciprocalShiftWeight p := by
    obtain ⟨hpr,ho,hlog⟩ := hQ p hp
    let D : ℕ := d*(∏ i,p i).totient
    have hDp : 0 < D := Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hpr i).pos)))
    have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hDp
    have hD0 : (0:ℝ) < D := by exact_mod_cast hDp
    have hb := hx S hS D hDp
      ((primeInterval (x/(2*(D:ℝ))) (x/D)).filter (fun q => ¬IsNormalPrime S q)) (by
        intro q hq
        obtain ⟨hq,hnormal⟩ := Finset.mem_filter.mp hq
        obtain ⟨hprime,_,hqup⟩ := mem_head_prime_interval (zero_lt_one.trans hx1).le hD0 hq
        have hlow := hhead (D:ℝ) hD1 hlog q hq
        have hmul := (le_div_iff₀ hD0).mp hqup
        have hqm : ((q-1:ℕ):ℝ)*(D:ℝ) ≤ x := by
          rw [Nat.cast_sub hprime.one_le,Nat.cast_one]
          nlinarith only [hmul,hD0]
        refine ⟨hprime,?_,?_,hnormal⟩
        · norm_num only [show (1:ℝ)-1/10=9/10 by norm_num] at hlow
          exact hlow.le
        · exact_mod_cast hqm)
    apply hb.trans_eq
    dsimp [D]
    rw [←prime_tail_totient_weight p hpr ho,Nat.cast_mul]
    ring
  have hh := Finset.sum_le_sum hbound
  simpa only [nonNormalHeadPairs,Finset.card_sigma,Nat.cast_sum,Finset.mul_sum] using hh

end TotientAsymptotic

end

end OAI
