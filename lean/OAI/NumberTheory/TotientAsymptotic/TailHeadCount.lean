import OAI.NumberTheory.TotientAsymptotic.HeadPrimeCount
import OAI.NumberTheory.TotientAsymptotic.OrderedPrimeProduct
import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBridge
import Mathlib.Order.Fin.Tuple

namespace OAI

/-! Counting distinct candidate integers by a finite sum over ordered tails. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma prime_tail_totient_weight {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i,(p i).Prime) (horder : StrictAnti p) :
    ((∏ i,p i).totient:ℝ)⁻¹=reciprocalShiftWeight p := by
  rw [ppt_totient_primeProduct p hp horder.injective]
  rfl

def tailHeadPairs {n : ℕ} (x : ℝ) (d : ℕ) (Q : Finset (Fin n → ℕ)) :
    Finset (Σ _p : Fin n → ℕ,ℕ) :=
  Q.sigma (fun p => primeInterval
    (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
    (x/((d*(∏ i,p i).totient:ℕ):ℝ)))

theorem tail_head_pair_count : ∀ᶠ x : ℝ in atTop,
    ∀ d : ℕ,0 < d → ∀ n : ℕ,∀ Q : Finset (Fin n → ℕ),
      (∀ p ∈ Q,(∀ i,(p i).Prime) ∧ StrictAnti p ∧
        Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ)) →
      (x/(4*d*Real.log x))*(∑ p ∈ Q,reciprocalShiftWeight p) ≤
        ((tailHeadPairs x d Q).card:ℝ) := by
  filter_upwards [head_prime_count_lower,eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro d hd n Q hQ
  have hcount (p) (hp : p ∈ Q) :
      (x/(4*d*Real.log x))*reciprocalShiftWeight p ≤
        ((primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
          (x/((d*(∏ i,p i).totient:ℕ):ℝ))).card:ℝ) := by
    obtain ⟨hprime,horder,hlog⟩ := hQ p hp
    have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hprime i).pos)
    have hφ := Nat.totient_pos.mpr hr
    have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd hφ
    have hh := hx _ hD hlog
    apply le_trans _ hh
    rw [←prime_tail_totient_weight p hprime horder,Nat.cast_mul]
    ring_nf
    exact le_rfl
  have hh := Finset.sum_le_sum hcount
  simpa only [tailHeadPairs,Finset.card_sigma,Nat.cast_sum,Finset.mul_sum] using hh

lemma ordered_head_product_injective {n : ℕ} {p q : Fin n → ℕ} {a b : ℕ}
    (hp : ∀ i,(p i).Prime) (hq : ∀ i,(q i).Prime) (ha : a.Prime) (hb : b.Prime)
    (hpo : StrictAnti p) (hqo : StrictAnti q)
    (hap : ∀ i,p i < a) (hbq : ∀ i,q i < b)
    (he : a*(∏ i,p i)=b*(∏ i,q i)) : a=b ∧ p=q := by
  have hpc : ∀ i : Fin (n+1),Nat.Prime ((Fin.cons a p : Fin (n+1) → ℕ) i) := by
    intro i
    refine Fin.cases ha (fun j => ?_) i
    simpa using hp j
  have hqc : ∀ i : Fin (n+1),Nat.Prime ((Fin.cons b q : Fin (n+1) → ℕ) i) := by
    intro i
    refine Fin.cases hb (fun j => ?_) i
    simpa using hq j
  have hpa : StrictAnti (Fin.cons a p) :=
    (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr ⟨hap,hpo⟩
  have hqa : StrictAnti (Fin.cons b q) :=
    (Fin.strictMono_cons (α:=OrderDual ℕ)).mpr ⟨hbq,hqo⟩
  have hh := ordered_prime_product_injective hpc hqc hpa hqa
    (by simpa only [Fin.prod_cons] using he)
  constructor
  · simpa only [Fin.cons_zero] using congrFun hh 0
  · funext i
    simpa only [Fin.cons_succ] using congrFun hh i.succ

end TotientAsymptotic

end

end OAI
