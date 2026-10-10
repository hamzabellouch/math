import OAI.NumberTheory.TotientAsymptotic.TailHeadCount

namespace OAI

/-! Upper counting for restrictions on the tail of a head-prime candidate. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma head_prime_count_upper : ∀ᶠ x : ℝ in atTop,∀ D : ℝ,1 ≤ D →
    Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      ((primeInterval (x/(2*D)) (x/D)).card:ℝ) ≤ x/(D*Real.log x) := by
  filter_upwards [prime_interval_uniform primeNumberTheoremInput
    (a:=1/2) (b:=1) (ε:=1/4) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with x hx hx1
  intro D hD hlog
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hhalf : (1/2:ℝ)*x/D=x/(2*D) := by ring
  have hlu : x/(2*D) ≤ x/D := by
    rw [←hhalf]
    apply div_le_div_of_nonneg_right _ hD0.le
    linarith only [hx0]
  have hh := hx D (x/(2*D)) (x/D) hD hlog
    hhalf.le (hhalf.le.trans hlu) (by simp)
  rw [min_eq_left hlu] at hh
  have hupper := (abs_le.mp hh).2
  have he : (x/D-x/(2*D))/Real.log x+(1/4:ℝ)*x/(D*Real.log x)=
      (3/4:ℝ)*(x/(D*Real.log x)) := by ring
  have hpos : 0 ≤ x/(D*Real.log x) := (div_pos hx0 (mul_pos hD0 hlogx)).le
  linarith only [hupper,he,hpos]

theorem tail_head_pair_upper : ∀ᶠ x : ℝ in atTop,
    ∀ d : ℕ,0 < d → ∀ n : ℕ,∀ Q : Finset (Fin n → ℕ),
      (∀ p ∈ Q,(∀ i,(p i).Prime) ∧ StrictAnti p ∧
        Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ)) →
      ((tailHeadPairs x d Q).card:ℝ) ≤
        (x/(d*Real.log x))*(∑ p ∈ Q,reciprocalShiftWeight p) := by
  filter_upwards [head_prime_count_upper] with x hx
  intro d hd n Q hQ
  have hcount (p) (hp : p ∈ Q) :
      ((primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
        (x/((d*(∏ i,p i).totient:ℕ):ℝ))).card:ℝ) ≤
        (x/(d*Real.log x))*reciprocalShiftWeight p := by
    obtain ⟨hprime,horder,hlog⟩ := hQ p hp
    have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hprime i).pos)
    have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr hr)
    apply (hx _ hD hlog).trans_eq
    rw [←prime_tail_totient_weight p hprime horder,Nat.cast_mul]
    ring
  have hh := Finset.sum_le_sum hcount
  simpa only [tailHeadPairs,Finset.card_sigma,Nat.cast_sum,Finset.mul_sum] using hh

end TotientAsymptotic

end

end OAI
