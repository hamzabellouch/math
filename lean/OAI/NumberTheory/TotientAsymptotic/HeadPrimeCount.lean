import OAI.NumberTheory.TotientAsymptotic.PrimeInterval
import OAI.NumberTheory.TotientAsymptotic.PrimeNumberTheorem

namespace OAI

/-! Uniform abundance of head primes above a subpower tail denominator. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma head_prime_count_lower : ∀ᶠ x : ℝ in atTop,∀ D : ℝ,1 ≤ D →
    Real.log D ≤ (Real.log x)^(4/5:ℝ) →
      x/(4*D*Real.log x) ≤ ((primeInterval (x/(2*D)) (x/D)).card:ℝ) := by
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
  have hlo := (abs_le.mp hh).1
  have he : (x/D-x/(2*D))/Real.log x-(1/4:ℝ)*x/(D*Real.log x)=
      x/(4*D*Real.log x) := by ring
  linarith only [hlo,he]

lemma mem_head_prime_interval {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) {p : ℕ}
    (hp : p ∈ primeInterval (x/(2*D)) (x/D)) :
    p.Prime ∧ x/(2*D) < p ∧ (p:ℝ) ≤ x/D := by
  obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
  have hh := Nat.mem_primesLE.mp hp
  exact ⟨hh.2,hlo,(Nat.cast_le.mpr hh.1).trans (Nat.floor_le (div_nonneg hx hD.le))⟩

end TotientAsymptotic

end

end OAI
