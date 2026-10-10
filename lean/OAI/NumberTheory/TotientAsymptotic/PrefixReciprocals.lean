import OAI.NumberTheory.TotientAsymptotic.TailBelowPrefix

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def prefixReciprocalError (H : ℕ) : ℝ := polynomialGeometricTail 0 (Real.exp (-1)) H

lemma prefixReciprocalError_nonneg (H : ℕ) : 0 ≤ prefixReciprocalError H :=
  polynomialGeometricTail_nonneg 0 (Real.exp_pos _).le H

lemma prefixReciprocalError_tendsto : Tendsto prefixReciprocalError atTop (nhds 0) :=
  polynomialGeometricTail_tendsto 0 _

lemma weighted_prefixReciprocalError_tendsto (C : ℝ) :
    Tendsto (fun H => Real.exp (C*cofactorScale H)*prefixReciprocalError H) atTop (nhds 0) :=
  cofactor_polynomialGeometricTail_tendsto C 0 (Real.exp_pos _).le (by simp)

lemma prefix_prime_reciprocal : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    ∀ i : Fin (R x H), (1 : ℝ)/remainderPrime η (i.val+1) ≤
      Real.exp (-1)^(m x-(i.val+1)) := by
  have ht : Tendsto (fun h : ℝ => h*Real.exp (-(1/2 : ℝ)*h)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      1 (1/2) (by norm_num : (0 : ℝ)<1/2)
  obtain ⟨h₀,hh₀⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))
  filter_upwards [eventually_ge_atTop (Nat.ceil h₀),eventually_ge_atTop 2] with H hH hH2
  intro x hs hm η hη i
  have hi : i.val+1 ≤ R x H := by have := i.isLt; omega
  have hPH := (P_lt_self hH2).le
  have hiL : i.val+1 ≤ L x H := by unfold R L at *; omega
  have hh : H ≤ m x-(i.val+1) := by unfold R at hi; omega
  let h := m x-(i.val+1)
  have hhr : h₀ ≤ (h : ℝ) := (Nat.le_ceil h₀).trans (by exact_mod_cast hH.trans hh)
  have he := hh₀ h hhr
  have he' : (h : ℝ) ≤ Real.exp ((1/2 : ℝ)*h) := by
    have he' := mul_lt_mul_of_pos_right he (Real.exp_pos ((1/2 : ℝ)*h))
    rw [mul_assoc,← Real.exp_add] at he'
    simpa using he'.le
  have hband : lam*h ≤ bandScale x (i.val+1) := by
    have ha := alpha_ge_lam hs
    have hp : 1 ≤ (rho^h)⁻¹ := (one_le_inv₀ (pow_pos rho_pos h)).mpr
      (pow_le_one₀ rho_pos.le rho_lt_one.le)
    change _ ≤ alpha (theta x)*h*(rho^h)⁻¹
    exact (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg h)).trans
      (le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg h)) hp)
  have hp := hη.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega,hiL⟩)
  have hp0 : (0 : ℝ) < remainderPrime η (i.val+1) := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) < remainderPrime η (i.val+1) := by exact_mod_cast hp.1.one_lt
  have hl : (1/2 : ℝ)*h ≤ Real.log (Real.log (remainderPrime η (i.val+1) : ℝ)) := by
    have hlow := hp.2.1
    simp only [remainderCoord,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false] at hlow
    have hlambda := collision_lambda_bounds.1
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hlog : (h : ℝ) ≤ Real.log (remainderPrime η (i.val+1) : ℝ) :=
    he'.trans ((Real.le_log_iff_exp_le (Real.log_pos hp1)).mp hl)
  have hprime : Real.exp h ≤ (remainderPrime η (i.val+1) : ℝ) :=
    (Real.le_log_iff_exp_le hp0).mp hlog
  calc
    (1 : ℝ)/remainderPrime η (i.val+1) ≤ 1/Real.exp h := one_div_le_one_div_of_le (Real.exp_pos _) hprime
    _ = Real.exp (-1)^h := by rw [one_div,← Real.exp_neg,← Real.exp_nat_mul]; congr 1; ring

lemma prefix_reciprocal_sum : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x →
    ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      (∑ i, (1 : ℝ)/ζ.primes i) ≤ prefixReciprocalError H := by
  filter_upwards [prefix_prime_reciprocal] with H hH
  intro x hs hm ζ hζ
  obtain ⟨η,hη,hd,hp⟩ := hζ
  have hsummable : Summable (fun n : ℕ => Real.exp (-1)^(H+n)) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)).comp_injective (fun _ _ h => by omega)
  have he : (∑ i : Fin (R x H), Real.exp (-1)^(m x-(i.val+1))) =
      ∑ n ∈ Finset.range (R x H), Real.exp (-1)^(H+n) := by
    apply Finset.sum_bij (fun i _ => m x-(i.val+1)-H)
    · intro i _
      have := i.isLt
      apply Finset.mem_range.mpr
      unfold R at *
      omega
    · intro i _ j _ hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      unfold R at *
      omega
    · intro n hn
      have hn' := Finset.mem_range.mp hn
      refine ⟨⟨m x-H-1-n,by unfold R at *; omega⟩,Finset.mem_univ _,?_⟩
      change m x-(m x-H-1-n+1)-H=n
      unfold R at hn'
      omega
    · intro i _
      congr 1
      have := i.isLt
      unfold R at *
      omega
  calc
    (∑ i, (1 : ℝ)/ζ.primes i) ≤ ∑ i : Fin (R x H), Real.exp (-1)^(m x-(i.val+1)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [hp]
      exact hH x hs hm η hη i
    _ = _ := he
    _ ≤ ∑' n : ℕ, Real.exp (-1)^(H+n) := hsummable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = prefixReciprocalError H := by simp [prefixReciprocalError,polynomialGeometricTail]

end TotientAsymptotic

end

end OAI
