import OAI.NumberTheory.TotientAsymptotic.LocalPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.PrimeDiscardCutoff

namespace OAI

/-! Each suffix lies in a prime interval determined only by its distance from the end. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def localPrimeHeight (A : ℝ) (L h : ℕ) : ℝ :=
  A*(h+L+2:ℕ)*(rho^(h+L+2))⁻¹+2

lemma localPrimeHeight_ge_two {A : ℝ} (hA : 0 ≤ A) (L h : ℕ) :
    2 ≤ localPrimeHeight A L h := by
  unfold localPrimeHeight
  have hn : 0 ≤ A*(h+L+2:ℕ)*(rho^(h+L+2))⁻¹ :=
    mul_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (inv_pos.mpr (pow_pos rho_pos _)).le
  linarith only [hn]

lemma localPrimeHeight_mono {A : ℝ} (hA : 0 ≤ A) (L : ℕ) :
    Monotone (localPrimeHeight A L) := by
  intro h k hhk
  have hh : h+L+2 ≤ k+L+2 := by omega
  have he := mul_le_mul_of_nonneg_left (index_inv_pow_mono hh) hA
  unfold localPrimeHeight
  simpa only [mul_assoc,add_comm] using add_le_add_right he 2

lemma prime_mem_discard_bound_of_coordinate {p : ℕ} (hp : p.Prime)
    {U : ℝ} (hU : 2 ≤ U) (hcoord : B p ≤ U) :
    p ∈ Nat.primesLE (discardPrimeBound U) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have he : (p:ℝ) ≤ Real.exp (Real.exp U) :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hp1)).mp hcoord)
  have hupper := (discardPrimeBound_bounds hU).2.2.2
  have hUU : U ≤ (6/5:ℝ)*U := by linarith only [hU]
  have hh : (p:ℝ) ≤ discardPrimeBound U :=
    he.trans ((Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hUU)).trans hupper)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hh,hp⟩

theorem local_prime_suffix_support {c : ℝ} (hc : 0 < c) :
    ∃ A : ℝ,0 < A ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,n+H=m x → ∀ p ∈ gridPrimeTuples (localPrimeGrid x c L n),
        ∀ i j : Fin n,i ≤ j →
          p j ∈ Nat.primesLE (discardPrimeBound (localPrimeHeight A L (m x-i.val))) := by
  obtain ⟨A,hA,hdata⟩ := local_prime_coordinates hc
  refine ⟨A,hA,?_⟩
  intro L
  filter_upwards [hdata L] with H hH
  filter_upwards [hH] with x hx
  intro n hn p hp i j hij
  obtain ⟨hprime,_,_,hupper⟩ := hx n hn p hp
  have hji : m x-j.val ≤ m x-i.val := Nat.sub_le_sub_left hij _
  have hcoord : B (p j) ≤ localPrimeHeight A L (m x-i.val) := by
    apply le_trans (hupper j)
    have hm := localPrimeHeight_mono hA.le L hji
    unfold localPrimeHeight at hm ⊢
    linarith only [hm]
  exact prime_mem_discard_bound_of_coordinate (hprime j) (localPrimeHeight_ge_two hA.le _ _) hcoord

lemma localPrimeHeight_log_bound {A : ℝ} (hA : 0 < A) (L : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ᶠ h : ℕ in atTop,
      Real.log (6*localPrimeHeight A L h) ≤ D*h := by
  let D := |Real.log (6*(A+2))|+2*(1+lam)
  have hD : 0 < D := by dsimp [D]; linarith [lam_pos,abs_nonneg (Real.log (6*(A+2)))]
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop (L+2),eventually_ge_atTop 1] with h hh hh1
  let k := h+L+2
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by dsimp [k]; omega)
  have hk0 : (0:ℝ) < k := zero_lt_one.trans_le hk1
  have hkh : (k:ℝ) ≤ 2*h := by exact_mod_cast (show k ≤ 2*h by dsimp [k]; omega)
  have hr : (1:ℝ) ≤ (rho^k)⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hkr : (1:ℝ) ≤ (k:ℝ)*(rho^k)⁻¹ := one_le_mul_of_one_le_of_one_le hk1 hr
  have hu : localPrimeHeight A L h ≤ (A+2)*(k:ℝ)*(rho^k)⁻¹ := by
    unfold localPrimeHeight
    change A*(k:ℝ)*(rho^k)⁻¹+2 ≤ _
    nlinarith only [hkr]
  have hu0 : 0 < localPrimeHeight A L h :=
    lt_of_lt_of_le (by norm_num) (localPrimeHeight_ge_two hA.le L h)
  have hlog := Real.log_le_log (mul_pos (by norm_num) hu0)
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ) ≤ 6))
  have he : 6*((A+2)*(k:ℝ)*(rho^k)⁻¹) = (6*(A+2))*(k:ℝ)*(rho^k)⁻¹ := by ring
  rw [he,Real.log_mul (mul_pos (by linarith) hk0).ne' (inv_ne_zero (pow_pos rho_pos _).ne'),
    Real.log_mul (by linarith : 6*(A+2) ≠ 0) hk0.ne',Real.log_inv,Real.log_pow] at hlog
  have hlrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [hlrho] at hlog
  have hklog := Real.log_le_self hk0.le
  have hconst := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ h by exact_mod_cast hh1)
    (abs_nonneg (Real.log (6*(A+2))))
  have hlinear := mul_le_mul_of_nonneg_left hkh (show 0 ≤ 1+lam by linarith [lam_pos])
  dsimp [D]
  nlinarith only [hlog,hklog,hconst,hlinear,le_abs_self (Real.log (6*(A+2)))]

end TotientAsymptotic

end

end OAI
