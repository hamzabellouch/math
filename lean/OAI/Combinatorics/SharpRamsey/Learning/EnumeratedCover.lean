import Mathlib

namespace OAI

section
namespace SharpLogRamsey.DescriptionEnumeration
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

lemma choose_exp_bound {N n : ℕ} (hn : 0<n) :
    (N.choose n:ℝ) ≤ exp (n*(log ((N:ℝ)/n)+1)) := by
  by_cases hN : N=0
  · subst N
    rw [Nat.choose_eq_zero_of_lt hn]
    simp only [Nat.cast_zero]
    exact (exp_pos _).le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hN' : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he := Real.pow_div_factorial_le_exp (n:ℝ) (show (0:ℝ)≤n by positivity) n
  have hf : (1:ℝ)/n.factorial≤exp n/(n:ℝ)^n := by
    apply (div_le_div_iff₀ hfact (pow_pos hn' n)).mpr
    have hh := (div_le_iff₀ hfact).mp he
    simpa only [one_mul] using hh
  calc
    (N.choose n:ℝ) ≤ (N:ℝ)^n/n.factorial := Nat.choose_le_pow_div n N
    _ ≤ (N:ℝ)^n*(exp n/(n:ℝ)^n) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hf (pow_nonneg hN'.le n)
    _ = exp n*((N:ℝ)/n)^n := by rw [div_pow]; ring
    _ = exp (n*(log ((N:ℝ)/n)+1)) := by
      rw [mul_add,mul_one,exp_add,exp_nat_mul,exp_log (div_pos hN' hn')]
      ring

theorem public_cover (U : Finset α) (n : ℕ) (hn : 0<n) (hnu : n≤U.card) :
    let caps := U.powersetCard n
    (∀ W∈caps,W⊆U ∧ W.card=n) ∧
    (∀ S,S⊆U → S.card=n → ∃ W∈caps,S∩W=S) ∧
    log ((caps.card:ℝ)+1)≤log 2+n*(log ((U.card:ℝ)/n)+1) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro W hW
    exact mem_powersetCard.mp hW
  · intro S hSU hSn
    exact ⟨S,mem_powersetCard.mpr ⟨hSU,hSn⟩,inter_self S⟩
  · rw [card_powersetCard]
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
    have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
    have hb : 0≤(n:ℝ)*(log ((U.card:ℝ)/n)+1) := by positivity
    have h := choose_exp_bound (N:=U.card) hn
    have he := one_le_exp_iff.mpr hb
    have hm : ((U.card.choose n:ℝ)+1)≤2*exp (n*(log ((U.card:ℝ)/n)+1)) := by linarith
    have hl := log_le_log (by positivity : (0:ℝ)<(U.card.choose n:ℝ)+1) hm
    rwa [log_mul (by norm_num) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.DescriptionEnumeration

end

end OAI
