import OAI.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe uS uTerm

variable {Out K H A : Type*} [Fintype Out] [DecidableEq Out]
  [Fintype K] [Fintype H] [Fintype A]
variable {S : Type uS}
variable (N : ℕ) [NeZero N] (T : ℕ)

local notation "Ch" => ((Finset.univ.filter
  (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)) : Type _)

local instance retainedOrderNeZero (χ : Ch) : NeZero (orderOf χ.val) :=
  ⟨(zmod_character_order_pos χ.val).ne'⟩

theorem forecastRetained_site_term_count
    (positive : (χ : Ch) → (K → H → ZMod (orderOf χ.val)) → Prop)
    (e : (χ : Ch) → {r // positive χ r} → A → ScalarSiteExpansion.{uS,uTerm} S)
    {O : ℝ}
    (he : ∀ χ r a, (Fintype.card (e χ r a).Term : ℝ) ≤ Real.exp O) :
    (Fintype.card (Σ χ : Ch, Σ r : {r // positive χ r}, ∀ a, (e χ r a).Term) : ℝ) ≤
      (T : ℝ) ^ (Fintype.card Out + Fintype.card K * Fintype.card H + 1) *
        Real.exp (Fintype.card A * O) := by
  have hterm (χ : Ch) (r : {r // positive χ r}) :
      (Fintype.card (∀ a, (e χ r a).Term) : ℝ) ≤ Real.exp (Fintype.card A * O) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    calc
      (∏ a, (Fintype.card (e χ r a).Term : ℝ)) ≤ ∏ _a : A, Real.exp O :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun a _ => he χ r a)
      _ = Real.exp (Fintype.card A * O) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  have hres (χ : Ch) : Fintype.card {r // positive χ r} ≤
      orderOf χ.val ^ (Fintype.card K * Fintype.card H) := by
    have h := Fintype.card_subtype_le (positive χ)
    simpa only [Fintype.card_fun, ZMod.card, ← pow_mul, Nat.mul_comm] using h
  have hcount : (∑ χ : Ch, orderOf χ.val ^ (Fintype.card K * Fintype.card H)) ≤
      T ^ (Fintype.card Out + Fintype.card K * Fintype.card H + 1) := by
    have hsum := Finset.sum_coe_sort
      (Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T))
      (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ^ (Fintype.card K * Fintype.card H))
    have hb := rationalForecast_order_residue_term_count (I := K × H) (J := Out) N T
    exact hsum.trans_le (by simpa only [Fintype.card_prod] using hb)
  have hresSum : (∑ χ : Ch, (Fintype.card {r // positive χ r} : ℝ)) ≤
      (T : ℝ) ^ (Fintype.card Out + Fintype.card K * Fintype.card H + 1) := by
    calc
      _ ≤ ∑ χ : Ch, ((orderOf χ.val ^ (Fintype.card K * Fintype.card H) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun χ _ => Nat.cast_le.mpr (hres χ))
      _ ≤ _ := by exact_mod_cast hcount
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    (∑ χ : Ch, (Fintype.card (Σ r : {r // positive χ r}, ∀ a, (e χ r a).Term) : ℝ)) ≤
        ∑ χ : Ch, (Fintype.card {r // positive χ r} : ℝ) *
          Real.exp (Fintype.card A * O) := by
      apply Finset.sum_le_sum
      intro χ _
      rw [Fintype.card_sigma, Nat.cast_sum]
      exact (Finset.sum_le_sum (fun r _ => hterm χ r)).trans_eq (by simp)
    _ = (∑ χ : Ch, (Fintype.card {r // positive χ r} : ℝ)) *
        Real.exp (Fintype.card A * O) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hresSum (Real.exp_nonneg _)

end Erdos3

end

end OAI
