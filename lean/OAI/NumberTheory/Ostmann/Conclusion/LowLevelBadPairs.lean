import OAI.NumberTheory.Ostmann.Conclusion.BadFraction

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def TransferBadArrangement {r m : ℕ} (σ : Equiv.Perm (Fin r × Fin m)) : Prop :=
  r ≤ 2 ∨ BadArrangement σ

def transferBadCount (r m : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin r × Fin m) // TransferBadArrangement σ}

theorem transferBadCount_le_all (r m : ℕ) : transferBadCount r m ≤ (r*m).factorial := by
  classical
  have h := Nat.card_le_card_of_injective
    (fun σ : {σ : Equiv.Perm (Fin r × Fin m) // TransferBadArrangement σ} => σ.val)
    Subtype.val_injective
  simpa only [transferBadCount, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_prod,
    Fintype.card_fin] using h

theorem transferBadCount_eq_of_gt {r m : ℕ} (hr : 2 < r) :
    transferBadCount r m = badArrangementCount r m := by
  simp only [transferBadCount, badArrangementCount, TransferBadArrangement, not_le.mpr hr, false_or]

theorem transferBad_fraction_bound {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (transferBadCount r m : ℝ)/((r*m).factorial : ℝ) ≤
      (r : ℝ)^(2*r)*Real.exp ((2-(3/4 : ℝ)*Real.log r)*(r : ℝ)*m) := by
  by_cases hsmall : r ≤ 2
  · have hfrac : (transferBadCount r m : ℝ)/((r*m).factorial : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast transferBadCount_le_all r m
    have hp : 1 ≤ (r : ℝ)^(2*r) := one_le_pow₀ (by exact_mod_cast hr)
    have hlog : Real.log (r : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by exact_mod_cast hr : (0 : ℝ) < r)
      have : (r : ℝ) ≤ 2 := by exact_mod_cast hsmall
      linarith
    have hexp : 1 ≤ Real.exp ((2-(3/4 : ℝ)*Real.log r)*(r : ℝ)*m) := by
      apply Real.one_le_exp_iff.mpr
      have hrate : 0 ≤ 2-(3/4 : ℝ)*Real.log r := by linarith
      exact mul_nonneg (mul_nonneg hrate (by positivity)) (by positivity)
    exact hfrac.trans (by nlinarith)
  · rw [transferBadCount_eq_of_gt (by omega)]
    refine (badArrangement_fraction_bound hr hm).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg (show 0 ≤ (r : ℝ) by positivity) (show 0 ≤ (m : ℝ) by positivity)
    nlinarith

def relativePairEquiv {G : Type*} [Group G] (P : G → Prop) (a : G) :
    {b : G // P (a⁻¹*b)} ≃ {b : G // P b} where
  toFun b := ⟨a⁻¹*b.val,b.property⟩
  invFun b := ⟨a*b.val,by simpa using b.property⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp

theorem relative_bad_count {r m : ℕ} (a : Equiv.Perm (Fin r × Fin m)) :
    Nat.card {b : Equiv.Perm (Fin r × Fin m) // TransferBadArrangement (a⁻¹*b)} =
      transferBadCount r m :=
  Nat.card_congr (relativePairEquiv TransferBadArrangement a)

end Ostmann.Conclusion

end

end OAI
