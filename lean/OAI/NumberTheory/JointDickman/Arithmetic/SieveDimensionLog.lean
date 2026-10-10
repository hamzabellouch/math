import OAI.NumberTheory.JointDickman.Arithmetic.UpperSieveInput

namespace OAI

/-! # The sieve dimension condition on logarithmic intervals -/
namespace JointDickman
open Finset

 theorem sieveDimension_log_interval {P Q : Finset ℕ} {g : ℕ → ℝ} {κ A z a b R : ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hp : ∀ p ∈ P, 0 < (p:ℝ)) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hQP : Q ⊆ P)
    (ha : Real.log 2 ≤ a) (hab : a ≤ b) (hbz : b ≤ Real.log z) (hz : 0 < z)
    (hQ : ∀ p ∈ Q, a ≤ Real.log p ∧ Real.log p ≤ b)
    (hR : 0 < R) (hba : b ≤ R*a) :
    (∏ p ∈ Q, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log R+A/Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := h2.trans_le ha
  have hsub : Q ⊆ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b) := by
    intro p hq
    refine mem_filter.mpr ⟨hQP hq,?_,?_⟩
    · exact (Real.exp_le_exp.mpr (hQ p hq).1).trans_eq (Real.exp_log (hp p (hQP hq)))
    · exact (Real.exp_log (hp p (hQP hq))).symm.trans_le (Real.exp_le_exp.mpr (hQ p hq).2)
  calc
    _ ≤ ∏ p ∈ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b), (1-g p)⁻¹ := by
      apply prod_le_prod_of_subset_of_one_le₀ hsub
      · intro p hq
        exact inv_nonneg.mpr (by linarith [(hg p (hQP hq)).2])
      · intro p hq _
        exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hq).1).2])).mpr
          (by linarith [(hg p (mem_filter.mp hq).1).1])
    _ ≤ (Real.log (Real.exp b)/Real.log (Real.exp a))^κ *
        Real.exp (A/Real.log (Real.exp a)) := by
      apply hd
      · calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
             _ ≤ _ := Real.exp_le_exp.mpr ha
      · exact Real.exp_le_exp.mpr hab
      · exact (Real.exp_le_exp.mpr hbz).trans_eq (Real.exp_log hz)
    _ ≤ R^κ * Real.exp (A/Real.log 2) := by
      simp only [Real.log_exp]
      apply mul_le_mul
      · exact Real.rpow_le_rpow (div_nonneg (ha0.le.trans hab) ha0.le)
          ((div_le_iff₀ ha0).mpr hba) hκ
      · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hA h2 ha)
      · exact (Real.exp_pos _).le
      · exact Real.rpow_nonneg hR.le κ
    _ = _ := by rw [Real.rpow_def_of_pos hR, ← Real.exp_add]; congr 1; ring

end JointDickman

end OAI
