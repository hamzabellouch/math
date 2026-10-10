import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkRestorationErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkRestorationError
open Construction HistoryBulkPriorGrid ScaleBudget Filter

theorem bulk_restoration_error_eventually (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (n a M : ℕ) (H : ℝ),
      E.card ≤ 2 → n ≤ 2^k*Conclusion.bulkSize k L → a ≤ 3+2^(k+1) →
      0 < M → Real.log (M : ℝ) ≤ Real.exp (bulk.μ*L) → 0 ≤ H →
      H ≤ (M : ℝ)^(n+a)*Real.exp (C*((Conclusion.bulkSize k L : ℝ)+1)) →
      (bulkFullMassRatio L E^n-1)*H ≤ Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [ratio_pow_error_eventually,
    eventually_double_exp_error (restorationCost k C) 1
      (a := bulk.μ) (b := (1/250 : ℝ)) (d := bulk.target) (c := 1)
      (by norm_num [bulk]) (by norm_num [bulk]) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hratio hbudget hL
  intro E n a M H hE hn ha hM hmod hH0 hH
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hmodulus : (M : ℝ)^(n+a)*Real.exp (C*((Conclusion.bulkSize k L : ℝ)+1)) ≤
      Real.exp (((n : ℝ)+(a : ℝ))*Real.exp (bulk.μ*L)+
        C*((Conclusion.bulkSize k L : ℝ)+1)) := by
    calc
      _ = Real.exp (((n : ℝ)+(a : ℝ))*Real.log (M : ℝ)+
          C*((Conclusion.bulkSize k L : ℝ)+1)) := by
        rw [Real.exp_add, ← Nat.cast_add, Real.exp_nat_mul, Real.exp_log hMp]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hmod
          (by positivity : (0 : ℝ) ≤ (n : ℝ)+(a : ℝ))
        linarith only [hh]
  have hr := hratio E hE n
  have hcost := restoration_cost_le k C hL hn ha
  calc
    _ ≤ Real.exp (2+(1+Real.log 4)*(n : ℝ)-Real.exp ((1/250 : ℝ)*L))*
        Real.exp (((n : ℝ)+(a : ℝ))*Real.exp (bulk.μ*L)+
          C*((Conclusion.bulkSize k L : ℝ)+1)) :=
      mul_le_mul hr.2 (hH.trans hmodulus) hH0 (Real.exp_nonneg _)
    _ = Real.exp (2+(1+Real.log 4)*(n : ℝ)-Real.exp ((1/250 : ℝ)*L)+
        (((n : ℝ)+(a : ℝ))*Real.exp (bulk.μ*L)+C*((Conclusion.bulkSize k L : ℝ)+1))) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (-1*Real.exp ((1/250 : ℝ)*L)+
        restorationCost k C*L^1*Real.exp (bulk.μ*L)) := by
      apply Real.exp_le_exp.mpr
      simp only [pow_one]
      linarith only [hcost]
    _ ≤ _ := hbudget

theorem bulk_grid_source_error_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (a M : ℕ) (H : ℝ),
      E.card ≤ 2 → Fintype.card ι ≤ 2^k*Conclusion.bulkSize k L → a ≤ 3+2^(k+1) →
      0 < M → Real.log (M : ℝ) ≤ Real.exp (bulk.μ*L) → 0 ≤ H →
      H ≤ (M : ℝ)^(Fintype.card ι+a)*Real.exp (C*((Conclusion.bulkSize k L : ℝ)+1)) →
      ∀ (hZ : 0 < harmonicPrimeMass (bulkPrimeBand L E)) (F : (ι → ℕ) → ℂ),
      (∀ p : BulkPrimeTuple ι L, ‖F (fun i => (p i).val)‖ ≤ H) →
      ‖bulkGridMean L E F-
        (bulkProductPrior (ι := ι) L E hZ).cmean (fun p => F (fun i => (p i).val))‖ ≤
        Real.exp (-Real.exp (bulk.target*L)) := by
  filter_upwards [bulk_restoration_error_eventually k C] with L hL
  intro E a M H hE hn ha hM hmod hH0 hH hZ F hF
  exact (bulkGridMean_sub_source_cmean_le L E hZ F hH0 hF).trans
    (hL E (Fintype.card ι) a M H hE hn ha hM hmod hH0 hH)

end Ostmann.Arithmetic.HistoryBulkRestorationError

end

end OAI
