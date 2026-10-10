import OAI.Analysis.FiniteFactor.Sampling.IntegratedCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

/-- Telescoping products needs upper bounds only. In particular, a zero ideal
coordinate moment causes no division or exceptional case. -/
theorem sampling_product_error {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (M ε : ℝ)
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ M) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ M)
    (he : ∀ i ∈ S, |f i-g i| ≤ ε) :
    |(∏ i ∈ S, f i)-(∏ i ∈ S, g i)| ≤ (S.card : ℝ)*ε*M^S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfi := hf i (mem_insert_self _ _)
    have hgi := hg i (mem_insert_self _ _)
    have hei := he i (mem_insert_self _ _)
    have hfS : ∀ j ∈ S, 0 ≤ f j ∧ f j ≤ M := fun j hj => hf j (mem_insert_of_mem hj)
    have hgS : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ M := fun j hj => hg j (mem_insert_of_mem hj)
    have heS : ∀ j ∈ S, |f j-g j| ≤ ε := fun j hj => he j (mem_insert_of_mem hj)
    have hprod : 0 ≤ ∏ j ∈ S, g j := prod_nonneg (fun j hj => (hgS j hj).1)
    have hprodM : (∏ j ∈ S, g j) ≤ M^S.card := by
      calc
        _ ≤ ∏ _j ∈ S, M := prod_le_prod₀ (fun j hj => (hgS j hj).1) (fun j hj => (hgS j hj).2)
        _ = _ := by simp
    have hMp : 0 ≤ M^S.card := pow_nonneg (by linarith) _
    have hbase : 0 ≤ (S.card : ℝ)*ε*M^S.card := by positivity
    rw [prod_insert hi,prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    calc
      _ = |f i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j))+(f i-g i)*(∏ j ∈ S, g j)| := by congr 1; ring
      _ ≤ |f i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j))|+|(f i-g i)*(∏ j ∈ S, g j)| := abs_add_le _ _
      _ = f i*|(∏ j ∈ S, f j)-(∏ j ∈ S, g j)|+|f i-g i| *(∏ j ∈ S, g j) := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfi.1,abs_of_nonneg hprod]
      _ ≤ M*((S.card : ℝ)*ε*M^S.card)+ε*M^S.card := by
        exact add_le_add (mul_le_mul hfi.2 (ih hfS hgS heS) (abs_nonneg _) (by linarith))
          (mul_le_mul hei hprodM hprod hε)
      _ ≤ _ := by nlinarith [mul_nonneg hε hMp,mul_nonneg (show 0 ≤ M-1 by linarith) (mul_nonneg hε hMp)]

end
end FiniteFactor

end OAI
