import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudgetSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBlocks

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem biasedBlockWeight_eq_moment_integrand (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (v : CommonSample sources origin) :
    biasedBlockWeight sources origin p q v =
      (v.val:ℝ)⁻¹ * ∏i:Fiber p q,sourceWeight sources origin i.val v*(v.val:ℝ) := by
  simp only [biasedBlockWeight,blockWeight,CompensationEqualityPatterns.multiplicity,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,div_eq_mul_inv]
  ring

omit [DecidableEq ι] in
theorem biasedBlockWeight_nonneg (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (v : CommonSample sources origin) :
    0≤biasedBlockWeight sources origin p q v := by
  rw [biasedBlockWeight_eq_moment_integrand]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.prod_nonneg (fun i _ => mul_nonneg (sourceWeight_nonneg sources origin i.val v)
      (Nat.cast_nonneg _)))

theorem biasedBlockWeight_sum_le (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (C : ι → ℝ)
    (hcap : ∀i (v:CommonSample sources origin),
      sourceWeight sources origin i v*(v.val:ℝ)≤C i) (q : Block p) :
    (∑v:CommonSample sources origin,biasedBlockWeight sources origin p q v)≤blockCap p C q := by
  simp_rw [biasedBlockWeight_eq_moment_integrand]
  exact blockMoment_le_cap p (sourceWeight sources origin) (fun v => (v.val:ℝ)) C
    (sourceWeight_nonneg sources origin)
    (fun v => by exact_mod_cast (commonSample_prime sources origin v).pos)
    hcap (HistoryCompensationMoment.sourceWeight_sum sources origin) q

theorem pattern_biased_kernel_sum_le (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (C : ι → ℝ)
    (hcap : ∀i (v:CommonSample sources origin),
      sourceWeight sources origin i v*(v.val:ℝ)≤C i)
    (K : (Block p → CommonSample sources origin) → Block p → ℝ)
    (hK : ∀b q,0≤K b q ∧ K b q≤2/((b q).val:ℝ)) :
    (∑b:BlockDraw p (CommonSample sources origin),
      (∏q,biasedBlockWeight sources origin p q (b.val q)) *
        (∏q,((b.val q).val:ℝ)) * (∏q,K b.val q)) ≤
      (2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockCap p C q := by
  let w : Block p → CommonSample sources origin → ℝ :=
    fun q v => 2*biasedBlockWeight sources origin p q v
  have hw : ∀q v,0≤w q v := fun q v =>
    mul_nonneg (by norm_num) (biasedBlockWeight_nonneg sources origin p q v)
  calc
    _ ≤ ∑b:BlockDraw p (CommonSample sources origin),∏q,w q (b.val q) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro q hq
        exact mul_nonneg (mul_nonneg (biasedBlockWeight_nonneg sources origin p q (b.val q))
          (Nat.cast_nonneg _)) (hK b.val q).1
      · intro q hq
        have hp : (0:ℝ)<(b.val q).val := by
          exact_mod_cast (commonSample_prime sources origin (b.val q)).pos
        have hk := (le_div_iff₀ hp).mp (hK b.val q).2
        dsimp only [w]
        calc
          (biasedBlockWeight sources origin p q (b.val q)*((b.val q).val:ℝ))*K b.val q =
              biasedBlockWeight sources origin p q (b.val q)*(K b.val q*((b.val q).val:ℝ)) := by ring
          _ ≤ biasedBlockWeight sources origin p q (b.val q)*2 :=
            mul_le_mul_of_nonneg_left hk (biasedBlockWeight_nonneg sources origin p q (b.val q))
          _ = _ := mul_comm _ _
    _ ≤ ∏q:Block p,∑v:CommonSample sources origin,w q v := blockDraw_sum_prod_le p w hw
    _ = (2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,∑v:CommonSample sources origin,biasedBlockWeight sources origin p q v := by
      simp only [w,←Finset.mul_sum,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.prod_le_prod₀
        (fun q _ => Finset.sum_nonneg (fun v _ => biasedBlockWeight_nonneg sources origin p q v))
        (fun q _ => biasedBlockWeight_sum_le sources origin p C hcap q)

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
