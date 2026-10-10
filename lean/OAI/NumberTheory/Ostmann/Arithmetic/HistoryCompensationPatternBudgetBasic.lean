import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsHistory

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPatternBudget
open Construction CompensationEqualityPatterns
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

def blockMoment {τ : ι→ℕ} (p : Pattern τ) (μ : ι→κ→ℝ) (value : κ→ℝ)
    (q : Block p) : ℝ := ∑x:κ, (value x)⁻¹*∏i:Fiber p q, (μ i.val x*value x)

omit [DecidableEq ι] in
theorem blockDraw_sum_prod_le {τ : ι→ℕ} (p : Pattern τ)
    (w : Block p→κ→ℝ) (hw : ∀q x,0 ≤ w q x) :
    (∑b:BlockDraw p κ,∏q:Block p,w q (b.val q)) ≤ ∏q:Block p,∑x:κ,w q x := by
  let P : (Block p→κ)→Prop := fun b => Function.Injective (fun q => (blockType p q,b q))
  have he := Fintype.sum_subtype_add_sum_subtype P (fun b : Block p→κ => ∏q,w q (b q))
  have hn : 0 ≤ ∑b:{b:Block p→κ // ¬P b},∏q,w q (b.val q) :=
    Finset.sum_nonneg (fun b _ => Finset.prod_nonneg (fun q _ => hw q (b.val q)))
  calc
    _ ≤ ∑b:Block p→κ,∏q,w q (b q) := by
      change (∑b:{b:Block p→κ // P b},∏q,w q (b.val q)) ≤ _
      linarith
    _ = _ := (Fintype.prod_sum w).symm

omit [DecidableEq ι] [Fintype κ] in
theorem blockWeight_mul_jacobian {τ : ι→ℕ} (p : Pattern τ)
    (μ : ι→κ→ℝ) (value : κ→ℝ) (b : BlockDraw p κ) :
    (∏q:Block p,blockWeight p μ q (b.val q))*(∏i:ι,value (expand p b i))=
      ∏q:Block p,∏i:Fiber p q,(μ i.val (b.val q)*value (b.val q)) := by
  rw [product_by_multiplicity p b value,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _
  simp only [blockWeight,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,CompensationEqualityPatterns.multiplicity]

omit [DecidableEq ι] in
theorem blockDraw_weighted_norm_le {τ : ι→ℕ} (p : Pattern τ)
    (μ : ι→κ→ℝ) (value : κ→ℝ) (hμ : ∀i x,0 ≤ μ i x)
    (hv : ∀x,0 ≤ value x) (F : BlockDraw p κ→ℂ)
    (hF : ∀b,‖F b‖ ≤ (∏i:ι,value (expand p b i))*∏q:Block p,(2/value (b.val q))) :
    ‖∑b:BlockDraw p κ,(∏q:Block p,blockWeight p μ q (b.val q)) • F b‖ ≤
      (2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockMoment p μ value q := by
  let w : Block p→κ→ℝ := fun q x => 2*(value x)⁻¹*∏i:Fiber p q,(μ i.val x*value x)
  have hw : ∀q x,0 ≤ w q x := by
    intro q x
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (hv x)))
      (Finset.prod_nonneg (fun i _ => mul_nonneg (hμ i.val x) (hv x)))
  have hb : ∀b:BlockDraw p κ,
      ‖(∏q:Block p,blockWeight p μ q (b.val q)) • F b‖ ≤ ∏q:Block p,w q (b.val q) := by
    intro b
    have hm : 0 ≤ ∏q:Block p,blockWeight p μ q (b.val q) := by
      apply Finset.prod_nonneg; intro q _
      exact Finset.prod_nonneg (fun i _ => hμ i.val (b.val q))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm]
    calc
      _ ≤ (∏q:Block p,blockWeight p μ q (b.val q))*
          ((∏i:ι,value (expand p b i))*∏q:Block p,(2/value (b.val q))) :=
        mul_le_mul_of_nonneg_left (hF b) hm
      _ = _ := by
        rw [←mul_assoc,blockWeight_mul_jacobian,←Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro q _
        dsimp only [w]
        rw [div_eq_mul_inv]
        ring
  calc
    _ ≤ ∑b:BlockDraw p κ,‖(∏q:Block p,blockWeight p μ q (b.val q)) • F b‖ := norm_sum_le _ _
    _ ≤ ∑b:BlockDraw p κ,∏q:Block p,w q (b.val q) := Finset.sum_le_sum (fun b _ => hb b)
    _ ≤ ∏q:Block p,∑x:κ,w q x := blockDraw_sum_prod_le p w hw
    _ = _ := by
      simp only [w,mul_assoc,←Finset.mul_sum,blockMoment,Finset.prod_mul_distrib,
        Finset.prod_const,Finset.card_univ]

end Ostmann.Arithmetic.HistoryCompensationPatternBudget

end

end OAI
