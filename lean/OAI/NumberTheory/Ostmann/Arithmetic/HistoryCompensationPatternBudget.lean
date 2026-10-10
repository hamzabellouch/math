import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudgetBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPatternBudget
open Construction CompensationEqualityPatterns
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

def anchor {τ : ι→ℕ} (p : Pattern τ) (q : Block p) : Fiber p q :=
  Classical.choice (fiber_nonempty p q)

def blockCap {τ : ι→ℕ} (p : Pattern τ) (C : ι→ℝ) (q : Block p) : ℝ :=
  ∏i ∈ Finset.univ.erase (anchor p q), C i.val

theorem blockMoment_le_cap {τ : ι→ℕ} (p : Pattern τ)
    (μ : ι→κ→ℝ) (value : κ→ℝ) (C : ι→ℝ)
    (hμ : ∀i x,0 ≤ μ i x) (hv : ∀x,0<value x)
    (hcap : ∀i x,μ i x*value x ≤ C i) (hnorm : ∀i,∑x,μ i x=1) (q : Block p) :
    blockMoment p μ value q ≤ blockCap p C q :=
  HistoryCompensationMoment.block_moment_le (fun i:Fiber p q => μ i.val) value
    (fun i:Fiber p q => C i.val) (anchor p q) (fun i x => hμ i.val x)
    hv (fun i x => hcap i.val x) (hnorm (anchor p q).val)

theorem norm_product_weighted_sum_le (τ : ι→ℕ)
    (μ : ι→κ→ℝ) (value : κ→ℝ) (hμ : ∀i x,0 ≤ μ i x)
    (hv : ∀x,0 ≤ value x) (F : (ι→κ)→ℂ)
    (hF : ∀(p:Pattern τ)(b:BlockDraw p κ),
      ‖F (expand p b)‖ ≤ (∏i:ι,value (expand p b i))*∏q:Block p,(2/value (b.val q))) :
    ‖∑w:ι→κ,(∏i,μ i (w i)) • F w‖ ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockMoment p μ value q := by
  rw [product_weighted_sum_eq_patterns τ μ F]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  exact blockDraw_weighted_norm_le p μ value hμ hv (fun b => F (expand p b)) (hF p)

theorem norm_product_weighted_sum_le_caps (τ : ι→ℕ)
    (μ : ι→κ→ℝ) (value : κ→ℝ) (C : ι→ℝ)
    (hμ : ∀i x,0 ≤ μ i x) (hv : ∀x,0<value x)
    (hcap : ∀i x,μ i x*value x ≤ C i) (hnorm : ∀i,∑x,μ i x=1)
    (F : (ι→κ)→ℂ)
    (hF : ∀(p:Pattern τ)(b:BlockDraw p κ),
      ‖F (expand p b)‖ ≤ (∏i:ι,value (expand p b i))*∏q:Block p,(2/value (b.val q))) :
    ‖∑w:ι→κ,(∏i,μ i (w i)) • F w‖ ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockCap p C q := by
  apply (norm_product_weighted_sum_le τ μ value hμ (fun x => (hv x).le) F hF).trans
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod₀
  · intro q _
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (inv_nonneg.mpr (hv x).le)
      (Finset.prod_nonneg (fun i _ => mul_nonneg (hμ i.val x) (hv x).le)))
  · intro q _
    exact blockMoment_le_cap p μ value C hμ hv hcap hnorm q

theorem sum_pattern_cost_le (τ : ι→ℕ) (C : ι→ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hcap : ∀p:Pattern τ,∏q:Block p,blockCap p C q ≤ U) :
    (∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockCap p C q) ≤
      (2:ℝ)^(Fintype.card ι*Fintype.card ι)*(2:ℝ)^Fintype.card ι*U := by
  calc
    _ ≤ ∑p:Pattern τ,(2:ℝ)^Fintype.card ι*U := by
      apply Finset.sum_le_sum
      intro p _
      exact (mul_le_mul_of_nonneg_left (hcap p) (by positivity)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (card_block_le p)) hU)
    _ = (Fintype.card (Pattern τ):ℝ)*((2:ℝ)^Fintype.card ι*U) := by simp
    _ ≤ _ := by
      have hh : (Fintype.card (Pattern τ):ℝ) ≤ (2:ℝ)^(Fintype.card ι*Fintype.card ι) :=
        by exact_mod_cast card_pattern_le τ
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (mul_nonneg (by positivity) hU)

theorem prod_blockCap_le_pow {τ : ι→ℕ} (p : Pattern τ) (C : ι→ℝ) {R : ℝ}
    (hC : ∀i,0 ≤ C i) (hR : 1 ≤ R) (hcap : ∀i,C i ≤ R) :
    (∏q:Block p,blockCap p C q) ≤ R^Fintype.card ι := by
  have hq (q : Block p) : blockCap p C q ≤ ∏i:Fiber p q,R := by
    calc
      _ ≤ ∏i ∈ Finset.univ.erase (anchor p q),R :=
        Finset.prod_le_prod₀ (fun i _ => hC i.val) (fun i _ => hcap i.val)
      _ = R^(Finset.univ.erase (anchor p q)).card := by simp
      _ ≤ R^Fintype.card (Fiber p q) :=
        pow_le_pow_right₀ hR (by simp)
      _ = _ := by simp
  calc
    _ ≤ ∏q:Block p,∏i:Fiber p q,R := by
      exact Finset.prod_le_prod₀
        (fun q _ => Finset.prod_nonneg (fun i _ => hC i.val)) (fun q _ => hq q)
    _ = _ := by
      simpa using Fintype.prod_fiberwise (label p) (fun _ : ι => R)

end Ostmann.Arithmetic.HistoryCompensationPatternBudget

end

end OAI
