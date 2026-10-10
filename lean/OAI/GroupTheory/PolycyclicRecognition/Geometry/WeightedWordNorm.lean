import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Basic.NNReal.Basic

namespace OAI

/-! # Norms obtained by assigning costs to group elements

The infimum of the costs of finite product expressions is subadditive.
A pre-existing group norm below the costs guarantees separation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

open Set
variable {G : Type*} (c : G → ℝ≥0)

/-- Total cost of a product expression. -/
def productCost (l : List G) : ℝ≥0 := (l.map c).sum

@[simp] theorem productCost_nil : productCost c [] = 0 := rfl
@[simp] theorem productCost_cons (g : G) (l : List G) :
    productCost c (g :: l) = c g + productCost c l := rfl
@[simp] theorem productCost_append (l m : List G) :
    productCost c (l ++ m) = productCost c l + productCost c m := by
  simp [productCost]

variable [Group G]

/-- Weighted word norm, allowing every finite product expression. -/
def weightedWordNorm (g : G) : ℝ≥0 :=
  ⨅ l : {l : List G // l.prod = g}, productCost c l.val

private instance productExpression_nonempty (g : G) : Nonempty {l : List G // l.prod = g} :=
  ⟨⟨[g], by simp⟩⟩

theorem weightedWordNorm_le_cost (l : List G) :
    weightedWordNorm c l.prod ≤ productCost c l :=
  by
    unfold weightedWordNorm
    exact ciInf_le (f := fun z : {w : List G // w.prod = l.prod} => productCost c z.val)
      (OrderBot.bddBelow _) ⟨l, rfl⟩

theorem weightedWordNorm_le (g : G) : weightedWordNorm c g ≤ c g := by
  simpa using weightedWordNorm_le_cost c [g]

@[simp] theorem weightedWordNorm_one : weightedWordNorm c 1 = 0 := by
  exact le_antisymm (by simpa using weightedWordNorm_le_cost c []) (zero_le)

theorem weightedWordNorm_mul (g h : G) :
    weightedWordNorm c (g * h) ≤ weightedWordNorm c g + weightedWordNorm c h := by
  apply NNReal.le_iInf_add_iInf
  intro l m
  simpa only [List.prod_append, l.property, m.property, productCost_append] using
    weightedWordNorm_le_cost c (l.val ++ m.val)

theorem exists_productCost_lt (g : G) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ l : List G, l.prod = g ∧ productCost c l < weightedWordNorm c g + ε := by
  have h : weightedWordNorm c g < weightedWordNorm c g + ε := lt_add_of_pos_right _ hε
  rw [weightedWordNorm] at h
  obtain ⟨l, hl⟩ := (ciInf_lt_iff (OrderBot.bddBelow _)).mp h
  exact ⟨l.val, l.property, hl⟩

variable (hinv : ∀ g, c g⁻¹ = c g)

include hinv in
theorem productCost_inv_reverse (l : List G) :
    productCost c (l.map Inv.inv).reverse = productCost c l := by
  simp only [productCost, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  exact hinv g

include hinv in
theorem weightedWordNorm_inv_le (g : G) : weightedWordNorm c g⁻¹ ≤ weightedWordNorm c g := by
  apply le_ciInf
  intro l
  have hp : (l.val.map Inv.inv).reverse.prod = g⁻¹ := by
    rw [← List.prod_inv_reverse, l.property]
  simpa only [hp, productCost_inv_reverse c hinv] using
    weightedWordNorm_le_cost c (l.val.map Inv.inv).reverse

include hinv in
@[simp] theorem weightedWordNorm_inv (g : G) : weightedWordNorm c g⁻¹ = weightedWordNorm c g := by
  exact le_antisymm (weightedWordNorm_inv_le c hinv g)
    (by simpa using weightedWordNorm_inv_le c hinv g⁻¹)

def weightedWordSeminorm : GroupSeminorm G where
  toFun g := weightedWordNorm c g
  map_one' := by simp
  inv' g := congrArg (fun r : ℝ≥0 => (r : ℝ)) (weightedWordNorm_inv c hinv g)
  mul_le' g h := by exact_mod_cast weightedWordNorm_mul c g h

theorem seminorm_product_le_cost (p : GroupSeminorm G) (hc : ∀ g, p g ≤ c g) (l : List G) :
    p l.prod ≤ productCost c l := by
  induction l with
  | nil => simp
  | cons g l ih =>
    change p (g * l.prod) ≤ (c g : ℝ) + (productCost c l : ℝ)
    exact (p.mul_le' _ _).trans (add_le_add (hc g) ih)

theorem seminorm_le_weightedWordNorm (p : GroupSeminorm G) (hc : ∀ g, p g ≤ c g) (g : G) :
    p g ≤ weightedWordNorm c g := by
  rw [weightedWordNorm, NNReal.coe_iInf]
  apply le_ciInf
  intro l
  simpa only [l.property] using seminorm_product_le_cost c p hc l.val

/-- A norm below the assigned costs makes the weighted seminorm a norm. -/
def weightedWordGroupNorm (p : GroupNorm G) (hc : ∀ g, p g ≤ c g) : GroupNorm G where
  toGroupSeminorm := weightedWordSeminorm c hinv
  eq_one_of_map_eq_zero' g hg := by
    apply p.eq_one_of_map_eq_zero'
    apply le_antisymm ?_ (apply_nonneg p g)
    exact (seminorm_le_weightedWordNorm c p.toGroupSeminorm hc g).trans_eq hg

end PolycyclicRecognition

end

end OAI
