import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SizedSet

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.FactorialAssignments
open Finset Classical
variable {P T : Type*} [Fintype P] [Fintype T] (j : T → ℕ)

abbrev FlatSlot := (t : T) × Fin (j t)

local instance flatSlotDec : DecidableEq (FlatSlot j) := Classical.decEq _

def flatten : Slots (P := P) j ≃ (FlatSlot j → P) where
  toFun x s := x s.1 s.2
  invFun x t i := x ⟨t,i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def namedFlat (x : Named (P := P) j) : FlatSlot j → P := flatten j (realize j x)

omit [Fintype P] [Fintype T] in
lemma namedFlat_injective : Function.Injective (namedFlat (P := P) j) :=
  (flatten j).injective.comp (realize_injective j)

omit [Fintype P] in
lemma unorderedWeight_flat (W : T → P → ℝ) (x : Named (P := P) j) :
    unorderedWeight j W (forget j x) = ∏ s : FlatSlot j, W s.1 (namedFlat j x s) := by
  rw [unorderedWeight_forget]
  exact (Fintype.prod_sigma (fun (s : FlatSlot j) => W s.1 (namedFlat j x s))).symm

theorem unordered_gated_sum (V : Unordered (P := P) j → Prop)
    (W : T → P → ℝ) (hW : ∀ t p, 0 ≤ W t p)
    (G : (FlatSlot j → P) → ℝ) (hG : ∀ x, 0 ≤ G x)
    (hVG : ∀ x : Named (P := P) j, V (forget j x) → G (namedFlat j x) = 1) :
    (∑ q : Unordered (P := P) j, if V q then unorderedWeight j W q else 0) ≤
      (∑ x : FlatSlot j → P, G x * ∏ s, W s.1 (x s)) /
        (∏ t, (j t).factorial : ℕ) := by
  rw [factorial_quotient]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnonneg (x : FlatSlot j → P) : 0 ≤ G x * ∏ s, W s.1 (x s) :=
    mul_nonneg (hG x) (prod_nonneg (fun s _ => hW s.1 _))
  calc
    _ ≤ ∑ x : Named (P := P) j, G (namedFlat j x) * ∏ s, W s.1 (namedFlat j x s) := by
      apply sum_le_sum
      intro x hx
      by_cases hv : V (forget j x)
      · rw [ite_eq_left hv,hVG x hv,one_mul,unorderedWeight_flat]
      · rw [ite_eq_right hv]
        exact hnonneg _
    _ = ∑ x ∈ univ.image (namedFlat (P := P) j), G x * ∏ s, W s.1 (x s) :=
      (sum_image (f := fun x => G x * ∏ s, W s.1 (x s))
        (s := univ) (fun x _ y _ he => namedFlat_injective j he)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => hnonneg x)

end OrdinaryCorrelations.FactorialAssignments

end

end OAI
