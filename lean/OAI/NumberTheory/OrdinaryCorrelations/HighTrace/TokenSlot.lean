import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllSlotMasses
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FlatSlot

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.PivotSummation
open OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
variable {h ℓ : ℕ} {w : ClosedLine h ℓ} {S : PrimeSystem}

local instance tokenTypeDec (w : ClosedLine h ℓ) : DecidableEq (TokenType w) := Classical.decEq _
local instance primeIndexDec (S : PrimeSystem) : DecidableEq S.Index := Classical.decEq _

abbrev TokenSlot (j : TokenType w → ℕ) := FactorialAssignments.FlatSlot j

local instance tokenSlotDec (j : TokenType w → ℕ) : DecidableEq (TokenSlot j) := Classical.decEq _

def slotShape (j : TokenType w → ℕ) (s : TokenSlot j) : Shape w := s.1.2

def slotCore (j : TokenType w → ℕ) (s : TokenSlot j) : Prop := s.1.1 = true

def unorderedEdgeProduct (j : TokenType w → ℕ)
    (U : FactorialAssignments.Unordered (P := S.Index) j) (e : Fin ℓ) : ℝ :=
  ∏ t : TokenType w, if e ∈ t.2.edges.val then ∏ p ∈ (U t).val, (p.val : ℝ) else 1

def unorderedBins (j : TokenType w → ℕ)
    (C : Fin ℓ → ℝ) (H τ : ℝ) (U : FactorialAssignments.Unordered (P := S.Index) j) : Prop :=
  ∀ e ∈ w.treeSteps, H < C e * unorderedEdgeProduct j U e ∧
    C e * unorderedEdgeProduct j U e ≤ τ*H

lemma slotEdgeProduct_named (j : TokenType w → ℕ)
    (x : FactorialAssignments.Named (P := S.Index) j) (e : Fin ℓ) :
    slotEdgeProduct (slotShape j) S (FactorialAssignments.namedFlat j x) e =
      unorderedEdgeProduct j (FactorialAssignments.forget j x) e := by
  let : DecidableEq S.Index := Classical.decEq _
  unfold slotEdgeProduct unorderedEdgeProduct
  rw [Fintype.prod_sigma]
  apply prod_congr rfl
  intro t ht
  by_cases he : e ∈ t.2.edges.val
  · simp only [slotShape,he,ite_true,FactorialAssignments.forget,
      FactorialAssignments.forgetBlock]
    rw [prod_image (fun i _ k _ hik => (x t).injective hik)]
    apply prod_congr rfl
    intro i hi
    rfl
  · simp only [slotShape,he,ite_false,prod_const_one]

lemma pivotBinIndicator_nonneg (j : TokenType w → ℕ)
    (C : Fin ℓ → ℝ) (H τ : ℝ) (x : TokenSlot j → S.Index) :
    0 ≤ pivotBinIndicator (slotShape j) (slotCore j) S C H τ x := by
  unfold pivotBinIndicator
  apply prod_nonneg
  intro i hi
  split_ifs <;> norm_num

lemma unorderedBins_gate (j : TokenType w → ℕ)
    (C : Fin ℓ → ℝ) (H τ : ℝ) (x : FactorialAssignments.Named (P := S.Index) j)
    (hx : unorderedBins j C H τ (FactorialAssignments.forget j x)) :
    pivotBinIndicator (slotShape j) (slotCore j) S C H τ (FactorialAssignments.namedFlat j x) = 1 := by
  unfold pivotBinIndicator
  apply prod_eq_one
  intro i hi
  rw [slotEdgeProduct_named]
  have he : (slotShape j (orderedPivot (slotShape j) (slotCore j) i)).topEdge ∈ w.treeSteps :=
    Shape.grows _ |>.1 (Shape.topEdge_mem _)
  exact ite_eq_left (hx _ he)

lemma token_constants_product (j : TokenType w → ℕ) (u : TokenType w → ℝ)
    (x : TokenSlot j → S.Index) :
    (∏ s : TokenSlot j, u s.1 * slotWeight S (slotCore j s) (x s)) =
      (∏ t, u t ^ j t) * ∏ s : TokenSlot j, slotWeight S (slotCore j s) (x s) := by
  rw [prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  simp only [prod_const,card_univ,Fintype.card_fin]

lemma slot_mass_product (j : TokenType w → ℕ) (vC vZ : ℝ) :
    (∏ s : TokenSlot j, if slotCore j s then vC else vZ) =
      ∏ t : TokenType w, tokenMass w vC vZ t ^ j t := by
  rw [Fintype.prod_sigma]
  apply prod_congr rfl
  intro t ht
  cases he : t.1 <;> simp [slotCore,tokenMass,he]

lemma token_gated_sum (j : TokenType w → ℕ) (u : TokenType w → ℝ)
    (C : Fin ℓ → ℝ) (H τ : ℝ) :
    (∑ x : TokenSlot j → S.Index,
      pivotBinIndicator (slotShape j) (slotCore j) S C H τ x *
        ∏ s : TokenSlot j, u s.1 * slotWeight S (s.1.1=true) (x s)) =
    (∏ t, u t ^ j t) *
      (∑ x : TokenSlot j → S.Index,
        pivotBinIndicator (slotShape j) (slotCore j) S C H τ x *
        ∏ s : TokenSlot j, slotWeight S (slotCore j s) (x s)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  change _ * (∏ s : TokenSlot j, u s.1 * slotWeight S (slotCore j s) (x s)) = _
  rw [token_constants_product]
  ring

lemma token_mass_algebra (j : TokenType w → ℕ) (u : TokenType w → ℝ) (vC vZ K : ℝ) :
    (∏ t, u t ^ j t) * (K * ∏ s : TokenSlot j, if slotCore j s then vC else vZ) =
      K * ∏ t : TokenType w, (tokenMass w vC vZ t * u t) ^ j t := by
  rw [slot_mass_product]
  simp_rw [mul_pow]
  rw [prod_mul_distrib]
  ring

def tokenNamedSum (S : PrimeSystem) (j : TokenType w → ℕ)
    (u : TokenType w → ℝ) (C : Fin ℓ → ℝ) (H τ : ℝ) : ℝ :=
  ∑ x : TokenSlot j → S.Index,
    pivotBinIndicator (slotShape j) (slotCore j) S C H τ x *
      ∏ s : TokenSlot j, u s.1 * slotWeight S (s.1.1=true) (x s)

def tokenMassProduct (j : TokenType w → ℕ) (vC vZ : ℝ) (u : TokenType w → ℝ) : ℝ :=
  ∏ t : TokenType w, (tokenMass w vC vZ t * u t) ^ j t

def tokenFactorialProduct (j : TokenType w → ℕ) (vC vZ : ℝ) (u : TokenType w → ℝ) : ℝ :=
  ∏ t : TokenType w, (tokenMass w vC vZ t * u t) ^ j t / (j t).factorial

def unorderedTokenSum (S : PrimeSystem) (j : TokenType w → ℕ)
    (u : TokenType w → ℝ) (C : Fin ℓ → ℝ) (H τ : ℝ)
    (V : FactorialAssignments.Unordered (P := S.Index) j → Prop) : ℝ :=
  ∑ U : FactorialAssignments.Unordered (P := S.Index) j,
    if V U ∧ unorderedBins j C H τ U then
      FactorialAssignments.unorderedWeight j
        (fun t p => u t * slotWeight S (t.1=true) p) U else 0

def NamedTokenBound (S : PrimeSystem) (K τ : ℝ) : Prop :=
  ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ) (j : TokenType w → ℕ)
    (C : Fin ℓ → ℝ), (∀ e, 0 < C e) → ∀ H : ℝ,
    ∀ (u : TokenType w → ℝ), (∀ t, 0 ≤ u t) →
    tokenNamedSum S j u C H τ ≤
      K^(pivotEdges (slotShape j) (slotCore j)).card *
        tokenMassProduct j S.harmonicCore S.harmonicCenter u

def PrimeNamedBound (S : PrimeSystem) (K τ : ℝ) : Prop :=
  ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ) (σ : Type) [Fintype σ],
    ∀ (q : σ → Shape w) (core : σ → Prop) (C : Fin ℓ → ℝ),
    (∀ e, 0 < C e) → ∀ H : ℝ,
    (∑ x : σ → S.Index, pivotBinIndicator q core S C H τ x *
      ∏ s, slotWeight S (core s) (x s)) ≤
      K^(pivotEdges q core).card *
        ∏ s : σ, if core s then S.harmonicCore else S.harmonicCenter

lemma namedTokenBound_of_prime (S : PrimeSystem) (K τ : ℝ)
    (hB : PrimeNamedBound S K τ) : NamedTokenBound S K τ := by
  intro h ℓ w j C hC H u hu
  unfold tokenNamedSum tokenMassProduct
  rw [token_gated_sum]
  have hp := hB h ℓ w (TokenSlot j) (slotShape j) (slotCore j) C hC H
  have h0 : 0 ≤ ∏ t, u t ^ j t := prod_nonneg (fun t _ => pow_nonneg (hu t) _)
  have he := mul_le_mul_of_nonneg_left hp h0
  rw [token_mass_algebra] at he
  exact he

lemma source_token_named_sum (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, NamedTokenBound (sourceSystem B)
      (((Real.log 4+1)*τ)/B^(1-eta)) τ := by
  filter_upwards [source_named_prime_sum τ hτ] with B hB
  exact namedTokenBound_of_prime _ _ _ hB

def UnorderedTokenBound (S : PrimeSystem) (K τ : ℝ) : Prop :=
  ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ) (j : TokenType w → ℕ)
    (C : Fin ℓ → ℝ), (∀ e, 0 < C e) → ∀ H : ℝ,
    ∀ (V : FactorialAssignments.Unordered (P := S.Index) j → Prop)
      (u : TokenType w → ℝ), (∀ t, 0 ≤ u t) →
    unorderedTokenSum S j u C H τ V ≤
      K^(pivotEdges (slotShape j) (slotCore j)).card *
        tokenFactorialProduct j S.harmonicCore S.harmonicCenter u

lemma unorderedTokenBound_of_named (S : PrimeSystem) (K τ : ℝ)
    (hB : NamedTokenBound S K τ) : UnorderedTokenBound S K τ := by
  intro h ℓ w j C hC H V u hu
  have hg := FactorialAssignments.unordered_gated_sum j
    (fun U => V U ∧ unorderedBins j C H τ U)
    (fun t p => u t * slotWeight S (t.1=true) p)
    (fun t p => mul_nonneg (hu t) (slotWeight_nonneg _ _ _))
    (pivotBinIndicator (slotShape j) (slotCore j) S C H τ)
    (pivotBinIndicator_nonneg j C H τ)
    (fun x hx => unorderedBins_gate j C H τ x hx.2)
  have hp := hB h ℓ w j C hC H u hu
  have hd : 0 ≤ ((∏ t : TokenType w, (j t).factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc := hg.trans (div_le_div_of_nonneg_right hp hd)
  unfold unorderedTokenSum
  convert hc using 1
  · apply Finset.sum_congr rfl
    intro U hU
    by_cases hv : V U ∧ unorderedBins j C H τ U <;> simp only [hv,ite_false]
  · unfold tokenMassProduct tokenFactorialProduct
    rw [prod_div_distrib,← Nat.cast_prod,mul_div_assoc]

theorem source_unordered_prime_sum (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, UnorderedTokenBound (sourceSystem B)
      (((Real.log 4+1)*τ)/B^(1-eta)) τ := by
  filter_upwards [source_token_named_sum τ hτ] with B hB
  exact unorderedTokenBound_of_named _ _ _ hB

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
