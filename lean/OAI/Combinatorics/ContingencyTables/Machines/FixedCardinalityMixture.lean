import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityBits
import OAI.Combinatorics.ContingencyTables.Transport.FiniteScaledDraw
import OAI.Combinatorics.ContingencyTables.Machines.InitialLocalChoices

namespace OAI

/-! # The uniform-size mixture realizes the initial factorial weights

A size is drawn uniformly from 0,...,n, followed by the sequential
fixed-cardinality draw. Its subset mass is the literal local factorial
weight divided by n+1. The bounded Boolean implementation uses a fresh
word for the size and for each inclusion decision.
-/

namespace ContingencyTables.FixedCardinalityMixture

open ResidualMixture FirstSuccess FairBits FixedCardinalityLaw FixedCardinalityBits
open scoped BigOperators Classical
noncomputable section

def sizeMixture (n : ℕ) : RationalLaw (Fin n → Bool) :=
  bindLaw (uniformLaw (α := Fin (n+1))) (fun k => fixedLaw n k.val)

theorem sizeMixture_mass (n : ℕ) (v : Fin n → Bool) :
    (sizeMixture n).mass v=factorialMass n (count v)/(n+1) := by
  let k₀ : Fin (n+1) := ⟨count v,Nat.lt_succ_of_le (count_le v)⟩
  have hiff (k : Fin (n+1)) : count v=k.val ↔ k=k₀ := by
    constructor
    · intro h; apply Fin.ext; exact h.symm
    · intro h; subst k; rfl
  change (∑ k : Fin (n+1),(uniformLaw (α := Fin (n+1))).mass k*
    (fixedLaw n k.val).mass v)=_
  simp_rw [fixedLaw_mass n _ (Nat.le_of_lt_succ (Fin.isLt _)) v,hiff]
  simp [uniformLaw,uniformMass,k₀,mul_comm,div_eq_mul_inv]

def subsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun v := Finset.univ.filter (fun i => v i=true)
  invFun S i := decide (i∈S)
  left_inv v := by
    funext i
    cases h : v i <;> simp [h]
  right_inv S := by ext i; simp

lemma count_subset_inverse (n : ℕ) (S : Finset (Fin n)) :
    count ((subsetEquiv n).symm S)=S.card := by
  change (∑ i : Fin n,if decide (i∈S) then 1 else 0)=S.card
  simp only [decide_eq_true_eq]
  rw [←Finset.sum_filter]
  simp

def localLaw (n : ℕ) : RationalLaw (Finset (Fin n)) :=
  equivLaw (subsetEquiv n) (sizeMixture n)

theorem localLaw_mass (n : ℕ) (S : Finset (Fin n)) :
    (localLaw n).mass S=factorialMass n S.card/(n+1) := by
  change (sizeMixture n).mass ((subsetEquiv n).symm S)=_
  rw [sizeMixture_mass,count_subset_inverse]

theorem localLaw_mass_cast (n : ℕ) (S : Finset (Fin n)) :
    ((localLaw n).mass S:ℝ)=InitialLocalChoices.localWeight n 0 0 S/(n+1) := by
  rw [localLaw_mass]
  simp [factorialMass,InitialLocalChoices.localWeight,Rat.cast_div,Rat.cast_mul]

def roundedSizeMixture (B n : ℕ) : RationalLaw (Fin n → Bool) :=
  bindLaw (scaledLaw (n+1) B (Nat.succ_pos n))
    (fun k => roundedFixedLaw B n k.val)

lemma uniformInt_eq (n : ℕ) :
    uniformIntLaw (n+1) (Nat.succ_pos n)=uniformLaw (α := Fin (n+1)) := by
  apply RationalLaw.ext
  funext k
  simp [uniformIntLaw,uniformLaw,uniformMass]

theorem roundedSizeMixture_error (B n : ℕ) :
    variation (roundedSizeMixture B n) (sizeMixture n)≤
      (n+1:ℚ)/(2*(2:ℚ)^B)+(n:ℚ)/(2:ℚ)^B := by
  have h := variation_bind_uniform
    (scaledLaw (n+1) B (Nat.succ_pos n)) (uniformLaw (α := Fin (n+1)))
    (fun k => roundedFixedLaw B n k.val) (fun k => fixedLaw n k.val)
    ((n:ℚ)/(2:ℚ)^B) (fun k => roundedFixed_error B n k.val)
  have hs := scaledLaw_variation (n+1) B (Nat.succ_pos n)
  rw [uniformInt_eq] at hs
  have hs' : variation (scaledLaw (n+1) B (Nat.succ_pos n)) (uniformLaw (α := Fin (n+1)))≤
      (n+1:ℚ)/(2*(2:ℚ)^B) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  exact h.trans (_root_.add_le_add hs' le_rfl)

def drawBits (B n : ℕ) := B+n*B

def vectorDraw (B n : ℕ) (bits : Fin (drawBits B n) → Bool) : Fin n → Bool :=
  let words := splitWordEquiv B (n*B) bits
  bitDraw B n (scaledBitInteger (n+1) B (Nat.succ_pos n) words.1).val words.2

theorem vectorDraw_law (B n : ℕ) :
    mapLaw (uniformLaw (α := Fin (drawBits B n) → Bool)) (vectorDraw B n)=
      roundedSizeMixture B n := by
  let drawSize := scaledBitInteger (n+1) B (Nat.succ_pos n)
  let finish (k : Fin (n+1)) := bitDraw B n k.val
  have he := map_equiv (splitWordEquiv B (n*B))
    (uniformLaw (α := Fin (B+n*B) → Bool))
    (fun words => finish (drawSize words.1) words.2)
  rw [uniform_equiv,←uniform_product] at he
  have hb := mapLaw_product_finish (uniformLaw (α := Fin B → Bool))
    (uniformLaw (α := Fin (n*B) → Bool)) drawSize finish
  have hsize : mapLaw (uniformLaw (α := Fin B → Bool)) drawSize=
      scaledLaw (n+1) B (Nat.succ_pos n) := scaledBitIntegerLaw_eq _ _ _
  have hfinish : (fun k => mapLaw (uniformLaw (α := Fin (n*B) → Bool)) (finish k))=
      (fun k : Fin (n+1) => roundedFixedLaw B n k.val) := by
    funext k
    exact bitDraw_law B n k.val
  rw [hsize,hfinish] at hb
  exact he.symm.trans hb

def subsetDraw (B n : ℕ) (bits : Fin (drawBits B n) → Bool) : Finset (Fin n) :=
  subsetEquiv n (vectorDraw B n bits)

theorem subsetDraw_error (B n : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (drawBits B n) → Bool)) (subsetDraw B n))
      (localLaw n)≤(n+1:ℚ)/(2*(2:ℚ)^B)+(n:ℚ)/(2:ℚ)^B := by
  have he := mapLaw_equiv_output (subsetEquiv n)
    (uniformLaw (α := Fin (drawBits B n) → Bool)) (vectorDraw B n)
  change variation (mapLaw _ (fun bits => subsetEquiv n (vectorDraw B n bits))) _≤_
  rw [he,vectorDraw_law,localLaw,variation_equiv]
  exact roundedSizeMixture_error B n

end
end ContingencyTables.FixedCardinalityMixture

end OAI
