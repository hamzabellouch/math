import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.Finite

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Outer.Clone100Counting

open scoped BigOperators

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def sign (b : Bool) : ℚ := if b then -1 else 1

def bias (f : Index → Bool) : ℚ := (∑ i, sign (f i)) / 100

def majorityBit (f : Index → Bool) : Bool := decide (bias f < 0)

theorem majority_aligned_nonneg (f : Index → Bool) :
    0 ≤ sign (majorityBit f) * bias f := by
  by_cases h : bias f < 0
  · simp [majorityBit, h, sign]
    exact le_of_lt h
  · simpa [majorityBit, h, sign] using le_of_not_gt h

def parityIndicator (a b c rhs : Bool) : ℚ :=
  if (xor (xor a b) c) == rhs then 1 else 0

theorem parityIndicator_nonneg (a b c rhs : Bool) :
    0 ≤ parityIndicator a b c rhs := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_le_one (a b c rhs : Bool) :
    parityIndicator a b c rhs ≤ 1 := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_eq (a b c rhs : Bool) :
    parityIndicator a b c rhs =
      (1 + sign rhs * sign a * sign b * sign c) / 2 := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    norm_num [parityIndicator, sign]

def unconditionedScore (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : Triple, parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs) / 1000000

theorem independent_product_sum (p q r : Index → ℚ) :
    (∑ t : Triple, p t.1 * q t.2.1 * r t.2.2) =
      (∑ i, p i) * (∑ j, q j) * (∑ k, r k) := by
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

theorem unconditionedScore_eq (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs =
      (1 + sign rhs * bias p * bias q * bias r) / 2 := by
  have hp := independent_product_sum
    (fun i => sign (p i)) (fun i => sign (q i)) (fun i => sign (r i))
  have hs : (∑ t : Triple, sign rhs * sign (p t.1) * sign (q t.2.1) * sign (r t.2.2)) =
      sign rhs * ((∑ i, sign (p i)) * (∑ j, sign (q j)) * (∑ k, sign (r k))) := by
    rw [← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  unfold unconditionedScore
  simp_rw [parityIndicator_eq, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  unfold bias
  norm_num
  ring

theorem unconditionedScore_le_one (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤ 1 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset Triple))
    (fun t _ => parityIndicator_le_one (p t.1) (q t.2.1) (r t.2.2) rhs)
  norm_num [Fintype.card_prod, Fintype.card_fin] at h
  unfold unconditionedScore
  linarith

theorem signed_product_of_failure (a b c rhs : Bool) (x y z : ℚ)
    (h : (xor (xor a b) c == rhs) = false) :
    sign rhs * x * y * z = -((sign a * x) * (sign b * y) * (sign c * z)) := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    simp_all [sign]

theorem unconditionedScore_le_half_of_failure (p q r : Index → Bool) (rhs : Bool)
    (h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) = false) :
    unconditionedScore p q r rhs ≤ 1 / 2 := by
  have hn := mul_nonneg
    (mul_nonneg (majority_aligned_nonneg p) (majority_aligned_nonneg q))
    (majority_aligned_nonneg r)
  rw [unconditionedScore_eq,
    signed_product_of_failure (majorityBit p) (majorityBit q) (majorityBit r)
      rhs (bias p) (bias q) (bias r) h]
  linarith

theorem unconditionedScore_le (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 := by
  cases h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) with
  | false =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 0 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi, add_zero]
    exact unconditionedScore_le_half_of_failure p q r rhs h
  | true =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 1 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi]
    norm_num
    exact unconditionedScore_le_one p q r rhs

theorem condition_970200_le {T : Type*} [Fintype T]
    (good : T → Prop) [DecidablePred good]
    (_hT : Fintype.card T = 1000000)
    (hgood : Fintype.card {t : T // good t} = 970200)
    (f : T → ℚ) (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    (∑ t : {t : T // good t}, f t.val) / 970200 ≤
      (∑ t : T, f t) / 1000000 + 3 / 100 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype good f
  have hn : 0 ≤ ∑ t : {t : T // ¬good t}, f t.val :=
    Finset.sum_nonneg (fun t _ => hf0 t.val)
  have hle : (∑ t : {t : T // good t}, f t.val) ≤ ∑ t : T, f t := by
    linarith
  have hcap := Finset.sum_le_sum (s := (Finset.univ : Finset {t : T // good t}))
    (fun t _ => hf1 t.val)
  simp only [Finset.sum_const, Finset.card_univ, hgood, nsmul_eq_mul] at hcap
  norm_num at hcap
  linarith

def conditionedScore (good : Triple → Prop) [DecidablePred good]
    (p q r : Index → Bool) (rhs : Bool) : ℚ :=
  (∑ t : {t : Triple // good t},
    parityIndicator (p t.val.1) (q t.val.2.1) (r t.val.2.2) rhs) / 970200

theorem conditionedScore_le (good : Triple → Prop) [DecidablePred good]
    (hgood : Fintype.card {t : Triple // good t} = 970200)
    (p q r : Index → Bool) (rhs : Bool) :
    conditionedScore good p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 + 3 / 100 := by
  have hcond := condition_970200_le good
    (by norm_num [Fintype.card_prod, Fintype.card_fin]) hgood
    (fun t => parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs)
    (fun t => parityIndicator_nonneg _ _ _ _)
    (fun t => parityIndicator_le_one _ _ _ _)
  have hmaj := unconditionedScore_le p q r rhs
  change conditionedScore good p q r rhs ≤ unconditionedScore p q r rhs + 3 / 100 at hcond
  linarith

end DFVSGames.Outer.Clone100Counting
end

section

namespace DFVSGames.Outer.Clone100Triples

abbrev Index := Fin 100
abbrev Triple := Index × Index × Index

def good (t : Triple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance : DecidablePred good := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

abbrev GoodTriple := {t : Triple // good t}

def toEmbedding (t : GoodTriple) : Fin 3 ↪ Index where
  toFun := ![t.val.1, t.val.2.1, t.val.2.2]
  inj' := by
    have h01 := t.property.1
    have h02 := t.property.2.1
    have h12 := t.property.2.2
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def fromEmbedding (f : Fin 3 ↪ Index) : GoodTriple :=
  ⟨(f 0, f 1, f 2), by
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h)
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h)⟩

def embeddingEquiv : GoodTriple ≃ (Fin 3 ↪ Index) where
  toFun := toEmbedding
  invFun := fromEmbedding
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv f := by
    ext i
    fin_cases i <;> rfl

theorem card_goodTriple : Fintype.card GoodTriple = 970200 := by
  rw [Fintype.card_congr embeddingEquiv, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial_succ]

theorem card_triple : Fintype.card Triple = 1000000 := by
  norm_num [Fintype.card_prod, Fintype.card_fin]

instance : Nonempty GoodTriple :=
  ⟨⟨(0, 1, 2), by decide⟩⟩

end DFVSGames.Outer.Clone100Triples
end

section

namespace DFVSGames.Outer.Clone100

open DFVSGames.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def triples : List GoodTriple := Finset.univ.toList

theorem triples_length : triples.length = 970200 := by
  simp [triples, card_goodTriple]

def clone {N : Type} (e : Equation N) (t : GoodTriple) : Equation (N × Fin 100) :=
  ⟨(e.first, t.val.1), (e.second, t.val.2.1), (e.third, t.val.2.2), e.rhs⟩

theorem clone_distinct {N : Type} (e : Equation N) (t : GoodTriple) :
    (clone e t).first ≠ (clone e t).second ∧
      (clone e t).first ≠ (clone e t).third ∧
      (clone e t).second ≠ (clone e t).third := by
  exact ⟨fun h => t.property.1 (congrArg Prod.snd h),
    fun h => t.property.2.1 (congrArg Prod.snd h),
    fun h => t.property.2.2 (congrArg Prod.snd h)⟩

theorem clone_lift {N : Type} (e : Equation N) (t : GoodTriple) (a : N → Bool) :
    satisfied (clone e t) (fun z => a z.1) = satisfied e a := rfl

def nameEquiv (n : Nat) : Fin n × Fin 100 ≃ Fin (n * 100) := finProdFinEquiv

def equation {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    Equation (Fin (n * 100)) :=
  ⟨nameEquiv n (e.first, t.val.1), nameEquiv n (e.second, t.val.2.1),
    nameEquiv n (e.third, t.val.2.2), e.rhs⟩

theorem equation_distinct {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    (equation e t).first ≠ (equation e t).second ∧
      (equation e t).first ≠ (equation e t).third ∧
      (equation e t).second ≠ (equation e t).third := by
  obtain ⟨h12, h13, h23⟩ := clone_distinct e t
  exact ⟨fun h => h12 ((nameEquiv n).injective h),
    fun h => h13 ((nameEquiv n).injective h),
    fun h => h23 ((nameEquiv n).injective h)⟩

def equations {n : Nat} (es : List (Equation (Fin n))) :
    List (Equation (Fin (n * 100))) :=
  es.flatMap (fun e => triples.map (equation e))

theorem equations_length {n : Nat} (es : List (Equation (Fin n))) :
    (equations es).length = es.length * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.length_append, List.length_map,
      triples_length, List.length_cons] at *
    omega

theorem equations_nonempty {n : Nat} (es : List (Equation (Fin n))) (hne : es ≠ []) :
    equations es ≠ [] := by
  apply List.length_pos_iff.mp
  rw [equations_length]
  exact Nat.mul_pos (List.length_pos_iff.mpr hne) (by decide)

def clonedInput (input : SourceEncoding.Input) : SourceEncoding.Input where
  «variables» := input.«variables» * 100
  equations := equations input.equations
  nonempty := equations_nonempty input.equations input.nonempty

def clonedSource (input : SourceEncoding.Input) : Source :=
  Source.ofList (clonedInput input).equations (clonedInput input).nonempty

theorem clonedSource_distinct (input : SourceEncoding.Input) :
    (clonedSource input).DistinctNames := by
  intro i
  have hm : (clonedInput input).equations[i.val] ∈ equations input.equations :=
    List.getElem_mem i.isLt
  obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, _, he⟩ := List.mem_map.mp ht
  change ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).second ∧
    ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).third ∧
    ((clonedInput input).equations[i.val]).second ≠
      ((clonedInput input).equations[i.val]).third
  rw [← he]
  exact equation_distinct e t

def lift {n : Nat} (a : Fin n → Bool) : Fin (n * 100) → Bool :=
  fun v => a ((nameEquiv n).symm v).1

theorem equation_lift {n : Nat} (e : Equation (Fin n)) (t : GoodTriple)
    (a : Fin n → Bool) : satisfied (equation e t) (lift a) = satisfied e a := by
  simp [equation, lift, satisfied]

theorem completeness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin n → Bool) :
    (equations es).countP (fun e => satisfied e (lift a)) =
      es.countP (fun e => satisfied e a) * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.countP_append, List.countP_map,
      Function.comp_def] at *
    simp_rw [equation_lift]
    rw [CloneGap.count_const, triples_length, ih]
    cases h : satisfied e a <;> simp [h, Nat.add_mul, Nat.add_comm]

def success {n : Nat} (es : List (Equation (Fin n))) (a : Fin n → Bool) : ℚ :=
  (es.countP (fun e => satisfied e a) : ℚ) / es.length

theorem completeness (input : SourceEncoding.Input)
    (a : Fin input.«variables» → Bool) :
    success (clonedInput input).equations (lift a) = success input.equations a := by
  simp only [success, clonedInput, completeness_count, equations_length, Nat.cast_mul]
  have hn : (input.equations.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (List.length_pos_iff.mpr input.nonempty)
  field_simp

private theorem count_as_sum_inline_Clone100 {A : Type} (xs : List A) (p : A → Bool) :
    (xs.countP p : ℚ) = (xs.map (fun x => if p x then (1 : ℚ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h, ih, add_comm]

def majority {n : Nat} (a : Fin (n * 100) → Bool) : Fin n → Bool :=
  fun v => majorityBit (fun i => a (nameEquiv n (v, i)))

theorem equation_count_le {n : Nat} (e : Equation (Fin n))
    (a : Fin (n * 100) → Bool) :
    ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((1 + if satisfied e (majority a) then (1 : ℚ) else 0) / 2 + 3 / 100) := by
  have bound := conditionedScore_le good card_goodTriple
    (fun i => a (nameEquiv n (e.first, i)))
    (fun i => a (nameEquiv n (e.second, i)))
    (fun i => a (nameEquiv n (e.third, i))) e.rhs
  have he : ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) =
      ∑ t : GoodTriple, parityIndicator (a (nameEquiv n (e.first, t.val.1)))
        (a (nameEquiv n (e.second, t.val.2.1)))
        (a (nameEquiv n (e.third, t.val.2.2))) e.rhs := by
    rw [List.countP_map, count_as_sum_inline_Clone100]
    exact (Finset.sum_map_toList (Finset.univ : Finset GoodTriple)
        (fun t => parityIndicator (a (nameEquiv n (e.first, t.val.1)))
          (a (nameEquiv n (e.second, t.val.2.1)))
          (a (nameEquiv n (e.third, t.val.2.2))) e.rhs))
  rw [he]
  unfold conditionedScore at bound
  have hb := (div_le_iff₀ (show (0 : ℚ) < 970200 by norm_num)).mp bound
  rw [mul_comm _ (970200 : ℚ)] at hb
  exact hb

theorem soundness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin (n * 100) → Bool) :
    ((equations es).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((53 / 100 : ℚ) * es.length +
        (es.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    have he := equation_count_le e a
    simp only [equations, List.flatMap_cons, List.countP_append, Nat.cast_add,
      List.length_cons] at *
    cases h : satisfied e (majority a) <;>
      simp [h] at * <;> linarith

theorem soundness (input : SourceEncoding.Input)
    (a : Fin (clonedInput input).«variables» → Bool) :
    success (clonedInput input).equations a ≤
      (1 + success input.equations (majority a)) / 2 + 3 / 100 := by
  have h := soundness_count input.equations a
  have hn : (0 : ℚ) < input.equations.length := by
    exact_mod_cast List.length_pos_iff.mpr input.nonempty
  change (_ : ℚ) / _ ≤ _
  simp only [clonedInput, equations_length, Nat.cast_mul]
  rw [div_le_iff₀ (mul_pos hn (by norm_num))]
  calc
    _ ≤ 970200 * ((53 / 100 : ℚ) * input.equations.length +
        (input.equations.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := h
    _ = _ := by
      unfold success
      field_simp
      ring

theorem soundness_four_fifths (input : SourceEncoding.Input) (ξ : ℚ)
    (hξ : ξ < 1 / 100)
    (hsource : ∀ a, success input.equations a ≤ (1 + ξ) / 2)
    (a : Fin (clonedInput input).«variables» → Bool) :
    success (clonedInput input).equations a ≤ 4 / 5 := by
  have h := soundness input a
  have hs := hsource (majority a)
  linarith

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      input.«variables» * 100 + input.equations.length * 970200 + 2 +
        input.equations.length * 970200 * (300 * input.«variables» + 2) := by
  have h := SourceEncoding.inputBits_length_le (clonedInput input)
  simpa [clonedInput, equations_length, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

end
end DFVSGames.Outer.Clone100

end

section

namespace DFVSGames.Outer.SourceIncidence

open DFVSGames.Reduction ActualSource
open DFVSGames.Foundations Games Target PCP
open DFVSGames.Soundness.IncidenceExtraction
open DFVSGames.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

def incidence (S : Source) : Incidence (Fin S.occurrences) (Fin S.«variables») where
  name := ActualGame.names S
  rhs i := (S.equation i).rhs

theorem names_distinct (S : Source) (hS : S.DistinctNames) :
    ∀ o i j, (incidence S).name o i = (incidence S).name o j → i = j := by
  intro o i j hij
  obtain ⟨h12, h13, h23⟩ := hS o
  fin_cases i <;> fin_cases j <;>
    simp_all [incidence, ActualGame.names, eq_comm]

private theorem uniform_probability_eq_expect_inline_SourceIncidence {n : Nat} [Nonempty (Fin n)]
    (p : Fin n → Bool) :
    (FiniteDistribution.uniform (Fin n)).probability p =
      (Finset.univ.expect (fun i => if p i then (1 : ℚ) else 0) : ℚ) := by
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform, Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases p i <;> simp

theorem paritySuccess_eq (S : Source) (a : Fin S.«variables» → Bool) :
    paritySuccess (incidence S) (FiniteDistribution.uniform (Fin S.occurrences)) a =
      (((S.sourceList.countP (fun e => CloneGap.satisfied e a) : ℚ) /
        S.occurrences : ℚ) : ℝ) := by
  unfold paritySuccess
  rw [uniform_probability_eq_expect_inline_SourceIncidence]
  have hevent (o : Fin S.occurrences) :
      decide (xorTriple (fun i => a ((incidence S).name o i)) = (incidence S).rhs o) =
        S.satisfied a o := by
    have hb : ∀ x y : Bool, decide (x = y) = (x == y) := by decide
    exact hb _ _
  simp_rw [hevent]
  rw [IncidenceProbability.expect_bool_indicator_eq_count_ofFn]
  congr 2
  have hm : List.ofFn (S.satisfied a) =
      S.sourceList.map (fun e => CloneGap.satisfied e a) := by
    simp [Source.sourceList, List.map_ofFn, Function.comp_def]
    rfl
  simp [hm, List.countP_map]

theorem paritySuccess_input (input : SourceEncoding.Input)
    (a : Fin input.«variables» → Bool) :
    paritySuccess (incidence (HastadSource.asSource input))
      (FiniteDistribution.uniform (Fin (HastadSource.asSource input).occurrences)) a =
      (Clone100.success input.equations a : ℝ) := by
  have h := paritySuccess_eq (HastadSource.asSource input) a
  rw [show (HastadSource.asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def input (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  Clone100.clonedInput (HastadSource.output H ξ hξ F)

def source (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : Source := HastadSource.asSource (input H ξ hξ F)

theorem source_distinct (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : (source H ξ hξ F).DistinctNames :=
  Clone100.clonedSource_distinct (HastadSource.output H ξ hξ F)

theorem source_complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ a, 1 - (ξ : ℝ) ≤ paritySuccess (incidence (source H ξ hξ F))
      (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences)) a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ F hF
  refine ⟨Clone100.lift a, ?_⟩
  have hvalue : 1 - ξ ≤ Clone100.success (input H ξ hξ F).equations
      (Clone100.lift a) := by
    change 1 - ξ ≤ Clone100.success
      (Clone100.clonedInput (HastadSource.output H ξ hξ F)).equations (Clone100.lift a)
    rw [Clone100.completeness]
    exact ha
  have hreal : 1 - (ξ : ℝ) ≤
      (Clone100.success (input H ξ hξ F).equations (Clone100.lift a) : ℝ) := by
    exact_mod_cast hvalue
  exact hreal.trans_eq (paritySuccess_input (input H ξ hξ F) (Clone100.lift a)).symm

theorem source_sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (hξsmall : ξ < 1 / 100)
    (F : Formula) (hF : ¬ F.Satisfiable) :
    parityValue (incidence (source H ξ hξ F))
      (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences)) ≤ 4 / 5 := by
  unfold parityValue
  apply Finset.sup'_le
  intro a _
  have h := Clone100.soundness_four_fifths (HastadSource.output H ξ hξ F) ξ hξsmall
    (HastadSource.sound H certificate ξ hξ F hF) a
  have hq : Clone100.success (input H ξ hξ F).equations a ≤ (4 / 5 : ℚ) := h
  have hreal : (Clone100.success (input H ξ hξ F).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (paritySuccess_input (input H ξ hξ F) a).trans_le hreal

def ordinaryGame (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) :=
  fourAnswerGame (incidence (source H ξ hξ F))
    (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences))

theorem ordinaryGame_projection (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : DFVSGames.Repetition.IsProjection (ordinaryGame H ξ hξ F) :=
  fourAnswerGame_isProjection _ _ (names_distinct _ (source_distinct H ξ hξ F))

theorem ordinaryGame_sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (hξsmall : ξ < 1 / 100)
    (F : Formula) (hF : ¬ F.Satisfiable) :
    (ordinaryGame H ξ hξ F).value ≤ 14 / 15 :=
  fourAnswerGame_value_le_fourteen_fifteenths _ _
    (names_distinct _ (source_distinct H ξ hξ F))
    (source_sound H certificate ξ hξ hξsmall F hF)

end
end DFVSGames.Outer.SourceIncidence

end

section

namespace DFVSGames.Explicit.MachineClone100Table

open DFVSGames.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end DFVSGames.Explicit.MachineClone100Table
end

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end DFVSGames.Explicit.MachineClone100Model
end

section

namespace DFVSGames.Explicit.MachineClone100Context

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

def contextTapes (triples : List (Nat × Nat × Nat)) (context : Context triples.length)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed
    ((MachineTransducer.output (fun control _ => control) (emission triples)
      context (base (contextSource context))).reverse ++ base .reversed)

@[simp] theorem contextTapes_reversed (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .reversed =
      (MachineTransducer.output (fun control _ => control) (emission triples)
        context (base (contextSource context))).reverse ++ base .reversed := by
  simp [contextTapes]

theorem contextTapes_other (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) (tape : Tape)
    (different : tape ≠ .reversed) :
    contextTapes triples context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base (contextSource context) = base (contextSource context) :=
  contextTapes_other triples context base _ (contextSource_ne_reversed context)

@[simp] theorem contextTapes_scratch (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .scratch = base .scratch :=
  contextTapes_other triples context base _ (by decide)

theorem setupStep (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (state : State triples.length) :
    TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
        3 * (base (contextSource context)).length + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState _, contextTapes triples context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    (defaultControl triples.length) (fun control _ => control) (emission triples)
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) (program triples nonempty)
    rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program triples nonempty)))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

def contextInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState _, contextTapes triples context base⟩)
      (3 * (base (contextSource context)).length + 3) where
  steps := 3 * (base (contextSource context)).length + 3
  evals_in_steps := contextTrace triples nonempty context base scratchEmpty state
  steps_le_m := Nat.le_refl _

@[simp] theorem contextInTime_steps (triples : List (Nat × Nat × Nat))
    (nonempty : triples ≠ []) (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (contextInTime triples nonempty context base scratchEmpty state).steps =
      3 * (base (contextSource context)).length + 3 := rfl

end DFVSGames.Explicit.MachineClone100Context
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
