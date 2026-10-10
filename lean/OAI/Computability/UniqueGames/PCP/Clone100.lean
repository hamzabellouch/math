import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.PCP.Clone100Triples
import OAI.Computability.UniqueGames.PCP.FoldedEquationLemmas
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Outer.Clone100

open UniqueGamesTheorem.Reduction CloneGap ActualSource
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
  «variables» := input.variables * 100
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
    (a : Fin input.variables → Bool) :
    success (clonedInput input).equations (lift a) = success input.equations a := by
  simp only [success, clonedInput, completeness_count, equations_length, Nat.cast_mul]
  have hn : (input.equations.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (List.length_pos_iff.mpr input.nonempty)
  field_simp

private theorem count_as_sum {A : Type} (xs : List A) (p : A → Bool) :
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
    rw [List.countP_map, count_as_sum]
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
    (a : Fin (clonedInput input).variables → Bool) :
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
    (a : Fin (clonedInput input).variables → Bool) :
    success (clonedInput input).equations a ≤ 4 / 5 := by
  have h := soundness input a
  have hs := hsource (majority a)
  linarith

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      input.variables * 100 + input.equations.length * 970200 + 2 +
        input.equations.length * 970200 * (300 * input.variables + 2) := by
  have h := SourceEncoding.inputBits_length_le (clonedInput input)
  simpa [clonedInput, equations_length, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
