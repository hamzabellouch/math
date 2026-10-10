import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Reduction.OccurrenceGame
import OAI.Computability.PerfectCompleteness.Reduction.Value

namespace OAI


namespace PerfectCompleteness
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

namespace Instance

noncomputable def occurrenceGame {q : Nat} (G : Instance q) :
    OccurrenceGame (Fin G.edges.length) (Fin G.leftVertices) (Fin G.rightVertices)
      (Fin (2 * q)) (Fin q) where
  occurrences :=
    { weight := fun _ => (G.edges.length : ℝ)⁻¹
      nonnegative := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      normalized := by
        have h : (G.edges.length : ℝ) ≠ 0 := by
          exact_mod_cast G.edgeCount_positive.ne'
        simp [h] }
  left := fun i => G.edges[i].left
  right := fun i => G.edges[i].right
  accepts := fun i a b => decide (G.edges[i].projection.images[a] = b)

theorem countSatisfied_eq_sum {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) (es : List (Edge l r q)) :
    (countSatisfied a b es : ℝ) =
      ∑ i : Fin es.length, if es[i].satisfied a b then (1 : ℝ) else 0 := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    simp only [List.length_cons, Fin.sum_univ_succ]
    cases h : e.satisfied a b <;> simp [countSatisfied, ih, h]

theorem occurrenceGame_success {q : Nat} (G : Instance q) (s : Labeling G) :
    G.occurrenceGame.success s =
      (countSatisfied s.1 s.2 G.edges : ℝ) / G.edges.length := by
  rw [countSatisfied_eq_sum, div_eq_mul_inv, Finset.sum_mul]
  unfold OccurrenceGame.success FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro i _
  change (if G.edges[i].satisfied s.1 s.2 then (G.edges.length : ℝ)⁻¹ else 0) = _
  cases h : G.edges[i].satisfied s.1 s.2 <;> simp

theorem occurrenceGame_value {q : Nat} (G : Instance q) [Nonempty (Fin q)] :
    letI : Nonempty (Fin (2 * q)) := ⟨⟨0, by
      have hq : 0 < q := Fin.pos_iff_nonempty.mpr (inferInstance : Nonempty (Fin q))
      omega⟩⟩
    G.occurrenceGame.value = G.value := by
  have hq : 0 < q := Fin.pos_iff_nonempty.mpr inferInstance
  let : Nonempty (Fin (2 * q)) := ⟨⟨0, by omega⟩⟩
  apply le_antisymm
  · apply (G.occurrenceGame.value_le_iff _).2
    intro s
    rw [G.occurrenceGame_success]
    exact G.rate_le_value s
  · obtain ⟨s, hs⟩ := G.maxSatisfied_attained hq
    have h := G.occurrenceGame.success_le_value s
    rw [G.occurrenceGame_success, hs] at h
    exact h

end Instance
end PerfectCompleteness



namespace PerfectCompleteness.WeightRounding

open scoped BigOperators

def paperScale (m : Nat) (δ : ℚ) : Nat := ⌈3 * (m : ℚ) / δ⌉₊

theorem paperScale_positive {m : Nat} (hm : 0 < m) {δ : ℚ} (hδ : 0 < δ) :
    0 < paperScale m δ := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have h : 1 ≤ paperScale m δ := (Nat.one_le_ceil_iff).2 (by positivity)
  omega

theorem paperScale_error {m : Nat} (hm : 0 < m) {δ : ℚ} (hδ : 0 < δ) :
    (m : ℚ) / paperScale m δ ≤ δ / 3 := by
  have hK : (0 : ℚ) < paperScale m δ := by
    exact_mod_cast paperScale_positive hm hδ
  have hceil : 3 * (m : ℚ) / δ ≤ (paperScale m δ : ℚ) := Nat.le_ceil _
  have hprod := (div_le_iff₀ hδ).1 hceil
  apply (div_le_div_iff₀ hK (by norm_num : (0 : ℚ) < 3)).2
  nlinarith

theorem paperScale_lt (m : Nat) {δ : ℚ} (hδ : 0 < δ) :
    (paperScale m δ : ℚ) < 3 * (m : ℚ) / δ + 1 :=
  Nat.ceil_lt_add_one (by positivity)

theorem paperScale_le_linear (m : Nat) (δ : ℚ) :
    paperScale m δ ≤ ⌈(3 : ℚ) / δ⌉₊ * m := by
  unfold paperScale
  apply Nat.ceil_le.mpr
  calc
    3 * (m : ℚ) / δ = ((3 : ℚ) / δ) * m := by ring
    _ ≤ (⌈(3 : ℚ) / δ⌉₊ : ℚ) * m :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg m)
    _ = ((⌈(3 : ℚ) / δ⌉₊ * m : Nat) : ℚ) := by rw [Nat.cast_mul]

structure PositiveWeights (m : Nat) where
  weight : Fin m → ℚ
  positive : ∀ i, 0 < weight i
  total : ∑ i, weight i = 1

namespace PositiveWeights

variable {m : Nat} (w : PositiveWeights m)

include w in
theorem size_positive : 0 < m := by
  by_contra h
  have hm : m = 0 := by omega
  subst m
  have ht := w.total
  simp at ht

def floorCopies (K : Nat) (i : Fin m) : Nat := ⌊(K : ℚ) * w.weight i⌋₊

def floorTotal (K : Nat) : Nat := ∑ i, w.floorCopies K i

def remainder (K : Nat) : Nat := K - w.floorTotal K

def multiplicity (K : Nat) (i : Fin m) : Nat :=
  w.floorCopies K i + if i.val < w.remainder K then 1 else 0

theorem floorCopies_le_scaled (K : Nat) (i : Fin m) :
    (w.floorCopies K i : ℚ) ≤ (K : ℚ) * w.weight i :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (w.positive i).le)

theorem scaled_lt_floorCopies_add_one (K : Nat) (i : Fin m) :
    (K : ℚ) * w.weight i < (w.floorCopies K i : ℚ) + 1 :=
  Nat.lt_floor_add_one _

theorem floorTotal_le (K : Nat) : w.floorTotal K ≤ K := by
  have h : (w.floorTotal K : ℚ) ≤ K := by
    calc
      (w.floorTotal K : ℚ) = ∑ i, (w.floorCopies K i : ℚ) := by
        simp [floorTotal]
      _ ≤ ∑ i, (K : ℚ) * w.weight i :=
        Finset.sum_le_sum fun i _ => w.floorCopies_le_scaled K i
      _ = (K : ℚ) := by rw [← Finset.mul_sum, w.total, mul_one]
  exact_mod_cast h

theorem remainder_lt (K : Nat) : w.remainder K < m := by
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, w.size_positive⟩, Finset.mem_univ _⟩
  have hsum := Finset.sum_lt_sum_of_nonempty hnonempty
    (fun i _ => w.scaled_lt_floorCopies_add_one K i)
  have h : (K : ℚ) < (w.floorTotal K : ℚ) + m := by
    calc
      (K : ℚ) = ∑ i, (K : ℚ) * w.weight i := by
        rw [← Finset.mul_sum, w.total, mul_one]
      _ < ∑ i, ((w.floorCopies K i : ℚ) + 1) := hsum
      _ = (w.floorTotal K : ℚ) + m := by
        simp [floorTotal, Finset.sum_add_distrib]
  have hn : K < w.floorTotal K + m := by exact_mod_cast h
  have hfloor := w.floorTotal_le K
  unfold remainder
  omega

theorem sum_multiplicity (K : Nat) : ∑ i, w.multiplicity K i = K := by
  have hones : (∑ i : Fin m, if i.val < w.remainder K then (1 : Nat) else 0) =
      w.remainder K := by
    rw [Finset.sum_boole, Fin.card_filter_val_lt, Nat.min_eq_right (w.remainder_lt K).le]
    rfl
  simp only [multiplicity, Finset.sum_add_distrib, hones]
  change w.floorTotal K + w.remainder K = K
  have hfloor := w.floorTotal_le K
  unfold remainder
  omega

theorem multiplicity_error_scaled (K : Nat) (i : Fin m) :
    |(w.multiplicity K i : ℚ) - (K : ℚ) * w.weight i| ≤ 1 := by
  have hlo := w.floorCopies_le_scaled K i
  have hhi := w.scaled_lt_floorCopies_add_one K i
  apply abs_le.mpr
  by_cases h : i.val < w.remainder K
  · simp only [multiplicity, ite_eq_left h, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith
  · simp only [multiplicity, ite_eq_right h, Nat.add_zero]
    constructor <;> linarith

theorem multiplicity_error (K : Nat) (hK : 0 < K) (i : Fin m) :
    |(w.multiplicity K i : ℚ) / K - w.weight i| ≤ 1 / (K : ℚ) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  calc
    |(w.multiplicity K i : ℚ) / K - w.weight i| =
        |((w.multiplicity K i : ℚ) - (K : ℚ) * w.weight i) / K| := by
      congr 1
      field_simp [ne_of_gt hKq]
    _ = |(w.multiplicity K i : ℚ) - (K : ℚ) * w.weight i| / K := by
      rw [abs_div, abs_of_pos hKq]
    _ ≤ 1 / (K : ℚ) :=
      div_le_div_of_nonneg_right (w.multiplicity_error_scaled K i) hKq.le

theorem sum_rounded_weights (K : Nat) (hK : 0 < K) :
    (∑ i, (w.multiplicity K i : ℚ) / K) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, w.sum_multiplicity]
  exact div_self (Nat.cast_ne_zero.mpr (ne_of_gt hK))

theorem l1_error (K : Nat) (hK : 0 < K) :
    (∑ i, |(w.multiplicity K i : ℚ) / K - w.weight i|) ≤ (m : ℚ) / K := by
  calc
    _ ≤ ∑ _i : Fin m, (1 : ℚ) / K :=
      Finset.sum_le_sum fun i _ => w.multiplicity_error K hK i
    _ = (m : ℚ) / K := by simp [div_eq_mul_inv]

def copies (K : Nat) : List (Fin m) :=
  (List.ofFn fun i => List.replicate (w.multiplicity K i) i).flatten

theorem copies_length (K : Nat) : (w.copies K).length = K := by
  simpa [copies, List.map_ofFn, List.sum_ofFn] using w.sum_multiplicity K

theorem copies_nonempty (K : Nat) (hK : 0 < K) : w.copies K ≠ [] := by
  intro h
  have hlen := w.copies_length K
  rw [h] at hlen
  simp at hlen
  omega

theorem copies_positive_support (K : Nat) (i : Fin m) (_hi : i ∈ w.copies K) :
    0 < w.weight i := w.positive i

theorem copies_filter_length (K : Nat) (keep : Fin m → Bool) :
    ((w.copies K).filter keep).length =
      ∑ i, if keep i then w.multiplicity K i else 0 := by
  simp only [copies, List.filter_flatten, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : keep i <;> simp [h]

def weightedAcceptance (keep : Fin m → Bool) : ℚ :=
  ∑ i, if keep i then w.weight i else 0

def unweightedAcceptance (K : Nat) (keep : Fin m → Bool) : ℚ :=
  (((w.copies K).filter keep).length : ℚ) / (w.copies K).length

theorem unweightedAcceptance_eq (K : Nat) (keep : Fin m → Bool) :
    w.unweightedAcceptance K keep =
      ∑ i, if keep i then (w.multiplicity K i : ℚ) / K else 0 := by
  rw [unweightedAcceptance, w.copies_length, w.copies_filter_length]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases keep i <;> simp

theorem acceptance_error (K : Nat) (hK : 0 < K) (keep : Fin m → Bool) :
    |w.unweightedAcceptance K keep - w.weightedAcceptance keep| ≤ (m : ℚ) / K := by
  rw [w.unweightedAcceptance_eq, weightedAcceptance, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(if keep i then (w.multiplicity K i : ℚ) / K else 0) -
        (if keep i then w.weight i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(w.multiplicity K i : ℚ) / K - w.weight i| := by
      apply Finset.sum_le_sum
      intro i _
      cases keep i <;> simp
    _ ≤ (m : ℚ) / K := w.l1_error K hK

theorem perfectCompleteness_preserved (K : Nat) (hK : 0 < K)
    (keep : Fin m → Bool) (hkeep : ∀ i, keep i = true) :
    w.unweightedAcceptance K keep = 1 := by
  rw [w.unweightedAcceptance_eq]
  simpa only [hkeep, ite_true] using w.sum_rounded_weights K hK

def output {α : Type*} (K : Nat) (entries : Fin m → α) : List α :=
  (w.copies K).map entries

theorem output_length {α : Type*} (K : Nat) (entries : Fin m → α) :
    (w.output K entries).length = K := by
  simp [output, w.copies_length]

theorem output_nonempty {α : Type*} (K : Nat) (hK : 0 < K)
    (entries : Fin m → α) : w.output K entries ≠ [] := by
  intro h
  change (w.copies K).map entries = [] at h
  exact w.copies_nonempty K hK (List.map_eq_nil_iff.mp h)

theorem output_support {α : Type*} (K : Nat) (entries : Fin m → α)
    (e : α) (he : e ∈ w.output K entries) :
    ∃ i : Fin m, entries i = e ∧ 0 < w.weight i := by
  obtain ⟨i, _, hi⟩ := List.mem_map.mp he
  exact ⟨i, hi, w.positive i⟩

theorem output_acceptance_error {α : Type*} (K : Nat) (hK : 0 < K)
    (entries : Fin m → α) (accepts : α → Bool) :
    |(((w.output K entries).filter accepts).length : ℚ) / (w.output K entries).length -
      (∑ i, if accepts (entries i) then w.weight i else 0)| ≤ (m : ℚ) / K := by
  simpa only [unweightedAcceptance, weightedAcceptance, output, List.filter_map,
    List.length_map, Function.comp_def] using
    w.acceptance_error K hK (fun i => accepts (entries i))

def paperOutput {α : Type*} (δ : ℚ) (entries : Fin m → α) : List α :=
  w.output (paperScale m δ) entries

theorem paperOutput_length {α : Type*} (δ : ℚ) (entries : Fin m → α) :
    (w.paperOutput δ entries).length = paperScale m δ :=
  w.output_length _ entries

theorem paperOutput_nonempty {α : Type*} {δ : ℚ} (hδ : 0 < δ)
    (entries : Fin m → α) : w.paperOutput δ entries ≠ [] :=
  w.output_nonempty _ (paperScale_positive w.size_positive hδ) entries

theorem paperOutput_length_lt {α : Type*} {δ : ℚ} (hδ : 0 < δ)
    (entries : Fin m → α) :
    ((w.paperOutput δ entries).length : ℚ) < 3 * (m : ℚ) / δ + 1 := by
  rw [w.paperOutput_length]
  exact paperScale_lt m hδ

theorem paperOutput_length_le_linear {α : Type*} (δ : ℚ)
    (entries : Fin m → α) :
    (w.paperOutput δ entries).length ≤ ⌈(3 : ℚ) / δ⌉₊ * m := by
  rw [w.paperOutput_length]
  exact paperScale_le_linear m δ

theorem paperOutput_acceptance_error {α : Type*} {δ : ℚ} (hδ : 0 < δ)
    (entries : Fin m → α) (accepts : α → Bool) :
    |(((w.paperOutput δ entries).filter accepts).length : ℚ) /
        (w.paperOutput δ entries).length -
      (∑ i, if accepts (entries i) then w.weight i else 0)| ≤ δ / 3 :=
  (w.output_acceptance_error _ (paperScale_positive w.size_positive hδ) entries accepts).trans
    (paperScale_error w.size_positive hδ)

theorem paperOutput_perfectCompleteness {α : Type*} {δ : ℚ} (hδ : 0 < δ)
    (entries : Fin m → α) (accepts : α → Bool)
    (haccepts : ∀ i, accepts (entries i) = true) :
    (((w.paperOutput δ entries).filter accepts).length : ℚ) /
      (w.paperOutput δ entries).length = 1 := by
  simpa only [paperOutput, output, List.filter_map, List.length_map, Function.comp_def,
    unweightedAcceptance] using
    w.perfectCompleteness_preserved _ (paperScale_positive w.size_positive hδ)
      (fun i => accepts (entries i)) haccepts

end PositiveWeights
end PerfectCompleteness.WeightRounding



namespace PerfectCompleteness.RoundedTarget

open scoped BigOperators
open WeightRounding
open UniqueGamesTheorem.Foundations.Games

variable {m l r q : Nat}

abbrev EndpointLabeling (l r q : Nat) :=
  (Fin l → Fin (2 * q)) × (Fin r → Fin q)

def construct (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) : Instance q where
  leftVertices := l
  rightVertices := r
  edges := w.output K entries
  nonempty := w.output_nonempty K hK entries

theorem edge_length (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) : (construct w entries K hK).edges.length = K :=
  w.output_length K entries

theorem edge_support (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (e : Edge l r q)
    (he : e ∈ (construct w entries K hK).edges) :
    ∃ i : Fin m, entries i = e ∧ 0 < w.weight i :=
  w.output_support K entries e he

theorem countSatisfied_eq_filter (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q)
    (es : List (Edge l r q)) :
    countSatisfied a b es = (es.filter fun e => e.satisfied a b).length := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    cases h : e.satisfied a b <;> simp [countSatisfied, h, ih, Nat.add_comm]

theorem count_eq (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    countSatisfied a b (construct w entries K hK).edges =
      ∑ i, if (entries i).satisfied a b then w.multiplicity K i else 0 := by
  change countSatisfied a b (w.output K entries) = _
  rw [countSatisfied_eq_filter]
  simpa only [PositiveWeights.output, List.filter_map, List.length_map,
    Function.comp_def] using w.copies_filter_length K (fun i => (entries i).satisfied a b)

def weightedSuccess (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) : ℚ :=
  w.weightedAcceptance fun i => (entries i).satisfied a b

theorem rate_eq (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    (countSatisfied a b (construct w entries K hK).edges : ℚ) /
        (construct w entries K hK).edges.length =
      w.unweightedAcceptance K (fun i => (entries i).satisfied a b) := by
  change (countSatisfied a b (w.output K entries) : ℚ) / (w.output K entries).length = _
  rw [countSatisfied_eq_filter]
  simp only [PositiveWeights.output, PositiveWeights.unweightedAcceptance,
    List.filter_map, List.length_map, Function.comp_def]

theorem rate_error (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    |(countSatisfied a b (construct w entries K hK).edges : ℚ) /
        (construct w entries K hK).edges.length - weightedSuccess w entries a b| ≤
      (m : ℚ) / K := by
  rw [rate_eq]
  exact w.acceptance_error K hK (fun i => (entries i).satisfied a b)

theorem real_rate_error (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    |(countSatisfied a b (construct w entries K hK).edges : ℝ) /
        (construct w entries K hK).edges.length - (weightedSuccess w entries a b : ℝ)| ≤
      (m : ℝ) / K := by
  have h := rate_error w entries K hK a b
  change |(countSatisfied a b (w.output K entries) : ℚ) /
      (w.output K entries).length - weightedSuccess w entries a b| ≤ (m : ℚ) / K at h
  change |(countSatisfied a b (w.output K entries) : ℝ) /
      (w.output K entries).length - (weightedSuccess w entries a b : ℝ)| ≤ (m : ℝ) / K
  have hc := (Rat.cast_le (K := ℝ)).2 h
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hc

noncomputable def weightedGame (w : PositiveWeights m) (entries : Fin m → Edge l r q) :
    OccurrenceGame (Fin m) (Fin l) (Fin r) (Fin (2 * q)) (Fin q) where
  occurrences :=
    { weight := fun i => (w.weight i : ℝ)
      nonnegative := fun i => by exact_mod_cast (w.positive i).le
      normalized := by exact_mod_cast w.total }
  left := fun i => (entries i).left
  right := fun i => (entries i).right
  accepts := fun i a b => decide ((entries i).projection.images[a] = b)

theorem weightedGame_success (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (s : EndpointLabeling l r q) :
    (weightedGame w entries).success s = (weightedSuccess w entries s.1 s.2 : ℝ) := by
  change (∑ i, if (entries i).satisfied s.1 s.2 then (w.weight i : ℝ) else 0) =
    ((∑ i, if (entries i).satisfied s.1 s.2 then w.weight i else 0 : ℚ) : ℝ)
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : (entries i).satisfied s.1 s.2 <;> simp

noncomputable def weightedValue (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (hq : 0 < q) : ℝ := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  letI : Nonempty (Fin (2 * q)) := ⟨⟨0, by omega⟩⟩
  exact (weightedGame w entries).value

theorem weightedSuccess_le_value (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (hq : 0 < q) (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    (weightedSuccess w entries a b : ℝ) ≤ weightedValue w entries hq := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin (2 * q)) := ⟨⟨0, by omega⟩⟩
  rw [← weightedGame_success w entries (a, b)]
  exact (weightedGame w entries).success_le_value (a, b)

theorem weightedValue_attained (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (hq : 0 < q) :
    ∃ s : EndpointLabeling l r q,
      (weightedSuccess w entries s.1 s.2 : ℝ) = weightedValue w entries hq := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin (2 * q)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s, hs⟩ := (weightedGame w entries).exists_optimal_strategy
  rw [weightedGame_success] at hs
  exact ⟨s, hs⟩

theorem completeness_preserved (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K)
    (hcomplete : ∃ s : EndpointLabeling l r q,
      ∀ i, (entries i).satisfied s.1 s.2 = true) :
    PerfectlyComplete (construct w entries K hK) := by
  obtain ⟨s, hs⟩ := hcomplete
  refine ⟨s, ?_⟩
  intro e he
  obtain ⟨i, hi, _⟩ := edge_support w entries K hK e he
  rw [← hi]
  exact hs i

theorem complete_value_eq_one (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (hq : 0 < q)
    (hcomplete : ∃ s : EndpointLabeling l r q,
      ∀ i, (entries i).satisfied s.1 s.2 = true) :
    (construct w entries K hK).value = 1 :=
  ((construct w entries K hK).perfectlyComplete_iff_value_eq_one hq).1
    (completeness_preserved w entries K hK hcomplete)

theorem value_le (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (hq : 0 < q) (bound : ℝ)
    (hsound : ∀ a : Fin l → Fin (2 * q), ∀ b : Fin r → Fin q,
      (weightedSuccess w entries a b : ℝ) ≤ bound) :
    (construct w entries K hK).value ≤ bound + (m : ℝ) / K := by
  obtain ⟨s, hs⟩ := (construct w entries K hK).maxSatisfied_attained hq
  have he := (abs_le.mp (real_rate_error w entries K hK s.1 s.2)).2
  have hw := hsound s.1 s.2
  unfold Instance.value
  rw [← hs]
  change (countSatisfied s.1 s.2 (w.output K entries) : ℝ) /
    (w.output K entries).length ≤ bound + (m : ℝ) / K
  change (countSatisfied s.1 s.2 (w.output K entries) : ℝ) /
    (w.output K entries).length - (weightedSuccess w entries s.1 s.2 : ℝ) ≤
      (m : ℝ) / K at he
  calc
    _ = ((countSatisfied s.1 s.2 (w.output K entries) : ℝ) /
        (w.output K entries).length - (weightedSuccess w entries s.1 s.2 : ℝ)) +
        (weightedSuccess w entries s.1 s.2 : ℝ) := by ring
    _ ≤ (m : ℝ) / K + bound := add_le_add he hw
    _ = bound + (m : ℝ) / K := add_comm _ _

theorem value_distance (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (hq : 0 < q) :
    |(construct w entries K hK).value - weightedValue w entries hq| ≤ (m : ℝ) / K := by
  have hu := value_le w entries K hK hq (weightedValue w entries hq)
    (weightedSuccess_le_value w entries hq)
  obtain ⟨s, hs⟩ := weightedValue_attained w entries hq
  have he := (abs_le.mp (real_rate_error w entries K hK s.1 s.2)).1
  rw [hs] at he
  have hl := (construct w entries K hK).rate_le_value s
  change -((m : ℝ) / K) ≤ (countSatisfied s.1 s.2 (w.output K entries) : ℝ) /
    (w.output K entries).length - weightedValue w entries hq at he
  change (countSatisfied s.1 s.2 (w.output K entries) : ℝ) /
    (w.output K entries).length ≤ (construct w entries K hK).value at hl
  apply abs_le.mpr
  constructor
  · exact he.trans (sub_le_sub hl (le_refl (weightedValue w entries hq)))
  · calc
      _ ≤ (weightedValue w entries hq + (m : ℝ) / K) - weightedValue w entries hq :=
        sub_le_sub hu (le_refl (weightedValue w entries hq))
      _ = (m : ℝ) / K := by ring

theorem soundAt_of_weighted_bound (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (K : Nat) (hK : 0 < K) (hq : 0 < q) (d : RationalThreshold) (bound : ℝ)
    (hsound : ∀ a : Fin l → Fin (2 * q), ∀ b : Fin r → Fin q,
      (weightedSuccess w entries a b : ℝ) ≤ bound)
    (hbudget : bound + (m : ℝ) / K ≤ (d.numerator : ℝ) / d.denominator) :
    SoundAt d (construct w entries K hK) :=
  ((construct w entries K hK).soundAt_iff_value_le hq d).2
    ((value_le w entries K hK hq bound hsound).trans hbudget)

def paper (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) : Instance q :=
  construct w entries (paperScale m δ) (paperScale_positive w.size_positive hδ)

theorem paper_edge_length (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) : (paper w entries δ hδ).edges.length = paperScale m δ :=
  edge_length w entries _ _

theorem paper_edge_length_le_linear (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) :
    (paper w entries δ hδ).edges.length ≤ ⌈(3 : ℚ) / δ⌉₊ * m := by
  rw [paper_edge_length]
  exact paperScale_le_linear m δ

theorem paper_value_distance (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) :
    |(paper w entries δ hδ).value - weightedValue w entries hq| ≤ (δ : ℝ) / 3 := by
  have hbudget : (m : ℝ) / paperScale m δ ≤ (δ : ℝ) / 3 := by
    have h := (Rat.cast_le (K := ℝ)).2 (paperScale_error w.size_positive hδ)
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h
  exact (value_distance w entries _ (paperScale_positive w.size_positive hδ) hq).trans hbudget

theorem paper_value_le (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (bound : ℝ)
    (hsound : ∀ a : Fin l → Fin (2 * q), ∀ b : Fin r → Fin q,
      (weightedSuccess w entries a b : ℝ) ≤ bound) :
    (paper w entries δ hδ).value ≤ bound + (δ : ℝ) / 3 := by
  have hbudget : (m : ℝ) / paperScale m δ ≤ (δ : ℝ) / 3 := by
    have h := (Rat.cast_le (K := ℝ)).2 (paperScale_error w.size_positive hδ)
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using h
  exact (value_le w entries _ (paperScale_positive w.size_positive hδ) hq bound hsound).trans
    (add_le_add (le_refl bound) hbudget)

theorem paper_soundAt_of_weighted_bound (w : PositiveWeights m)
    (entries : Fin m → Edge l r q) (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q)
    (d : RationalThreshold) (bound : ℝ)
    (hsound : ∀ a : Fin l → Fin (2 * q), ∀ b : Fin r → Fin q,
      (weightedSuccess w entries a b : ℝ) ≤ bound)
    (hbudget : bound + (δ : ℝ) / 3 ≤ (d.numerator : ℝ) / d.denominator) :
    SoundAt d (paper w entries δ hδ) :=
  ((paper w entries δ hδ).soundAt_iff_value_le hq d).2
    ((paper_value_le w entries δ hδ hq bound hsound).trans hbudget)

theorem paper_complete_value_eq_one (w : PositiveWeights m) (entries : Fin m → Edge l r q)
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q)
    (hcomplete : ∃ s : EndpointLabeling l r q,
      ∀ i, (entries i).satisfied s.1 s.2 = true) :
    (paper w entries δ hδ).value = 1 :=
  complete_value_eq_one w entries _ (paperScale_positive w.size_positive hδ) hq hcomplete

end PerfectCompleteness.RoundedTarget

end OAI
