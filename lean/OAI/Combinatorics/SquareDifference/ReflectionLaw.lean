import OAI.Combinatorics.SquareDifference.TupleReflection

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma expect_two_halves {I L K V A J : Type*} [Fintype I] [Fintype L] [Fintype K]
    [Fintype V] [Fintype A] [Fintype J] [DecidableEq I] [DecidableEq L]
    [DecidableEq K] [DecidableEq V]
    (e : I ⊕ I ≃ K) (f : L ⊕ L ≃ V) (G : (K → A) → (V → J) → ℝ) :
    (𝔼 Y : K → A, 𝔼 j : V → J, G Y j) =
      𝔼 x : I → A, 𝔼 y : I → A, 𝔼 j : L → J, 𝔼 k : L → J,
        G ((Sum.elim x y) ∘ e.symm) ((Sum.elim j k) ∘ f.symm) := by
  rw [expect_precompose e.symm, expect_sum_function]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  rw [expect_precompose f.symm, expect_sum_function]

lemma tupleValidity_half {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (x y : TupleHalfEntry S b hb α β → ZMod p) :
    tupleValidity S ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm) =
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
      listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
        (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y := by
  let e := tupleEntryHalfEquiv S b hb hne
  have hh := graphValidity_pullback e (tupleListEdges S) ((Sum.elim x y) ∘ e.symm)
  have he : ((Sum.elim x y) ∘ e.symm) ∘ e = Sum.elim x y := by
    funext z
    exact congrArg (Sum.elim x y) (e.symm_apply_apply z)
  rw [he] at hh
  change graphValidity (tupleUnmarkedGraph S b hb hne) (Sum.elim x y) = _ at hh
  change graphValidity (tupleListEdges S) _ = _
  rw [← hh]
  exact graphValidity_cut _ (tupleUnmarkedGraph_noopp S b hb hne)
    (tupleUnmarkedGraph_reflect S b hb hne) x y

lemma tupleWeight_half (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (j k : CutHalf b α β → TupleListIndex S) :
    tupleWeight S ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) =
      tupleHalfWeight S b α β j * tupleHalfWeight S b α β k := by
  have hh := indexWeight_equiv (halfSumEquiv b hne) (interaction S tupleDelta)
    ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm)
  have he : ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) ∘ (halfSumEquiv b hne) =
      Sum.elim j k := by
    funext z
    exact congrArg (Sum.elim j k) ((halfSumEquiv b hne).symm_apply_apply z)
  rw [he, unmarked_weight_factor S tupleDelta b hb hne] at hh
  exact hh.symm

lemma tupleCutForm_unmarked_factor {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleCutForm S b α β F =
      𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 y : TupleHalfEntry S b hb α β → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
      𝔼 k : CutHalf b α β → TupleListIndex S,
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
        graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) y *
        listKernel (cutCrossEdges (tupleUnmarkedGraph S b hb hne))
          (cutCrossDirection (tupleUnmarkedGraph S b hb hne)) x y *
        (tupleHalfWeight S b α β j * tupleHalfWeight S b α β k) *
        F (fun v => x (tupleHalfProjection S b hb α β v, j v)) *
        F (fun v => y (tupleHalfProjection S b hb α β v, k v)) := by
  classical
  unfold tupleCutForm tupleComponent
  rw [expect_two_halves (tupleEntryHalfEquiv S b hb hne) (halfSumEquiv b hne)]
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  rw [tupleValidity_half S b hb hne, tupleWeight_half S b hb hne]
  have hh := tupleOutput_half S b hb hne x y j k
  have hl : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) v.1) =
      fun v => x (tupleHalfProjection S b hb α β v, j v) := by
    funext v
    exact congrFun hh (Sum.inl v)
  have hr : (fun v : CutHalf b α β => tupleOutput S
      ((Sum.elim x y) ∘ (tupleEntryHalfEquiv S b hb hne).symm)
      ((Sum.elim j k) ∘ (halfSumEquiv b hne).symm) (reflect b α β v.1)) =
      fun v => y (tupleHalfProjection S b hb α β v, k v) := by
    funext v
    exact congrFun hh (Sum.inr v)
  dsimp only
  rw [hl, hr]
  ring

lemma weighted_average_sq_le {J : Type*} [Fintype J] [Nonempty J]
    (W f : J → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B) :
    (𝔼 j : J, W j * f j)^2 ≤ B^2 * (𝔼 j : J, (f j)^2) := by
  have hc := expect_mul_sq_le_sq_mul_sq univ W f
  have hw : (𝔼 j : J, (W j)^2) ≤ B^2 :=
    expect_le univ_nonempty (fun j _ => pow_le_pow_left₀ (hW j).1 (hW j).2 _)
  exact hc.trans (mul_le_mul_of_nonneg_right hw (expect_nonneg fun _ _ => sq_nonneg _))

lemma list_factorized_quadratic {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (W : (L → J) → ℝ)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    (𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
      K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k) =
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p,
        (K x * (𝔼 j : L → J, W j * f x j)) * listKernel E dir x y *
          (K y * (𝔼 k : L → J, W k * f y k)) := by
  apply expect_congr rfl
  intro x _
  apply expect_congr rfl
  intro y _
  conv_lhs => arg 2; ext j; arg 2; ext k; rw [show
    K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k =
      (K x * listKernel E dir x y * K y) * ((W j * f x j) * (W k * f y k)) by ring]
  simp only [← mul_expect, ← expect_mul]
  ring

lemma list_factorized_lower {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq L] [Nonempty J] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × I)) (dir : I → I → Bool)
    (K : (I → ZMod p) → ℝ) (hK : ∀ x, 0 ≤ K x ∧ (K x)^2 = K x)
    (W : (L → J) → ℝ) {B : ℝ} (hW : ∀ j, 0 ≤ W j ∧ W j ≤ B)
    (f : (I → ZMod p) → (L → J) → ℝ) :
    -(32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) * B^2 *
      (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) ≤
      𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, 𝔼 j : L → J, 𝔼 k : L → J,
        K x * K y * listKernel E dir x y * (W j * W k) * f x j * f y k := by
  rw [list_factorized_quadratic]
  let G (x : I → ZMod p) := K x * (𝔼 j : L → J, W j * f x j)
  have h := list_quadratic_lower hp E dir G
  have hg : (𝔼 x : I → ZMod p, (G x)^2) ≤
      B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2) := by
    rw [mul_expect]
    apply expect_le_expect
    intro x _
    dsimp [G]
    rw [mul_pow, (hK x).2, ← mul_expect]
    calc
      _ ≤ K x * (B^2 * (𝔼 j : L → J, (f x j)^2)) :=
        mul_le_mul_of_nonneg_left (weighted_average_sq_le W (f x) hW) (hK x).1
      _ = _ := by ring
  have hc : 0 ≤ (32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8) := by positivity
  have hm := mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr hc)
  change _ ≤ 𝔼 x : I → ZMod p, 𝔼 y : I → ZMod p, G x * listKernel E dir x y * G y
  calc
    _ = -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (B^2 * (𝔼 x : I → ZMod p, 𝔼 j : L → J, K x * (f x j)^2)) := by ring
    _ ≤ -((32 * E.card : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ) / 8)) *
      (𝔼 x : I → ZMod p, (G x)^2) := hm
    _ ≤ _ := by simpa only [neg_mul] using h

noncomputable def tupleUnmarkedMoment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
  𝔼 j : CutHalf b α β → TupleListIndex S,
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      (F (fun v => x (tupleHalfProjection S b hb α β v, j v))) ^ 2

lemma tupleUnmarkedMoment_nonneg {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleUnmarkedMoment S b hb hne F :=
  expect_nonneg fun _ _ => expect_nonneg fun _ _ =>
    mul_nonneg (graphValidity_nonneg _ _) (sq_nonneg _)

lemma tuple_unmarked_error_exact {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -(32 * (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ^ ((1 : ℝ) / 4) *
      (p : ℝ) ^ (-(1 : ℝ) / 8) * tupleWeightBound ^ 2 *
        tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  rw [tupleCutForm_unmarked_factor S b hb hne]
  exact list_factorized_lower hp _ _ _ (fun x =>
    ⟨graphValidity_nonneg _ x, graphValidity_sq _ x⟩)
    (tupleHalfWeight S b α β) (fun j =>
      ⟨(tupleHalfWeight_one_le S b α β j).trans' (by norm_num),
        tupleHalfWeight_le S hS b hb hne j⟩) _

lemma card_tupleHalfEntry_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype.card (TupleHalfEntry S b hb α β) ≤ Fintype.card TupleVertex := by
  classical
  have hsub : Fintype.card (TupleHalfAddress S b hb α β) ≤
      (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
    rw [← card_tupleAddress S]
    exact Fintype.card_subtype_le _
  have hS : S.card ≤ tupleBlocks := by
    simpa using (card_le_card (subset_univ S))
  have hr : tupleR ≤ Nat.factorial tupleH := Nat.div_le_self _ _
  rw [card_tupleVertex]
  rw [show Fintype.card (TupleHalfEntry S b hb α β) =
      Fintype.card (TupleHalfAddress S b hb α β) * (tupleR ^ S.card) by
        simp only [TupleHalfEntry, Fintype.card_prod, TupleListIndex, Fintype.card_fin]]
  calc
    _ ≤ (Nat.factorial tupleH) ^ (tupleBlocks - S.card) *
        (Nat.factorial tupleH) ^ S.card := Nat.mul_le_mul hsub (Nat.pow_le_pow_left hr _)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hS]

lemma card_relation_le_sq {I : Type*} [Fintype I] (E : Finset (I × I))
    {d : ℕ} (hd : Fintype.card I ≤ d) : E.card ≤ d^2 := by
  calc
    _ ≤ Fintype.card (I × I) := card_le_univ _
    _ = (Fintype.card I)^2 := by rw [Fintype.card_prod, sq]
    _ ≤ _ := Nat.pow_le_pow_left hd _

lemma card_tupleCrossEdges_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card ≤ (Fintype.card TupleVertex)^2 :=
  card_relation_le_sq _ (card_tupleHalfEntry_le S b hb α β)

noncomputable def tupleUnmarkedConstant : ℝ :=
  (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1 : ℝ) / 4) * tupleWeightBound^2

lemma tuple_unmarked_error {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    -tupleUnmarkedConstant * (p : ℝ)^(-(1 : ℝ)/8) *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm S b α β F := by
  have hc : (32 * ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ)) ^ ((1:ℝ)/4) ≤
      (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1:ℝ)/4) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have ht : ((cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card : ℝ) ≤
        (Fintype.card TupleVertex : ℝ)^2 := by
      exact_mod_cast card_tupleCrossEdges_le S b hb hne
    linarith
  have hm : 0 ≤ (p : ℝ)^(-(1:ℝ)/8) * tupleWeightBound^2 *
      tupleUnmarkedMoment S b hb hne F :=
    mul_nonneg (by positivity) (tupleUnmarkedMoment_nonneg S b hb hne F)
  have ht := mul_le_mul_of_nonneg_right hc hm
  have he := tuple_unmarked_error_exact hp S hS b hb hne F
  dsimp [tupleUnmarkedConstant]
  nlinarith

lemma tupleUnmarkedGraph_terminal (S : Finset (Fin tupleBlocks))
    (hs : S.card = tupleT + 1) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) :
    tupleUnmarkedGraph S b hb hne = ∅ := by
  have ht : ¬ S.card ≤ tupleT := by omega
  simp [tupleUnmarkedGraph, graphPullback, tupleListEdges, ht]

lemma tuple_terminal_positive {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (S : Finset (Fin tupleBlocks)) (hs : S.card = tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F := by
  have h := tuple_unmarked_error_exact hp S (by omega) b hb hne F
  simpa only [tupleUnmarkedGraph_terminal S hs b hb hne, cutCrossEdges,
    notMem_empty, or_self, filter_false, card_empty, Nat.cast_zero, mul_zero,
    Real.zero_rpow (by norm_num : (1 : ℝ)/4 ≠ 0), neg_zero, zero_mul] using h

abbrev TupleCutWord (α β : Fin tupleH) :=
  {w : Equiv.Perm (Fin tupleH) // w.symm α < w.symm β}

noncomputable def orderedPermEquiv {h : ℕ} (α β : Fin h) :
    {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} ≃ (CutHalf () α β : Type) where
  toFun w := ⟨fun _ => w.1, w.2⟩
  invFun w := ⟨w.1 (), w.2⟩
  left_inv _ := rfl
  right_inv w := by ext u; cases u; rfl

lemma card_orderedPerm {h : ℕ} {α β : Fin h} (hne : α ≠ β) :
    Fintype.card {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} = Nat.factorial h / 2 := by
  have hh := card_cutHalf () hne
  rw [← Fintype.card_congr (orderedPermEquiv α β), Fintype.card_unit, pow_one] at hh
  omega

lemma card_tupleCutWord {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (TupleCutWord α β) = tupleR :=
  card_orderedPerm hne

def tupleMarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (a : TupleAddress S) : TupleAddress (insert b S) :=
  fun c => a ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩

def tupleUnmarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) : TupleAddress S :=
  fun c => if hc : c.1 = b then w else u ⟨c.1, by simp [hc, c.2]⟩

lemma tupleUnmarkAddress_at (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleUnmarkAddress S b u w ⟨b, hb⟩ = w := by
  simp [tupleUnmarkAddress]

lemma tupleMark_unmark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleMarkAddress S b (tupleUnmarkAddress S b u w) = u := by
  funext c
  have hb : c.1 ≠ b := by intro h; exact c.2 (by simp [h])
  simp [tupleMarkAddress, tupleUnmarkAddress, hb]

lemma tupleUnmark_mark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (a : TupleAddress S) :
    tupleUnmarkAddress S b (tupleMarkAddress S b a) (a ⟨b,hb⟩) = a := by
  funext c
  by_cases hc : c.1 = b
  · have he : c = ⟨b,hb⟩ := Subtype.ext hc
    subst c
    simp [tupleUnmarkAddress]
  · simp [tupleUnmarkAddress, tupleMarkAddress, hc]

noncomputable def tupleHalfAddressEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    TupleHalfAddress S b hb α β ≃ TupleAddress (insert b S) × TupleCutWord α β where
  toFun a := (tupleMarkAddress S b a.1, ⟨a.1 ⟨b,hb⟩, a.2⟩)
  invFun a := ⟨tupleUnmarkAddress S b a.1 a.2.1, by
    change (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm α <
      (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm β
    rw [tupleUnmarkAddress_at]
    exact a.2.2⟩
  left_inv a := Subtype.ext (tupleUnmark_mark S b hb a.1)
  right_inv a := by
    apply Prod.ext
    · exact tupleMark_unmark S b a.1 a.2.1
    · apply Subtype.ext
      exact tupleUnmarkAddress_at S b hb a.1 a.2.1

noncomputable def tupleMarkIndexEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleListIndex (insert b S) ≃ TupleCutWord α β × TupleListIndex S :=
  Fintype.equivOfCardEq (by
    simp only [TupleListIndex, Fintype.card_fin, Fintype.card_prod,
      card_tupleCutWord hne, card_insert_of_notMem hb, pow_succ, mul_comm])

noncomputable def tupleRegroupEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ≃ TupleListEntry (insert b S) :=
  ((Equiv.prodCongr (tupleHalfAddressEquiv S b hb α β) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans
      (Equiv.prodCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne).symm)

lemma expect_ge_single {I : Type*} [Fintype I] (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (i : I) :
    (Fintype.card I : ℝ)⁻¹ * f i ≤ 𝔼 j : I, f j := by
  rw [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [mul_comm ((Fintype.card I : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_right (single_le_sum (fun j _ => hf j) (mem_univ i))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma expect_prod_function {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) :
    (𝔼 j : V → W × I, f j) =
      𝔼 w : V → W, 𝔼 i : V → I, f (fun v => (w v, i v)) := by
  calc
    _ = 𝔼 j : (V → W) × (V → I), f (fun v => (j.1 v,j.2 v)) :=
      Fintype.expect_equiv (Equiv.arrowProdEquivProdArrow V (fun _ => W) (fun _ => I))
        _ _ (fun _ => rfl)
    _ = _ := by rw [← univ_product_univ, expect_product]

lemma expect_restrict_first {V W I : Type*} [Fintype V] [Fintype W] [Fintype I]
    [DecidableEq V] (f : (V → W × I) → ℝ) (hf : ∀ j, 0 ≤ f j) (w : V → W) :
    ((Fintype.card W : ℝ) ^ Fintype.card V)⁻¹ *
      (𝔼 i : V → I, f (fun v => (w v, i v))) ≤ 𝔼 j : V → W × I, f j := by
  rw [expect_prod_function]
  simpa only [Fintype.card_fun, Nat.cast_pow] using
    expect_ge_single (fun w : V → W => 𝔼 i : V → I, f (fun v => (w v,i v)))
      (fun w => expect_nonneg fun i _ => hf _) w

lemma tupleRegroup_fst (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    (tupleRegroupEquiv S b hb hne a).1 = tupleMarkAddress S b a.1.1 := rfl

lemma tupleRegroup_snd (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (a : TupleHalfEntry S b hb α β) :
    (tupleMarkIndexEquiv S b hb hne) (tupleRegroupEquiv S b hb hne a).2 =
      (⟨a.1.1 ⟨b,hb⟩, a.1.2⟩, a.2) := by
  exact (tupleMarkIndexEquiv S b hb hne).apply_symm_apply _

def tupleWordOfHalf (b : Fin tupleBlocks) (α β : Fin tupleH) (v : CutHalf b α β) :
    TupleCutWord α β := ⟨v.1 b, v.2⟩

lemma tupleRegroup_projection (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (v : CutHalf b α β) (i : TupleListIndex S) :
    tupleRegroupEquiv S b hb hne (tupleHalfProjection S b hb α β v, i) =
      (tupleProjection (insert b S) v.1,
        (tupleMarkIndexEquiv S b hb hne).symm (tupleWordOfHalf b α β v, i)) := by
  apply Prod.ext
  · rfl
  · rfl

lemma tuple_regroup_edges (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    graphPullback (tupleRegroupEquiv S b hb hne) (tupleListEdges (insert b S)) ⊆
      cutInternalEdges (tupleUnmarkedGraph S b hb hne) := by
  intro a ha
  simp only [graphPullback, mem_filter, mem_univ, true_and] at ha
  simp only [cutInternalEdges, mem_filter, mem_univ, true_and, tupleUnmarkedGraph,
    graphPullback, tupleEntryHalfEquiv_inl, tupleListEdges, ite_eq_left hs]
  unfold tupleListEdges at ha
  split_ifs at ha with hnew
  · have h := (mem_filter.mp ha).2
    let f : {c : Fin tupleBlocks // c ∉ insert b S} ↪
        {c : Fin tupleBlocks // c ∉ S} :=
      ⟨fun c => ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩,
        fun c d he => Subtype.ext (congrArg (fun x : {c : Fin tupleBlocks // c ∉ S} => x.val) he)⟩
    exact addressEdge_mono_blocks tupleCycle (tupleT + 1) f a.1.1.1 a.2.1.1 h
  · simp at ha

lemma graphValidity_antitone {I : Type*} {p : ℕ} [Fact p.Prime]
    {E E' : Finset (I × I)} (hE : E' ⊆ E) (z : I → ZMod p) :
    graphValidity E z ≤ graphValidity E' z :=
  prod_le_prod_of_subset_of_le_one₀ hE (fun _ _ => squareIndicator_nonneg _)
    (fun _ _ _ => squareIndicator_le_one _)

lemma tuple_regroup_validity {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (Y : TupleListEntry (insert b S) → ZMod p) :
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne))
      (Y ∘ tupleRegroupEquiv S b hb hne) ≤ tupleValidity (insert b S) Y := by
  have h := graphValidity_antitone (tuple_regroup_edges S hs b hb hne)
    (Y ∘ tupleRegroupEquiv S b hb hne)
  rw [graphValidity_pullback] at h
  exact h

lemma tuple_regroup_moment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((tupleR : ℝ)^Fintype.card (CutHalf b α β))⁻¹ * tupleUnmarkedMoment S b hb hne F ≤
      𝔼 Y : TupleListEntry (insert b S) → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
        tupleValidity (insert b S) Y *
          (F (fun v => Y (tupleProjection (insert b S) v.1, j v)))^2 := by
  unfold tupleUnmarkedMoment
  rw [expect_precompose (tupleRegroupEquiv S b hb hne)]
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hV := tuple_regroup_validity S hs b hb hne Y
  have hrest := expect_restrict_first
    (fun j : CutHalf b α β → TupleCutWord α β × TupleListIndex S =>
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2)
    (fun j => mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)) (tupleWordOfHalf b α β)
  rw [card_tupleCutWord hne] at hrest
  have he : (𝔼 j : CutHalf b α β → TupleListIndex (insert b S),
      tupleValidity (insert b S) Y * (F (fun v => Y (tupleProjection (insert b S) v.1,j v)))^2) =
      𝔼 j : CutHalf b α β → TupleCutWord α β × TupleListIndex S,
      tupleValidity (insert b S) Y * (F (fun v =>
        Y (tupleProjection (insert b S) v.1, (tupleMarkIndexEquiv S b hb hne).symm (j v))))^2 := by
    apply Fintype.expect_equiv
      (Equiv.arrowCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne))
    intro j
    simp
  rw [he]
  refine le_trans ?_ hrest
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
  apply expect_le_expect
  intro j _
  dsimp only [Function.comp_apply]
  simp only [tupleRegroup_projection]
  exact mul_le_mul_of_nonneg_right hV (sq_nonneg _)

lemma card_cutHalf_eq_div {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = (Nat.factorial h)^Fintype.card B / 2 := by
  have hh := card_cutHalf b hne
  omega

def tupleHalfCount : ℕ := (Nat.factorial tupleH)^tupleBlocks / 2

lemma card_tupleHalf (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (CutHalf b α β) = tupleHalfCount := by
  simpa only [tupleHalfCount, Fintype.card_fin] using card_cutHalf_eq_div b hne

lemma tupleR_one_le : 1 ≤ (tupleR : ℝ) := by exact_mod_cast tupleR_pos

noncomputable def tupleMarkedConstant : ℝ :=
  (Real.exp tupleKappa - 1)^tupleHalfCount /
    ((tupleR : ℝ)^(tupleT + 1))^tupleHalfCount

lemma tupleMarkedConstant_pos : 0 < tupleMarkedConstant := by
  exact div_pos (pow_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr tupleKappa_pos)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)

lemma tupleMarkedConstant_le (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β) :
    tupleMarkedConstant ≤ (Real.exp tupleKappa - 1)^Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ)^Fintype.card (CutHalf b α β) := by
  rw [card_tupleHalf b hne]
  simp only [TupleListIndex, Fintype.card_fin, Nat.cast_pow]
  apply div_le_div_of_nonneg_left
    (pow_nonneg (sub_nonneg.mpr (Real.one_le_exp tupleKappa_pos.le)) _)
    (pow_pos (pow_pos (Nat.cast_pos.mpr tupleR_pos) _) _)
  exact pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _)
    (pow_le_pow_right₀ tupleR_one_le hs) _

end SquareDifference
end

end OAI
