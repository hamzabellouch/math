import OAI.Combinatorics.SquareDifference.MatrixBounds

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

noncomputable def indexEnergy {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := (1 / 2) * indexCross H j j

noncomputable def indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := Real.exp (indexEnergy H j)

lemma indexEnergy_nonneg {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    0 ≤ indexEnergy H j := by
  unfold indexEnergy indexCross
  apply mul_nonneg (by norm_num)
  exact sum_nonneg fun x _ => sum_nonneg fun y _ => mul_nonneg (hH x y) (by positivity)

lemma one_le_indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (j : I → J) :
    1 ≤ indexWeight H j := Real.one_le_exp_iff.mpr (indexEnergy_nonneg H hH j)

lemma indexCross_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j k : K → J) :
    indexCross (H.submatrix e e) (j ∘ e) (k ∘ e) = indexCross H j k := by
  unfold indexCross
  apply Fintype.sum_equiv e
  intro x
  exact Fintype.sum_equiv e _ _ (fun y => rfl)

lemma indexCross_transpose {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j k : I → J) :
    indexCross H.transpose k j = indexCross H j k := by
  unfold indexCross
  rw [sum_comm]
  simp only [Matrix.transpose_apply, eq_comm]

lemma indexCross_sum {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ) (j k : I → J) :
    indexCross H (Sum.elim j k) (Sum.elim j k) =
      indexCross (H.submatrix Sum.inl Sum.inl) j j +
      indexCross (H.submatrix Sum.inl Sum.inr) j k +
      indexCross (H.submatrix Sum.inr Sum.inl) k j +
      indexCross (H.submatrix Sum.inr Sum.inr) k k := by
  simp only [indexCross, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.submatrix_apply, sum_add_distrib]
  simp only [add_assoc, add_left_comm]
  rfl

lemma indexWeight_factor {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (j k : I → J) :
    indexWeight H (Sum.elim j k) =
      indexWeight (H.submatrix Sum.inl Sum.inl) j *
      Real.exp (indexCross (H.submatrix Sum.inl Sum.inr) j k) *
      indexWeight (H.submatrix Sum.inl Sum.inl) k := by
  have hrl : H.submatrix Sum.inr Sum.inl = (H.submatrix Sum.inl Sum.inr).transpose := by
    ext x y
    exact hsym x y
  have hrr : H.submatrix Sum.inr Sum.inr = H.submatrix Sum.inl Sum.inl := by
    ext x y
    exact href x y
  simp only [indexWeight, indexEnergy, indexCross_sum, hrl, hrr, indexCross_transpose]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma expect_sum_function {I J M : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [AddCommMonoid M] [Module ℚ≥0 M] (f : (I ⊕ I → J) → M) :
    (𝔼 j : I ⊕ I → J, f j) = 𝔼 j : I → J, 𝔼 k : I → J, f (Sum.elim j k) := by
  calc
    _ = 𝔼 jk : (I → J) × (I → J), f (Sum.elim jk.1 jk.2) := by
      apply Fintype.expect_equiv (Equiv.sumArrowEquivProdArrow I I J)
      intro j
      congr 1
      ext (i | i) <;> rfl
    _ = _ := by rw [← univ_product_univ, expect_product]

lemma reflected_index_weight_lower {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (H : Matrix (I ⊕ I) (I ⊕ I) ℝ)
    (hpos : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y))
    (hsym : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x))
    (href : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y))
    (κ : ℝ) (hκ : 0 ≤ κ) (hgap : (H.submatrix Sum.inl Sum.inr - κ • 1).PosSemidef)
    (f : (I → J) → ℝ) :
    ((Real.exp κ - 1) ^ Fintype.card I / (Fintype.card J : ℝ) ^ Fintype.card I) *
      (𝔼 j : I → J, (f j) ^ 2) ≤
      𝔼 j : I ⊕ I → J, indexWeight H j * f (j ∘ Sum.inl) * f (j ∘ Sum.inr) := by
  rw [expect_sum_function]
  simp only [indexWeight_factor H hsym href]
  have hh := marked_index_average (H.submatrix Sum.inl Sum.inr) κ hκ hgap
    (indexWeight (H.submatrix Sum.inl Sum.inl)) f (one_le_indexWeight _ hpos)
  convert hh using 1
  apply expect_congr rfl
  intro j _
  apply expect_congr rfl
  intro k _
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  ring

lemma card_positionPair (h : ℕ) : Fintype.card (PositionPair h) = h.choose 2 := by
  simpa [Fintype.card_subtype] using (Fintype.card_product_filter_lt (α := Fin h))

lemma interaction_row_sum {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w =
      ∑ _b ∈ S, ∑ p : PositionPair h, δ ^ (p.1.2.val - p.1.1.val) := by
  classical
  unfold interaction
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [sum_comm]
  simp

lemma interaction_row_sum_le {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (v : WordVertex B h) :
    ∑ w : WordVertex B h, interaction S δ v w ≤ (S.card : ℝ) * (h.choose 2 : ℝ) * δ := by
  rw [interaction_row_sum]
  calc
    _ ≤ ∑ _b ∈ S, ∑ _p : PositionPair h, δ := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro p _
      have hg : 1 ≤ p.1.2.val - p.1.1.val := by have := p.2; omega
      simpa using pow_le_pow_of_le_one hδ hδ1 hg
    _ = _ := by simp [card_positionPair, mul_assoc]

abbrev TupleVertex := WordVertex (Fin tupleBlocks) tupleH

abbrev TupleAddress (S : Finset (Fin tupleBlocks)) :=
  {b : Fin tupleBlocks // b ∉ S} → Equiv.Perm (Fin tupleH)

def tupleR : ℕ := Nat.factorial tupleH / 2

abbrev TupleListIndex (S : Finset (Fin tupleBlocks)) := Fin (tupleR ^ S.card)

abbrev TupleListEntry (S : Finset (Fin tupleBlocks)) := TupleAddress S × TupleListIndex S

def tupleProjection (S : Finset (Fin tupleBlocks)) (v : TupleVertex) : TupleAddress S :=
  fun b => v b.1

def tupleCycle : Equiv.Perm (Fin tupleH) := finRotate tupleH

def cycleVertex (j : ℕ) : TupleVertex := fun _ => tupleCycle ^ j

lemma tupleCycle_ne_one : tupleCycle ≠ 1 := by decide

lemma tupleCycle_sq_ne_one : tupleCycle ^ 2 ≠ 1 := by decide

lemma tupleCycle_pow : tupleCycle ^ tupleH = 1 := by
  have ho : orderOf tupleCycle = tupleH := by
    change orderOf (finRotate tupleH) = tupleH
    rw [(isCycle_finRotate_of_le (show 2 ≤ tupleH by decide)).orderOf,
      support_finRotate_of_le (show 2 ≤ tupleH by decide)]
    simp
  simpa only [ho] using pow_orderOf_eq_one tupleCycle

lemma card_tupleVertex : Fintype.card TupleVertex = (Nat.factorial tupleH) ^ tupleBlocks := by
  simp [TupleVertex, WordVertex, Fintype.card_perm]

lemma tupleR_pos : 0 < tupleR := by norm_num [tupleR, tupleH]

instance tupleListIndexNonempty (S : Finset (Fin tupleBlocks)) : Nonempty (TupleListIndex S) :=
  Fin.pos_iff_nonempty.mp (pow_pos tupleR_pos _)

lemma card_cleanBlocks (S : Finset (Fin tupleBlocks)) :
    Fintype.card {b : Fin tupleBlocks // b ∉ S} = tupleBlocks - S.card := by
  classical
  rw [Fintype.card_subtype]
  have heq : (univ.filter fun b : Fin tupleBlocks => b ∉ S) = univ \ S := by ext; simp
  rw [heq, card_sdiff_of_subset (subset_univ S)]
  simp

lemma card_tupleAddress (S : Finset (Fin tupleBlocks)) :
    Fintype.card (TupleAddress S) = (Nat.factorial tupleH) ^ (tupleBlocks - S.card) := by
  simp [TupleAddress, Fintype.card_perm]

noncomputable def tupleListEdges (S : Finset (Fin tupleBlocks)) :
    Finset (TupleListEntry S × TupleListEntry S) := by
  classical
  exact if S.card ≤ tupleT then
    univ.filter fun e => addressEdge tupleCycle (tupleT + 1) e.1.1 e.2.1 else ∅

lemma tupleListEdges_no_loop (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) : e.1 ≠ e.2 := by
  classical
  unfold tupleListEdges at he
  split_ifs at he with hs
  · intro heq
    have hh := (mem_filter.mp he).2
    rw [heq] at hh
    exact addressEdge_irrefl tupleCycle_ne_one (by norm_num [tupleT]) e.2.1 hh
  · simp at he

lemma tupleListEdges_no_opp (S : Finset (Fin tupleBlocks))
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) :
    (e.2, e.1) ∉ tupleListEdges S := by
  classical
  unfold tupleListEdges at he ⊢
  split_ifs at he ⊢ with hs
  · intro hop
    apply addressEdge_asymm tupleCycle_sq_ne_one _ (mem_filter.mp he).2 (mem_filter.mp hop).2
    rw [card_cleanBlocks]
    simp only [tupleBlocks, tupleT]
    omega
  · simp at he

lemma cycle_addressEdge (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT) (j : ℕ) :
    addressEdge tupleCycle (tupleT + 1)
      (tupleProjection S (cycleVertex j)) (tupleProjection S (cycleVertex (j + 1))) := by
  have hh : tupleT + 1 ≤ Fintype.card {b : Fin tupleBlocks // b ∉ S} := by
    rw [card_cleanBlocks]
    change tupleT + 1 ≤ (2 * tupleT + 1) - S.card
    omega
  convert addressEdge_full_shift tupleCycle (tupleT + 1) hh
    (tupleProjection S (cycleVertex j)) using 1
  funext b
  exact pow_succ tupleCycle j

lemma cycle_listEdge (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (j : ℕ) (i k : TupleListIndex S) :
    ((tupleProjection S (cycleVertex j), i), (tupleProjection S (cycleVertex (j + 1)), k)) ∈
      tupleListEdges S := by
  classical
  simp only [tupleListEdges, ite_eq_left hs, mem_filter, mem_univ, true_and]
  exact cycle_addressEdge S hs j

lemma expect_precompose {I K J M : Type*} [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : I ≃ K) (f : (I → J) → M) :
    (𝔼 j : I → J, f j) = 𝔼 j : K → J, f (j ∘ e) := by
  apply Fintype.expect_equiv (Equiv.arrowCongr e (Equiv.refl J))
  intro j
  congr 1
  funext i
  simp

lemma indexWeight_equiv {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq J]
    (e : I ≃ K) (H : Matrix K K ℝ) (j : K → J) :
    indexWeight (H.submatrix e e) (j ∘ e) = indexWeight H j := by
  simp only [indexWeight, indexEnergy, indexCross_equiv]

lemma marked_interaction_weight_lower {B : Type*} [Fintype B] [DecidableEq B]
    {J : Type*} [Fintype J] [DecidableEq J]
    (S : Finset B) (b : B) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (f : (CutHalf b α β → J) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card J : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 j : CutHalf b α β → J, (f j) ^ 2) ≤
      𝔼 j : WordVertex B tupleH → J, indexWeight (interaction S tupleDelta) j *
        f (fun x => j x.1) * f (fun x => j (reflect b α β x.1)) := by
  classical
  let e := halfSumEquiv b hαβ
  let H : Matrix (CutHalf b α β ⊕ CutHalf b α β) (CutHalf b α β ⊕ CutHalf b α β) ℝ :=
    Matrix.submatrix (interaction S tupleDelta) e e
  have hp : ∀ x y, 0 ≤ H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_nonneg S tupleDelta_pos.le x.1 y.1
  have hs : ∀ x y, H (Sum.inr x) (Sum.inl y) = H (Sum.inl y) (Sum.inr x) :=
    fun x y => interaction_symm S tupleDelta _ _
  have hr : ∀ x y, H (Sum.inr x) (Sum.inr y) = H (Sum.inl x) (Sum.inl y) :=
    fun x y => interaction_reflect S tupleDelta b α β x.1 y.1
  have hg : (H.submatrix Sum.inl Sum.inr - tupleKappa • 1).PosSemidef :=
    crossInteraction_gap S b hb α β
  have hh := reflected_index_weight_lower H hp hs hr tupleKappa tupleKappa_pos.le hg f
  rw [expect_precompose e] at hh
  have hw (j : WordVertex B tupleH → J) :
      indexWeight H (j ∘ e) = indexWeight (interaction S tupleDelta) j :=
    indexWeight_equiv e _ j
  refine hh.trans_eq ?_
  apply expect_congr rfl
  intro j _
  rw [hw]
  rfl

noncomputable def tupleWeight (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : ℝ := indexWeight (interaction S tupleDelta) j

noncomputable def tupleValidity {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : ℝ :=
  ∏ e ∈ tupleListEdges S, squareIndicator (Y e.2 - Y e.1)

def tupleOutput {p : ℕ} (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    TupleVertex → ZMod p := fun v => Y (tupleProjection S v, j v)

noncomputable def tupleComponent {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j)

noncomputable def tupleCutForm {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  tupleComponent S (fun z => F (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))

lemma tupleValidity_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : 0 ≤ tupleValidity S Y := by
  unfold tupleValidity
  exact prod_nonneg fun e _ => squareIndicator_nonneg _

lemma tupleValidity_le_one {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : tupleValidity S Y ≤ 1 := by
  unfold tupleValidity
  exact prod_le_one₀ (fun e _ => squareIndicator_nonneg _) (fun e _ => squareIndicator_le_one _)

lemma tupleProjection_reflect (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∈ S) (α β : Fin tupleH) (v : TupleVertex) :
    tupleProjection S (reflect b α β v) = tupleProjection S v := by
  funext a
  have hab : a.1 ≠ b := by intro h; exact a.2 (h ▸ hb)
  simp [tupleProjection, reflect, hab]

lemma tuple_marked_lower {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hαβ : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    ((Real.exp tupleKappa - 1) ^ Fintype.card (CutHalf b α β) /
      (Fintype.card (TupleListIndex S) : ℝ) ^ Fintype.card (CutHalf b α β)) *
      (𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun x => Y (tupleProjection S x.1, j x))) ^ 2) ≤
      tupleCutForm S b α β F := by
  classical
  unfold tupleCutForm tupleComponent
  rw [mul_expect]
  apply expect_le_expect
  intro Y _
  have hh := mul_le_mul_of_nonneg_left
    (marked_interaction_weight_lower S b hb hαβ
      (fun j : CutHalf b α β → TupleListIndex S =>
        F (fun x => Y (tupleProjection S x.1, j x)))) (tupleValidity_nonneg S Y)
  simp only [mul_expect] at hh ⊢
  convert hh using 1
  · apply expect_congr rfl
    intro j _
    ring
  · apply expect_congr rfl
    intro j _
    simp only [tupleWeight, tupleOutput, tupleProjection_reflect S b hb α β]
    ring

lemma indexEnergy_le_of_row {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (hH : ∀ x y, 0 ≤ H x y) (C : ℝ)
    (hC : ∀ x, ∑ y, H x y ≤ C) (j : I → J) :
    indexEnergy H j ≤ (Fintype.card I : ℝ) * C / 2 := by
  unfold indexEnergy indexCross
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ x, ∑ y, H x y := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      split_ifs <;> simp_all
    _ ≤ (1 / 2 : ℝ) * ∑ _x : I, C :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => hC x) (by norm_num)
    _ = _ := by simp; ring

noncomputable def tupleWeightBound : ℝ :=
  Real.exp ((Fintype.card TupleVertex : ℝ) * (tupleT + 1) *
    (tupleH.choose 2 : ℝ) * tupleDelta / 2)

lemma tupleWeightBound_pos : 0 < tupleWeightBound := Real.exp_pos _

lemma tupleWeight_one_le (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : 1 ≤ tupleWeight S j :=
  one_le_indexWeight _ (interaction_nonneg S tupleDelta_pos.le) j

lemma tupleWeight_le (S : Finset (Fin tupleBlocks)) (hS : S.card ≤ tupleT + 1)
    (j : TupleVertex → TupleListIndex S) : tupleWeight S j ≤ tupleWeightBound := by
  unfold tupleWeight tupleWeightBound indexWeight
  apply Real.exp_le_exp.mpr
  refine (indexEnergy_le_of_row (interaction S tupleDelta) (interaction_nonneg S tupleDelta_pos.le)
    ((S.card : ℝ) * (tupleH.choose 2 : ℝ) * tupleDelta)
    (interaction_row_sum_le S tupleDelta_pos.le tupleDelta_le_one) j).trans ?_
  have hSc : (S.card : ℝ) ≤ (tupleT : ℝ) + 1 := by exact_mod_cast hS
  have hδ := tupleDelta_pos.le
  calc
    _ ≤ (Fintype.card TupleVertex : ℝ) *
        (((tupleT : ℝ) + 1) * (tupleH.choose 2 : ℝ) * tupleDelta) / 2 := by gcongr
    _ = _ := by ring

lemma tupleComponent_nonneg {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) (hG : ∀ z, 0 ≤ G z) :
    0 ≤ tupleComponent S G := by
  apply expect_nonneg
  intro Y _
  apply expect_nonneg
  intro j _
  exact mul_nonneg (mul_nonneg (tupleValidity_nonneg S Y)
    (le_trans (by norm_num) (tupleWeight_one_le S j))) (hG _)

lemma tupleComponent_mass_le {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (hS : S.card ≤ tupleT + 1) : tupleComponent (p := p) S (fun _ => 1) ≤ tupleWeightBound := by
  unfold tupleComponent
  calc
    _ ≤ 𝔼 _Y : TupleListEntry S → ZMod p,
        𝔼 _j : TupleVertex → TupleListIndex S, tupleWeightBound := by
      apply expect_le_expect
      intro Y _
      apply expect_le_expect
      intro j _
      rw [mul_one]
      calc
        tupleValidity S Y * tupleWeight S j ≤ 1 * tupleWeight S j :=
          mul_le_mul_of_nonneg_right (tupleValidity_le_one S Y)
            (le_trans (by norm_num) (tupleWeight_one_le S j))
        _ ≤ tupleWeightBound := by simpa using tupleWeight_le S hS j
    _ = _ := by simp

lemma squareIndicator_ne_zero_iff {F : Type*} [Field F] (x : F) :
    squareIndicator x ≠ 0 ↔ x ≠ 0 ∧ IsSquare x := by
  classical
  simp only [squareIndicator]
  split_ifs with h <;> simp_all

lemma tupleValidity_edge {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) (hY : tupleValidity S Y ≠ 0)
    (e : TupleListEntry S × TupleListEntry S) (he : e ∈ tupleListEdges S) :
    Y e.2 - Y e.1 ≠ 0 ∧ IsSquare (Y e.2 - Y e.1) := by
  exact (squareIndicator_ne_zero_iff _).mp (prod_ne_zero_iff.mp hY e he)

lemma tuple_cycle_support {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (hS : S.card ≤ tupleT) (Y : TupleListEntry S → ZMod p)
    (hY : tupleValidity S Y ≠ 0) (j : TupleVertex → TupleListIndex S) (k : ℕ) :
    tupleOutput S Y j (cycleVertex (k + 1)) - tupleOutput S Y j (cycleVertex k) ≠ 0 ∧
    IsSquare (tupleOutput S Y j (cycleVertex (k + 1)) - tupleOutput S Y j (cycleVertex k)) := by
  exact tupleValidity_edge S Y hY _
    (cycle_listEdge S hS k (j (cycleVertex k)) (j (cycleVertex (k + 1))))

lemma cycleVertex_period (j : ℕ) : cycleVertex (j + tupleH) = cycleVertex j := by
  funext b
  simp [cycleVertex, pow_add, tupleCycle_pow]

lemma tupleWeight_empty (j : TupleVertex → TupleListIndex ∅) : tupleWeight ∅ j = 1 := by
  simp [tupleWeight, indexWeight, indexEnergy, indexCross, interaction]

lemma tuple_leading_mass {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    |tupleComponent (p := p) ∅ (fun _ => 1) -
        (1 / 2 : ℝ) ^ (tupleListEdges ∅).card| ≤
      ((tupleListEdges ∅).card : ℝ) * ((Real.sqrt p + 1) / (2 * p)) := by
  have heq : tupleComponent (p := p) ∅ (fun _ => 1) =
      𝔼 Y : TupleListEntry ∅ → ZMod p, tupleValidity ∅ Y := by
    simp [tupleComponent, tupleWeight_empty]
  rw [heq]
  exact graph_count hp (tupleListEdges ∅) (tupleListEdges_no_loop ∅) (tupleListEdges_no_opp ∅)

noncomputable def reflectEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Equiv.Perm (WordVertex B h) :=
  Function.Involutive.toPerm (reflect b α β) (reflect_involutive b α β)

lemma interaction_zero_of_unmarked_word {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) (v w : WordVertex B h)
    (hvw : v b ≠ w b) : interaction S δ v w = 0 := by
  classical
  apply interaction_eq_zero_of_not_neighbour
  intro c hc p heq
  apply hvw
  have hcb : b ≠ c := by intro h; exact hb (h ▸ hc)
  have hh := congrArg (fun v : WordVertex B h => v b) heq
  simpa [vertexSwap, hcb] using hh.symm

lemma unmarked_crossInteraction_zero {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S) {α β : Fin h} (hne : α ≠ β) :
    crossInteraction S δ b α β = 0 := by
  classical
  ext x y
  apply interaction_zero_of_unmarked_word S δ b hb
  intro heq
  have hn : ¬ cutPlus b α β (reflect b α β y.1) :=
    by
      rw [cutPlus_reflect_iff_not b hne]
      exact not_not.mpr y.2
  apply hn
  change (reflect b α β y.1 b).symm α < (reflect b α β y.1 b).symm β
  rw [← heq]
  exact x.2

lemma unmarked_weight_factor {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    {J : Type*} [DecidableEq J] (S : Finset B) (δ : ℝ) (b : B) (hb : b ∉ S)
    {α β : Fin h} (hne : α ≠ β) (j k : CutHalf b α β → J) :
    indexWeight (Matrix.submatrix (interaction S δ) (halfSumEquiv b hne) (halfSumEquiv b hne))
      (Sum.elim j k) =
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) j *
      indexWeight (Matrix.submatrix (interaction S δ) Subtype.val Subtype.val) k := by
  classical
  rw [indexWeight_factor]
  · have hz := unmarked_crossInteraction_zero S δ b hb hne
    change indexWeight _ j * Real.exp (indexCross (crossInteraction S δ b α β) j k) *
      indexWeight _ k = _
    rw [hz]
    simp only [indexCross, Matrix.zero_apply, zero_mul, sum_const_zero, Real.exp_zero,
      mul_one]
    rfl
  · intro x y
    exact interaction_symm S δ _ _
  · intro x y
    exact interaction_reflect S δ b α β x.1 y.1

end SquareDifference
end

end OAI
