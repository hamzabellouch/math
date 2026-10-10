import OAI.Combinatorics.BinaryEdit.EncodingUpper
import OAI.Combinatorics.BinaryEdit.EditMetric
import OAI.Combinatorics.BinaryEdit.Distortion

namespace OAI

/-! Distortion transport through finite images of fixed-width codes. -/

noncomputable section
namespace TreeEdit.BinaryLower

universe u

/-- The concatenation extension, viewed in its exact-length target type. -/
def encodedWord {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (x : Word α M) : Word Bool (M * P) :=
  ⟨encode c x.val, by rw [length_encode, x.property]⟩

/-- The actual finite image, rather than an abstract copy of the source set. -/
def encodedSet {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (W : Finset (Word α M)) : Finset (Word Bool (M * P)) :=
  W.image (encodedWord c)

lemma encodedWord_injective_of_lower {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    Function.Injective (encodedWord (M := M) c) := by
  intro x y hxy
  apply Subtype.ext
  apply ed_eq_zero_iff.mp
  have hval : encode c x.val = encode c y.val := congrArg Subtype.val hxy
  have h := hlower x y
  rw [hval, ed_self, Nat.cast_zero] at h
  have hed : (ed x.val y.val : ℝ) ≤ 0 := nonpos_of_mul_nonpos_right h ha
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hed)

lemma encodedSet_card {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (W : Finset (Word α M)) : (encodedSet c W).card = W.card := by
  exact Finset.card_image_of_injective W (encodedWord_injective_of_lower c ha hlower)

/-- The map from source membership witnesses into membership witnesses of the
encoded finite set, with no choice of an inverse. -/
def encodedMember {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (W : Finset (Word α M)) : {x : Word α M // x ∈ W} →
      {y : Word Bool (M * P) // y ∈ encodedSet c W} :=
  fun x => ⟨encodedWord c x.val, Finset.mem_image_of_mem _ x.property⟩

lemma encodedMember_injective {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (W : Finset (Word α M)) : Function.Injective (encodedMember c W) := by
  intro x y hxy
  apply Subtype.ext
  apply encodedWord_injective_of_lower c ha hlower
  exact congrArg Subtype.val hxy

/-- Distortion transport for the concrete finite image of a bi-Lipschitz code. -/
lemma c1_le_encodedSet_mul {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (hupper : ∀ x y : Word α M,
      (ed (encode c x.val) (encode c y.val) : ℝ) ≤
        b * (ed x.val y.val : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        (b / a) * binarySetDistortion (encodedSet c W) := by
  classical
  have : Nontrivial {x : Word α M // x ∈ W} := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < W.card by omega)
    refine ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩⟩
    exact fun h => hxy (congrArg Subtype.val h)
  have hg := encodedMember_injective c ha hlower W
  have : Nontrivial {y : Word Bool (M * P) // y ∈ encodedSet c W} := hg.nontrivial
  unfold binarySetDistortion
  refine c1_le_bilip_mul _ _ ?_ ?_ ?_ (encodedMember c W) hg a b ha hb ?_ ?_
  · intro x y
    exact Nat.cast_nonneg _
  · intro x y
    exact Nat.cast_nonneg _
  · intro x y hxy
    apply Nat.cast_pos.mpr
    apply editDistance_pos_iff.mpr
    intro h
    exact hxy (Subtype.ext (Subtype.ext h))
  · intro x y
    exact hlower x.val y.val
  · intro x y
    exact hupper x.val y.val

/-- The scale cancels: lower factor `P/804` and upper factor `P` lose only `804`. -/
lemma c1_le_804_encodedSet {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (hP : 0 < P)
    (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    (hlower : ∀ x y : Word α M,
      ((P : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        804 * binarySetDistortion (encodedSet c W) := by
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have h := c1_le_encodedSet_mul c W hW (a := (P : ℝ) / 804) (b := (P : ℝ))
    (by positivity) hPR hlower (fun x y => encode_editDistance_le_real c x.val y.val)
  have hratio : (P : ℝ) / ((P : ℝ) / 804) = 804 := by
    field_simp
  simpa only [hratio] using h

/-- Existential form used by the finite-tree binary-family construction. -/
theorem exists_binary_image_of_code {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (hP : 0 < P)
    (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    (hlower : ∀ x y : Word α M,
      ((P : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    ∃ V : Finset (Word Bool (M * P)), 2 ≤ V.card ∧
      c1 {x : Word α M // x ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) / 804 ≤
          binarySetDistortion V := by
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  refine ⟨encodedSet c W, ?_, ?_⟩
  · rw [encodedSet_card c (by positivity : (0 : ℝ) < P / 804) hlower W]
    exact hW
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 804)).mpr
    simpa only [mul_comm] using c1_le_804_encodedSet c hP W hW hlower

end TreeEdit.BinaryLower

end

end OAI
