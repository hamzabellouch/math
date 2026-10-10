import OAI.NumberTheory.Ostmann.Construction.PrimeSources

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

def Pattern (τ : ι → ℕ) := {r : Setoid ι // r ≤ Setoid.ker τ}

def patternCode {τ : ι → ℕ} (p : Pattern τ) : ι → ι → Bool :=
  fun i j => decide (p.val.r i j)

omit [Fintype ι] [DecidableEq ι] in
theorem patternCode_injective (τ : ι → ℕ) : Function.Injective (patternCode (τ := τ)) := by
  intro p q h
  apply Subtype.ext
  apply Setoid.ext
  intro i j
  exact decide_eq_decide.mp (congrFun (congrFun h i) j)

instance patternFintype (τ : ι → ℕ) : Fintype (Pattern τ) :=
  Fintype.ofInjective patternCode (patternCode_injective τ)

instance patternDecidableEq (τ : ι → ℕ) : DecidableEq (Pattern τ) := Classical.decEq _

theorem card_pattern_le (τ : ι → ℕ) :
    Fintype.card (Pattern τ) ≤ 2 ^ (Fintype.card ι * Fintype.card ι) := by
  have h := Fintype.card_le_of_injective (patternCode (τ := τ)) (patternCode_injective τ)
  simpa only [Fintype.card_fun, Fintype.card_bool, ← pow_mul] using h

def patternOf (τ : ι → ℕ) (w : ι → κ) : Pattern τ :=
  ⟨Setoid.ker (fun i => (τ i, w i)), fun _ _ h => congrArg Prod.fst h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem patternOf_rel (τ : ι → ℕ) (w : ι → κ) (i j : ι) :
    (patternOf τ w).val.r i j ↔ τ i = τ j ∧ w i = w j := by
  change (τ i, w i) = (τ j, w j) ↔ _
  simp only [Prod.mk.injEq]

abbrev Block {τ : ι → ℕ} (p : Pattern τ) := Quotient p.val

instance blockFintype {τ : ι → ℕ} (p : Pattern τ) : Fintype (Block p) := Fintype.ofFinite _
instance blockDecidableEq {τ : ι → ℕ} (p : Pattern τ) : DecidableEq (Block p) := Classical.decEq _

def label {τ : ι → ℕ} (p : Pattern τ) (i : ι) : Block p := Quotient.mk p.val i

omit [Fintype ι] [DecidableEq ι] in
theorem label_surjective {τ : ι → ℕ} (p : Pattern τ) : Function.Surjective (label p) :=
  Quotient.mk_surjective

omit [DecidableEq ι] in
theorem card_block_le {τ : ι → ℕ} (p : Pattern τ) :
    Fintype.card (Block p) ≤ Fintype.card ι :=
  Fintype.card_le_of_surjective (label p) (label_surjective p)

def blockType {τ : ι → ℕ} (p : Pattern τ) : Block p → ℕ :=
  Quotient.lift τ (fun _ _ h => p.property h)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem blockType_label {τ : ι → ℕ} (p : Pattern τ) (i : ι) :
    blockType p (label p i) = τ i := rfl

def BlockDraw {τ : ι → ℕ} (p : Pattern τ) (κ : Type*) :=
  {b : Block p → κ // Function.Injective (fun q => (blockType p q, b q))}

instance blockDrawFintype [Fintype κ] {τ : ι → ℕ} (p : Pattern τ) :
    Fintype (BlockDraw p κ) := inferInstanceAs (Fintype {b : Block p → κ //
      Function.Injective (fun q => (blockType p q, b q))})

def expand {τ : ι → ℕ} (p : Pattern τ) (b : BlockDraw p κ) : ι → κ :=
  fun i => b.val (label p i)

omit [Fintype ι] [DecidableEq ι] in
theorem patternOf_expand {τ : ι → ℕ} (p : Pattern τ) (b : BlockDraw p κ) :
    patternOf τ (expand p b) = p := by
  apply Subtype.ext
  apply Setoid.ext
  intro i j
  constructor
  · intro h
    apply Quotient.exact
    apply b.property
    exact h
  · intro h
    apply Prod.ext
    · exact p.property h
    · exact congrArg b.val (Quotient.sound h)

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
