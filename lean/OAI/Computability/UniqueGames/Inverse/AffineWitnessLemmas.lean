import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.AffineWitness

abbrev F2 := ZMod 2

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem add_self_binary (c : C) : c + c = 0 := by
  have h : (1 : F2) + 1 = 0 := by decide
  calc
    c + c = (1 : F2) • c + (1 : F2) • c := by simp
    _ = ((1 : F2) + 1) • c := (add_smul _ _ _).symm
    _ = 0 := by rw [h, zero_smul]

/-- A simultaneous row fiber and column slice, based at `M₀`. Agreement on
`Z` is exactly agreement with all column specifications spanning `Z`. -/
def InSlice (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) : Prop :=
  A.comp M = A.comp M₀ ∧ ∀ w ∈ Z, M w = M₀ w

/-- Changing the representative also changes the affine intercept. -/
theorem translate_target (A : C →ₗ[F2] R) (Z : Submodule F2 D)
    (M₀ M : D →ₗ[F2] C) (hM : InSlice A Z M₀ M)
    (z w : D) (hw : w ∈ Z) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u := by
  rw [map_add, hM.2 w hw]
  calc
    (M z + M₀ w) + (u + M₀ w) = (M z + u) + (M₀ w + M₀ w) := by
      ac_rfl
    _ = M z + u := by rw [add_self_binary, add_zero]

theorem no_affine_representative (e : D →ₗ[F2] F2) (Z : Submodule F2 D)
    (z : D) (h : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    e z = 0 ∧ ∀ w ∈ Z, e w = 0 := by
  have scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  have hz : e z = 0 := by
    rcases scalar_cases (e z) with hz | hz
    · exact hz
    · exact False.elim (h ⟨0, Z.zero_mem, by simpa using hz⟩)
  refine ⟨hz, ?_⟩
  intro w hw
  rcases scalar_cases (e w) with hw0 | hw1
  · exact hw0
  · exact False.elim (h ⟨w, hw, by rw [map_add, hz, zero_add, hw1]⟩)

/-- Rank-one translation in the row kernel. -/
def shift (e : D →ₗ[F2] F2) (h : C) (M : D →ₗ[F2] C) : D →ₗ[F2] C :=
  M + e.smulRight h

@[simp] theorem shift_apply (e : D →ₗ[F2] F2) (h : C)
    (M : D →ₗ[F2] C) (x : D) : shift e h M x = M x + e x • h := rfl

@[simp] theorem shift_zero (e : D →ₗ[F2] F2) (M : D →ₗ[F2] C) :
    shift e 0 M = M := by
  ext x
  simp

theorem shift_add (e : D →ₗ[F2] F2) (h k : C) (M : D →ₗ[F2] C) :
    shift e (h + k) M = shift e h (shift e k M) := by
  ext x
  simp only [shift_apply, smul_add]
  ac_rfl

theorem shift_preserves_slice (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ M : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (hM : InSlice A Z M₀ M) :
    InSlice A Z M₀ (shift e h M) := by
  constructor
  · ext x
    have hx := LinearMap.congr_fun hM.1 x
    have hh : A (h : C) = 0 := h.property
    simpa only [LinearMap.comp_apply, shift_apply, map_add, map_smul,
      hh, smul_zero, add_zero] using hx
  · intro w hw
    simp only [shift_apply, heZ w hw, zero_smul, add_zero]
    exact hM.2 w hw

theorem shift_preserves_target (e : D →ₗ[F2] F2) (z : D) (hz : e z = 0)
    (u h : C) (M : D →ₗ[F2] C) :
    shift e h M z + u = M z + u := by
  simp only [shift_apply, hz, zero_smul, add_zero]

/-- Normalization preserves every affine target value on the complete slice. -/
theorem normalize (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (h : ∃ w ∈ Z, e (z + w) = 1) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  obtain ⟨w, hw, he⟩ := h
  exact ⟨z + w, u + M₀ w, he, fun M hM => translate_target A Z M₀ M hM z w hw u⟩

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-! Conversion between explicitly listed affine column specifications and the
span-based slice used in first-bit normalization. -/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R ι : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem columns_iff_span (q : ι → D) (t : ι → C)
    (M₀ M : D →ₗ[F2] C) (hM₀ : ∀ i, M₀ (q i) = t i) :
    (∀ i, M (q i) = t i) ↔
      ∀ w ∈ Submodule.span F2 (Set.range q), M w = M₀ w := by
  constructor
  · intro hM w hw
    apply LinearMap.eqOn_span (s := Set.range q) (x := w) ?_ hw
    rintro _ ⟨i, rfl⟩
    exact (hM i).trans (hM₀ i).symm
  · intro hM i
    exact (hM (q i) (Submodule.subset_span ⟨i, rfl⟩)).trans (hM₀ i)

/-- A nonempty explicit affine row/column system is precisely the based slice.
The right-hand sides `S₀` and `t` are retained without homogenization. -/
theorem explicit_slice_iff (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow : A.comp M₀ = S₀) (hcol : ∀ i, M₀ (q i) = t i) :
    (A.comp M = S₀ ∧ ∀ i, M (q i) = t i) ↔
      InSlice A (Submodule.span F2 (Set.range q)) M₀ M := by
  unfold InSlice
  rw [hrow, columns_iff_span q t M₀ M hcol]

/-- The affine target value after normalization is unchanged at every matrix
satisfying the original, explicitly listed row and column equations. -/
theorem translate_explicit_target (A : C →ₗ[F2] R) (S₀ : D →ₗ[F2] R)
    (q : ι → D) (t : ι → C) (M₀ M : D →ₗ[F2] C)
    (hrow₀ : A.comp M₀ = S₀) (hcol₀ : ∀ i, M₀ (q i) = t i)
    (hrow : A.comp M = S₀) (hcol : ∀ i, M (q i) = t i)
    (z w : D) (hw : w ∈ Submodule.span F2 (Set.range q)) (u : C) :
    M (z + w) + (u + M₀ w) = M z + u :=
  translate_target A _ M₀ M
    ((explicit_slice_iff A S₀ q t M₀ M hrow₀ hcol₀).mp ⟨hrow, hcol⟩) z w hw u

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-!
# Agreement counting for a folded action

A function that changes by an injectively encoded group element under a group
action can agree with an invariant target on at most one point per orbit.  The
proof injects the product of the acting group and the agreement set into the
underlying finite space.  Freeness of the action is not an additional premise:
the folding law and injectivity of the encoding force the needed freeness.

Only elementary group and finite-cardinality infrastructure is used here.
-/

namespace UniqueGamesTheorem.Inverse

variable {H X Y : Type*} [AddGroup H] [AddGroup Y]

/-- Translates of distinct agreement witnesses are distinct.  The encoding need
not be given as a homomorphism: only its injectivity and the displayed folding
identity are needed for this conclusion. -/
theorem folded_action_injective
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Function.Injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val) := by
  intro a b hab
  have htarget : target a.2.val = target b.2.val := by
    calc
      target a.2.val = target (shift a.1 a.2.val) :=
        (target_invariant a.1 a.2.val).symm
      _ = target (shift b.1 b.2.val) := congrArg target hab
      _ = target b.2.val := target_invariant b.1 b.2.val
  have hfold : F a.2.val + embed a.1 = F b.2.val + embed b.1 := by
    calc
      F a.2.val + embed a.1 = F (shift a.1 a.2.val) :=
        (folded a.1 a.2.val).symm
      _ = F (shift b.1 b.2.val) := congrArg F hab
      _ = F b.2.val + embed b.1 := folded b.1 b.2.val
  rw [a.2.property, b.2.property, htarget] at hfold
  have hh : a.1 = b.1 := embed_injective (add_left_cancel hfold)
  have hx : a.2.val = b.2.val := by
    have hshift : shift a.1 a.2.val = shift a.1 b.2.val := by
      simpa only [hh] using hab
    have hinverse := congrArg (shift (-a.1)) hshift
    simpa only [← shift_add, neg_add_cancel, shift_zero] using hinverse
  exact Prod.ext hh (Subtype.ext hx)

/-- The agreement set of a folded function with an invariant target occupies
at most the reciprocal of the size of the acting group, in denominator-free
finite-cardinality form. -/
theorem folded_action_card_mul_agreement_le
    [Fintype H] [Fintype X] [DecidableEq Y]
    (shift : H → X → X)
    (shift_zero : ∀ x, shift 0 x = x)
    (shift_add : ∀ h k x, shift (h + k) x = shift h (shift k x))
    (embed : H → Y) (embed_injective : Function.Injective embed)
    (F target : X → Y)
    (folded : ∀ h x, F (shift h x) = F x + embed h)
    (target_invariant : ∀ h x, target (shift h x) = target x) :
    Fintype.card H * Fintype.card {x : X // F x = target x} ≤
      Fintype.card X := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective
      (fun a : H × {x : X // F x = target x} => shift a.1 a.2.val)
      (folded_action_injective shift shift_zero shift_add embed embed_injective
        F target folded target_invariant)

end UniqueGamesTheorem.Inverse

end

section

/-!
# Finite indicator expectations as conditional cardinality ratios

These identities use the complete finite sample set in the denominator.  They
also cover the empty set, for which both the expectation and the ratio are zero.
The equivalence variant transfers both the event and the sample space, so no
conditioning factor is lost when changing representations of a slice.
-/

namespace UniqueGamesTheorem.Inverse

open scoped BigOperators

variable {X Y : Type*}

/-- Filtering a finite sample set counts the same objects as first restricting
to the sample set and then imposing the event predicate. -/
theorem card_finset_subtype_eq_filter_card (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    Nat.card {x : s // p x.val} = (s.filter p).card := by
  classical
  let e : {x : s // p x.val} ≃ ↥(s.filter p) :=
    { toFun := fun x =>
        ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x =>
        ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
          (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

/-- An indicator's expectation on a finite set is its agreement count divided
by the cardinality of that same finite set. -/
theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

/-- A bijection preserving the event preserves its count. No choice of a
`Fintype` enumeration is involved in this identity. -/
theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

/-- Transfer the indicator expectation through an equivalence of the complete
finite sample space, including the denominator of the conditional law. -/
theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end UniqueGamesTheorem.Inverse

end

section

/-!
# Size of a binary row kernel

An `r`-row linear constraint on `ℓ` binary coordinates leaves a kernel with at
least `2^(ℓ-r)` elements.  This does not require independent constraint rows.
The exponent uses natural subtraction, so the assertion also covers `r > ℓ`.
The argument is rank--nullity followed by the exact finite-field cardinality
formula; it does not use any inverse theorem or rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse

/-- Even dependent binary row constraints remove at most one dimension per
row. -/
theorem binary_kernel_finrank_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ℓ - r ≤ Module.finrank (ZMod 2) A.ker := by
  have hnull : Module.finrank (ZMod 2) A.range +
      Module.finrank (ZMod 2) A.ker = ℓ := by
    simpa only [Module.finrank_fin_fun] using A.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) A.range ≤ r := by
    simpa only [Module.finrank_fin_fun] using A.range.finrank_le
  apply Nat.sub_le_iff_le_add.mpr
  calc
    ℓ = Module.finrank (ZMod 2) A.ker +
        Module.finrank (ZMod 2) A.range := hnull.symm.trans (Nat.add_comm _ _)
    _ ≤ Module.finrank (ZMod 2) A.ker + r :=
      Nat.add_le_add_left hrange _

/-- The cardinality of the binary row kernel is at least `2^(ℓ-r)`. -/
theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end UniqueGamesTheorem.Inverse

end

end OAI
