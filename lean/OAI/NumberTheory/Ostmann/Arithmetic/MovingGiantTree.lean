import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSpectatorNode
import OAI.NumberTheory.Ostmann.Construction.TransferConjugations
import OAI.NumberTheory.Ostmann.Tree.RationalTreeLeaves

namespace OAI

/-! # The moving-giant arithmetic in Section 8.1

The integer constants record actual products of regular small entries. At a
reversal, the sampled compensation product `u` is inserted into both children:
their constants are `u * CL` and `u * CR`. The pivot is reconstructed over the
integers first, and only its giant factor is passed to either child.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

inductive MovingGiantTree : ℕ → ℕ → Type
  | leaf (s : ℤ) (C : ℕ) : MovingGiantTree 0 C
  | node {n : ℕ} (s : ℤ) (CL CR u : ℕ)
      (left : MovingGiantTree n (u * CL))
      (right : MovingGiantTree n (u * CR)) : MovingGiantTree (n + 1) (CL * CR)

@[implicit_reducible] def MovingGiantTree.frequency :
    {n C : ℕ} → MovingGiantTree n C → ℤ
  | _, _, .leaf s _ => s
  | _, _, .node s _ _ _ _ _ => s

def movingGiantPivot (s v w : ℤ) (CL CR u XL XR ML MR : ℕ) : ℕ :=
  reconstructedPivot (v * ((XR * CR * MR : ℕ) : ℤ) -
    w * ((XL * CL * ML : ℕ) : ℤ)) s / u

/-- This is the exact division in (8.3), applied to a valid original node. -/
theorem movingGiantPivot_of_node {State : Type*}
    {sys : TransferHistorySystem State} {σ : State} {s v w : ℤ} {P : ℕ}
    (h : ValidTransferNode sys σ s v w P) (CL CR u p XL XR ML MR : ℕ)
    (hu : 0 < u) (hP : P = u * p)
    (hL : sys.leftProduct σ = XL * CL * ML)
    (hR : sys.rightProduct σ = XR * CR * MR) :
    movingGiantPivot s v w CL CR u XL XR ML MR = p := by
  unfold movingGiantPivot
  rw [← hL, ← hR, reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation, hP]
  exact Nat.mul_div_cancel_left p hu

def MovingGiantTree.Integral : {n C : ℕ} → MovingGiantTree n C →
    ℕ → ℕ → TreeLeafTuple ℕ n → Prop
  | _, _, .leaf _ _, _, _, _ => True
  | n + 1, _, .node s CL CR u left right, XL, XR, x =>
      let p := movingGiantPivot s left.frequency right.frequency CL CR u XL XR
        (treeLeafProduct n x.1) (treeLeafProduct n x.2)
      0 < p ∧
      left.frequency * ((XR * CR * treeLeafProduct n x.2 : ℕ) : ℤ) -
          right.frequency * ((XL * CL * treeLeafProduct n x.1 : ℕ) : ℤ) =
        s * ((u * p : ℕ) : ℤ) ∧
      left.Integral p XL x.1 ∧ right.Integral p XR x.2

def MovingGiantTree.UnitsAt (q : ℕ) : {n C : ℕ} → MovingGiantTree n C → Prop
  | _, _, .leaf s C => (s : ZMod q) ≠ 0 ∧ (C : ZMod q) ≠ 0
  | _, _, .node s CL CR u left right =>
      (s : ZMod q) ≠ 0 ∧ (CL : ZMod q) ≠ 0 ∧ (CR : ZMod q) ≠ 0 ∧
      (u : ZMod q) ≠ 0 ∧ left.UnitsAt q ∧ right.UnitsAt q

def TreeNaturalLift {q : ℕ} : (n : ℕ) →
    TreeLeafTuple ℕ n → TreeLeafTuple (ZMod q)ˣ n → Prop
  | 0, x, y => ((show ℕ from x) : ZMod q) = (show (ZMod q)ˣ from y)
  | n + 1, x, y => TreeNaturalLift n x.1 y.1 ∧ TreeNaturalLift n x.2 y.2

theorem TreeNaturalLift.product {q : ℕ} {n : ℕ}
    {x : TreeLeafTuple ℕ n} {y : TreeLeafTuple (ZMod q)ˣ n}
    (h : TreeNaturalLift n x y) :
    ((treeLeafProduct n x : ℕ) : ZMod q) = (treeLeafProduct n y : (ZMod q)ˣ) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [treeLeafProduct, Nat.cast_mul, Units.val_mul]
    rw [ih h.1, ih h.2]

/-- Ordinary integral evaluation, including the inserted-giant zero convention.
All additional smooth and range factors can multiply this spectator factor. -/
noncomputable def movingGiantAmplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n C : ℕ} → MovingGiantTree n C → ℕ → ℕ → TreeLeafTuple ℕ n → ℂ
  | _, _, .leaf s C, XL, XR, x =>
      g ((s : ZMod q) / ((D : ZMod q) * ((XL * XR * C * treeLeafProduct 0 x : ℕ) : ZMod q)))
  | n + 1, _, .node s CL CR u left right, XL, XR, x =>
      let p := movingGiantPivot s left.frequency right.frequency CL CR u XL XR
        (treeLeafProduct n x.1) (treeLeafProduct n x.2)
      if (p : ZMod q) = 0 then 0 else
        movingGiantAmplitude g D left p XL x.1 *
          conj (movingGiantAmplitude g D right p XR x.2)

/-- Every integral moving-giant history has a rational diagram whose constants
and frequencies depend only on the fixed small data and frequency history.
They do not depend on the giant values or on the bulk leaf values. -/
theorem MovingGiantTree.exists_residue_diagram {q : ℕ} [Fact q.Prime]
    {n C : ℕ} (T : MovingGiantTree n C) (hT : T.UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      (C : ZMod q) = U ∧ (T.frequency : ZMod q) = R.frequency ∧
      ∀ (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (XL XR : ℕ)
        (A B : (ZMod q)ˣ) (x : TreeLeafTuple ℕ n) (y : TreeLeafTuple (ZMod q)ˣ n),
        (XL : ZMod q) = A → (XR : ZMod q) = B → TreeNaturalLift n x y →
        T.Integral XL XR x → ∀ b : Bool,
        (if b then conj (movingGiantAmplitude g D T XL XR x)
          else movingGiantAmplitude g D T XL XR x) =
          rationalTreeAmplitude g D R A B (transferConjugations n b) y := by
  induction T with
  | leaf s C =>
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hT.1
    let U : (ZMod q)ˣ := Units.mk0 (C : ZMod q) hT.2
    refine ⟨U, .leaf S U, rfl, rfl, ?_⟩
    intro g D XL XR A B x y hA hB hxy _ b
    change ((show ℕ from x) : ZMod q) = (show (ZMod q)ˣ from y) at hxy
    have he : (s : ZMod q) / ((D : ZMod q) * ((XL * XR * C * treeLeafProduct 0 x : ℕ) : ZMod q)) =
        (rationalTreeArgument S U D A B y : ZMod q) := by
      simp only [Nat.cast_mul, hA, hB, show (C : ZMod q) = U from rfl, hxy,
        rationalTreeArgument, Units.val_div_eq_div_val, Units.val_mul, treeLeafProduct]
      congr 1
      ring
    cases b <;> simp only [movingGiantAmplitude, he, rationalTreeAmplitude,
      transferConjugations, Bool.false_eq_true, ↓reduceIte, Complex.star_def]
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨hs, hCL, hCR, hu, hl, hr⟩ := hT
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hs
    let A₀ : (ZMod q)ˣ := Units.mk0 (CL : ZMod q) hCL
    let B₀ : (ZMod q)ˣ := Units.mk0 (CR : ZMod q) hCR
    let U₀ : (ZMod q)ˣ := Units.mk0 (u : ZMod q) hu
    obtain ⟨UL, L, hUL, hfL, hL⟩ := ihL hl
    obtain ⟨UR, R, hUR, hfR, hR⟩ := ihR hr
    have eL : UL = U₀ * A₀ := by
      apply Units.ext
      simpa only [U₀, A₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUL.symm
    have eR : UR = U₀ * B₀ := by
      apply Units.ext
      simpa only [U₀, B₀, Units.val_mul, Units.val_mk0, Nat.cast_mul] using hUR.symm
    subst UL
    subst UR
    refine ⟨A₀ * B₀, .node S A₀ B₀ U₀ L R, ?_, rfl, ?_⟩
    · simp only [Nat.cast_mul, Units.val_mul, Units.val_mk0, A₀, B₀]
    intro g D XL XR A B x y hA hB hxy hI b
    let p := movingGiantPivot s left.frequency right.frequency CL CR u XL XR
      (treeLeafProduct n x.1) (treeLeafProduct n x.2)
    have hrec : reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
        ((A * A₀ * treeLeafProduct n y.1 : (ZMod q)ˣ) : ZMod q)
        ((B * B₀ * treeLeafProduct n y.2 : (ZMod q)ˣ) : ZMod q) = (p : ZMod q) := by
      have he := congrArg (fun z : ℤ => (z : ZMod q)) hI.2.1
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
        hA, hB, hxy.1.product, hxy.2.product, hfL, hfR] at he
      unfold reconstructedEntry
      apply (div_eq_iff (mul_ne_zero hs hu)).mpr
      simpa only [Units.val_mul, Units.val_mk0, S, A₀, B₀, U₀, mul_assoc,
        mul_comm, mul_left_comm] using he
    by_cases hp : (p : ZMod q) = 0
    · cases b <;> simp only [movingGiantAmplitude, show
        (movingGiantPivot s left.frequency right.frequency CL CR u XL XR
          (treeLeafProduct n x.1) (treeLeafProduct n x.2) : ZMod q) = 0 from hp,
        ↓reduceIte, map_zero, rationalTreeAmplitude, hrec, hp, Bool.false_eq_true,
        dite_true]
    · let V : (ZMod q)ˣ := Units.mk0 (p : ZMod q) hp
      have hVL : (p : ZMod q) = V := rfl
      have hleft := hL g D p XL V A x.1 y.1 hVL hA hxy.1 hI.2.2.1 b
      have hright := hR g D p XR V B x.2 y.2 hVL hB hxy.2 hI.2.2.2 (!b)
      have hV : Units.mk0
          (reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
            ((A * A₀ * treeLeafProduct n y.1 : (ZMod q)ˣ) : ZMod q)
            ((B * B₀ * treeLeafProduct n y.2 : (ZMod q)ˣ) : ZMod q))
          (by rw [hrec]; exact hp) = V := Units.ext hrec
      simp only [movingGiantAmplitude, show
        (movingGiantPivot s left.frequency right.frequency CL CR u XL XR
          (treeLeafProduct n x.1) (treeLeafProduct n x.2) : ZMod q) ≠ 0 from hp,
        ↓reduceIte, rationalTreeAmplitude, transferConjugations]
      rw [dite_eq_right (by rw [hrec]; exact hp), hV, ← hleft, ← hright]
      cases b <;> simp [p]

end Ostmann

end OAI
