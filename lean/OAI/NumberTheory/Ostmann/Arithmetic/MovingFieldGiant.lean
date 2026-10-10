import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantTree

namespace OAI

/-! # The actual moving-giant recursion directly over the spectator field -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFieldGiantAmplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n C : ℕ} → MovingGiantTree n C → ZMod q → ZMod q →
      TreeLeafTuple (ZMod q)ˣ n → ℂ
  | _, _, .leaf s C, x, y, z =>
      g ((s : ZMod q) / ((D : ZMod q) * x * y * C * (show (ZMod q)ˣ from z)))
  | n + 1, _, .node s CL CR u left right, x, y, z =>
      let v := reconstructedEntry (s : ZMod q) (left.frequency : ZMod q)
        (right.frequency : ZMod q) (u : ZMod q)
        (x * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
        (y * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ))
      if v = 0 then 0 else
        movingFieldGiantAmplitude g D left v x z.1 *
          conj (movingFieldGiantAmplitude g D right v y z.2)

/-- This is a field identity on all bulk residues, so the later averaging
does not require an integer lift satisfying the original division tests. -/
theorem MovingGiantTree.exists_field_diagram {q : ℕ} [Fact q.Prime]
    {n C : ℕ} (T : MovingGiantTree n C) (hT : T.UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      (C : ZMod q) = U ∧ (T.frequency : ZMod q) = R.frequency ∧
      ∀ (g : ZMod q → ℂ) (D A B : (ZMod q)ˣ)
        (z : TreeLeafTuple (ZMod q)ˣ n) (b : Bool),
        (if b then conj (movingFieldGiantAmplitude g D T A B z)
          else movingFieldGiantAmplitude g D T A B z) =
          rationalTreeAmplitude g D R A B (transferConjugations n b) z := by
  induction T with
  | leaf s C =>
    let S : (ZMod q)ˣ := Units.mk0 (s : ZMod q) hT.1
    let U : (ZMod q)ˣ := Units.mk0 (C : ZMod q) hT.2
    refine ⟨U, .leaf S U, rfl, rfl, ?_⟩
    intro g D A B z b
    have he : (s : ZMod q) / ((D : ZMod q) * A * B * C * (show (ZMod q)ˣ from z)) =
        (rationalTreeArgument S U D A B z : ZMod q) := by
      simp only [rationalTreeArgument, Units.val_div_eq_div_val, Units.val_mul,
        S, U, Units.val_mk0]
    cases b <;> simp only [movingFieldGiantAmplitude, he, rationalTreeAmplitude,
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
    intro g D A B z b
    let v := reconstructedEntry (s : ZMod q) (left.frequency : ZMod q)
      (right.frequency : ZMod q) (u : ZMod q)
      ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
      ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ))
    have hrec : reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
        ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
        ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q) = v := by
      simp only [v, hfL, hfR, S, U₀, A₀, B₀, Units.val_mul, Units.val_mk0]
    by_cases hv : v = 0
    · cases b <;> simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) = 0 from hv,
        ↓reduceIte, map_zero, rationalTreeAmplitude, hrec, hv, Bool.false_eq_true, dite_true]
    · let V : (ZMod q)ˣ := Units.mk0 v hv
      have hleft := hL g D V A z.1 b
      have hright := hR g D V B z.2 (!b)
      have hV : Units.mk0
          (reconstructedEntry (S : ZMod q) L.frequency R.frequency U₀
            ((A * A₀ * treeLeafProduct n z.1 : (ZMod q)ˣ) : ZMod q)
            ((B * B₀ * treeLeafProduct n z.2 : (ZMod q)ˣ) : ZMod q))
          (by rw [hrec]; exact hv) = V := Units.ext hrec
      simp only [movingFieldGiantAmplitude, show
        reconstructedEntry (s : ZMod q) (left.frequency : ZMod q) (right.frequency : ZMod q)
          (u : ZMod q) ((A : ZMod q) * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
          ((B : ZMod q) * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ)) ≠ 0 from hv,
        ↓reduceIte, rationalTreeAmplitude, transferConjugations]
      rw [dite_eq_right (by rw [hrec]; exact hv), hV, ← hleft, ← hright]
      cases b <;> simp [V, v]

end Ostmann

end OAI
