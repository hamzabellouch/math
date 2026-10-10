import OAI.GroupTheory.Thompson.StandardF

namespace OAI

/-!
# Identification with the standard finite-breakpoint PL definition

The standard condition below states only a finite strictly ordered list of
dyadic knots, the two endpoints, and the powers-of-two affine formulas.
Coverage is derived from the endpoints; it is not an additional premise.
-/

namespace ThompsonNonamenability

/-- The usual increasing PL interval homeomorphisms with finitely many dyadic
breakpoints and slopes in the integer powers of two. -/
def StandardPLCondition (f : UnitInterval ≃ₜ UnitInterval) : Prop :=
  StrictMono f ∧ ∃ n : ℕ, 0 < n ∧
    ∃ knots : Fin (n + 1) → UnitInterval,
      StrictMono knots ∧
      knots 0 = unitIntervalZero ∧
      knots (Fin.last n) = unitIntervalOne ∧
      (∀ i, IsDyadic (knots i : ℝ)) ∧
      ∃ exponent : Fin n → ℤ,
        ∀ (i : Fin n) (x : UnitInterval),
          knots i.castSucc ≤ x → x ≤ knots i.succ →
          (f x : ℝ) = (f (knots i.castSucc) : ℝ) +
            (2 : ℝ) ^ exponent i * ((x : ℝ) - (knots i.castSucc : ℝ))

theorem intervalHomeomorph_standardPL_iff (f : IntervalHomeomorph) :
    (StrictMono f ∧ HasDyadicPLPieces f) ↔ StandardPLCondition f.toHomeomorph := by
  constructor
  · rintro ⟨hf, ⟨w⟩⟩
    exact ⟨hf, w.pieceCount, w.positive, w.knots, w.strictMono_knots,
      w.first, w.last, w.dyadic, w.exponent, w.affine⟩
  · rintro ⟨hf, n, hn, knots, hmono, hfirst, hlast, hdyadic, exponent, haffine⟩
    refine ⟨hf, ⟨?_⟩⟩
    exact {
      pieceCount := n
      positive := hn
      knots := knots
      strictMono_knots := hmono
      first := hfirst
      last := hlast
      dyadic := hdyadic
      cover := SortedSubdivision.cover_of_endpoints hn knots hfirst hlast
      exponent := exponent
      affine := haffine }

namespace F

theorem standardPLCondition (g : F) : StandardPLCondition g.toHomeomorph :=
  (intervalHomeomorph_standardPL_iff g.toIntervalHomeomorph).mp g.property

/-- A faithful identification with the standard PL group carrier, with no
uniform-grid or transport assumption in the right-hand side. -/
def standardPLEquiv : F ≃ {f : UnitInterval ≃ₜ UnitInterval // StandardPLCondition f} where
  toFun g := ⟨g.toHomeomorph, g.standardPLCondition⟩
  invFun f := ⟨⟨f.val⟩, (intervalHomeomorph_standardPL_iff ⟨f.val⟩).mpr f.property⟩
  left_inv g := by
    apply F.ext
    intro x
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

@[simp] theorem standardPLEquiv_apply (g : F) :
    (standardPLEquiv g).val = g.toHomeomorph := rfl

end F

end ThompsonNonamenability

end OAI
