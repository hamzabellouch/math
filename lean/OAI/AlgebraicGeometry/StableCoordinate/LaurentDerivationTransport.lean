import OAI.AlgebraicGeometry.StableCoordinate.LaurentPresentation
import OAI.AlgebraicGeometry.StableCoordinate.LocalizationLND
import OAI.AlgebraicGeometry.StableCoordinate.GradedRelationSanity

namespace OAI

/-!
# Transport of the actual graded-hypersurface derivation to its Laurent model

This is the concrete bridge between the graded leading derivation and descent
to the quadric.  The invariant denominator is the actual generator `gX k 0`;
all maps use the explicit equivalence proved in `LaurentPresentation`.
-/

namespace StableCoordinate.LaurentDerivationTransport
open StableCoordinate.Obstruction StableCoordinate.LaurentPresentation

section General
variable {k : Type*} [CommRing k]
variable (D : Derivation k (G k) (G k)) (hp : D (gX k 0) = 0)

/-- Extend to the actual `p`-localization and transport to the Laurent model. -/
noncomputable def lift : Derivation k (LaurentPresentation.Laurent k)
    (LaurentPresentation.Laurent k) :=
  LocalizationLND.transport (B := LaurentPresentation.Laurent k)
    (LocalizationLND.localizeAway D (gX k 0) hp (Localized k))
    (LaurentPresentation.equiv k)

/-- Intertwining holds on every element of the actual graded presentation. -/
theorem lift_intertwine (r : G k) :
    lift D hp (toLaurentBase k r) = toLaurentBase k (D r) := by
  have h := LocalizationLND.transport_apply (B := LaurentPresentation.Laurent k)
    (LocalizationLND.localizeAway D (gX k 0) hp (Localized k))
    (LaurentPresentation.equiv k) (localMap k r)
  change lift D hp (LaurentPresentation.equiv k (localMap k r)) =
    LaurentPresentation.equiv k
      (LocalizationLND.localizeAway D (gX k 0) hp (Localized k) (localMap k r)) at h
  have hlocal : LocalizationLND.localizeAway D (gX k 0) hp (Localized k) (localMap k r) =
      localMap k (D r) := LocalizationLND.localizeAway_algebraMap D (gX k 0) hp (Localized k) r
  simpa only [hlocal, equiv_apply, toLaurent_localMap] using h

/-- The exact coefficient-input formula used by homogeneous Laurent descent. -/
theorem lift_C (b : B k) :
    lift D hp (LaurentPolynomial.C b) = toLaurentBase k (D (baseMap k b)) := by
  rw [← toLaurentBase_baseMap k b, lift_intertwine]

/-- The distinguished Laurent variable is invariant. -/
@[simp] theorem lift_T_one : lift D hp (LaurentPolynomial.T 1) = 0 := by
  have h := lift_intertwine D hp (gX k 0)
  rw [hp, map_zero, toLaurentBase_gX] at h
  exact h

/-- Invariant source elements remain invariant after Laurent transport. -/
theorem lift_kills (r : G k) (hr : D r = 0) :
    lift D hp (toLaurentBase k r) = 0 := by rw [lift_intertwine, hr, map_zero]

/-- Iteration commutes with the concrete presentation map. -/
theorem lift_iterate (n : ℕ) (r : G k) :
    (lift D hp : LaurentPresentation.Laurent k → LaurentPresentation.Laurent k)^[n]
      (toLaurentBase k r) = toLaurentBase k ((D : G k → G k)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, lift_intertwine, Function.iterate_succ_apply']

/-- Local nilpotence needs no additional domain or characteristic hypothesis. -/
theorem lift_locallyNilpotent
    (hD : ∀ r : G k, ∃ n : ℕ, (D : G k → G k)^[n] r = 0) :
    ∀ r : LaurentPresentation.Laurent k, ∃ n : ℕ,
      (lift D hp : LaurentPresentation.Laurent k → LaurentPresentation.Laurent k)^[n] r = 0 :=
  LocalizationLND.transport_locallyNilpotent (B := LaurentPresentation.Laurent k) _ _
    (LocalizationLND.localizeAway_locallyNilpotent D (gX k 0) hp (Localized k) hD)

end General

section Field
variable {k : Type*} [Field k]

/-- The literal source-to-Laurent map is injective; no `IsDomain G` circularity. -/
theorem toLaurentBase_injective : Function.Injective (toLaurentBase k) := by
  intro a b h
  apply GradedRelationSanity.G_away_injective k (Localized k)
  apply (LaurentPresentation.equiv k).injective
  change LaurentPresentation.equiv k (localMap k a) = LaurentPresentation.equiv k (localMap k b)
  simpa only [equiv_apply, toLaurent_localMap] using h

/-- A nonzero leading derivation cannot disappear under the concrete transport. -/
theorem lift_ne_zero (D : Derivation k (G k) (G k)) (hp : D (gX k 0) = 0)
    (hD : D ≠ 0) : lift D hp ≠ 0 := by
  intro hzero
  apply hD
  ext r
  apply toLaurentBase_injective
  have h := congrArg (fun E : Derivation k (LaurentPresentation.Laurent k)
      (LaurentPresentation.Laurent k) => E (toLaurentBase k r)) hzero
  simpa only [lift_intertwine, Derivation.zero_apply, map_zero] using h

/-- Source-invariant nonzero elements stay nonzero and invariant in the Laurent model. -/
theorem lift_nonzero_invariant (D : Derivation k (G k) (G k)) (hp : D (gX k 0) = 0)
    (r : G k) (hr : r ≠ 0) (hDr : D r = 0) :
    toLaurentBase k r ≠ 0 ∧ lift D hp (toLaurentBase k r) = 0 := by
  refine ⟨?_, lift_kills D hp r hDr⟩
  intro h
  apply hr
  apply toLaurentBase_injective
  simpa using h

end Field
end StableCoordinate.LaurentDerivationTransport

end OAI
