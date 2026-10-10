import OAI.AlgebraicGeometry.StableCoordinate.FrameScaling
import Mathlib.RingTheory.Polynomial.Nilpotent

namespace OAI

/-!
# Ordinary-polynomial adapters for normalized determinant lifts

The additive-coaction interface uses ordinary and iterated `Polynomial`, while
multivariate frames are convenient for the underlying unit rigidity argument.
These adapters give the same normalization and uniqueness directly for the
coaction parameter type, without changing variables through an equivalence.
-/

namespace StableCoordinate.FrameLift

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Equality of base coordinates is preserved under every ring homomorphism. -/
private theorem sameBase_map_aux {F G : Frame R} (h : SameBase F G) (f : R →+* S) :
    SameBase (F.map f) (G.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Frame.map, map_mul] using congrArg f h.1
  · simpa only [Frame.map, map_mul] using congrArg f h.2.1
  · simpa only [Frame.map, map_mul] using congrArg f h.2.2

/-- Units of an ordinary polynomial ring over a reduced ring are constant. -/
theorem univariate_unit_eq_C_constantCoeff [IsReduced R]
    {p : Polynomial R} (hp : IsUnit p) :
    p = Polynomial.C (Polynomial.constantCoeff p) := by
  have hd : p.natDegree = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact Polynomial.not_isUnit_of_natDegree_pos_of_isReduced p hpos hp
  exact Polynomial.eq_C_of_natDegree_eq_zero hd

/-- Reducedness passes to ordinary polynomial rings. -/
theorem polynomial_isReduced [IsReduced R] : IsReduced (Polynomial R) := by
  rw [isReduced_iff]
  intro p hp
  apply Polynomial.ext
  intro n
  simpa using ((Polynomial.isNilpotent_iff.mp hp) n).eq_zero

/-- Iterated-polynomial version: normalization at the two-parameter origin
is enough for the additive coaction group-law comparison. -/
theorem normalized_bivariate_unique [IsReduced R]
    {F G : Frame (Polynomial (Polynomial R))} (h : SameBase F G)
    (hzero : (F.map Polynomial.constantCoeff).map Polynomial.constantCoeff =
      (G.map Polynomial.constantCoeff).map Polynomial.constantCoeff) : F = G := by
  let : IsReduced (Polynomial R) := polynomial_isReduced
  apply normalized_univariate_unique h
  exact normalized_univariate_unique (sameBase_map_aux h Polynomial.constantCoeff) hzero

/-- Normalize an ordinary-polynomial frame to a prescribed initial frame. -/
noncomputable def normalizePolynomialFrame (F : Frame (Polynomial R)) (G : Frame R)
    (h : SameBase (F.map Polynomial.constantCoeff) G) : Frame (Polynomial R) :=
  F.scale (Units.map Polynomial.C.toMonoidHom (comparisonUnit h))

/-- Ordinary-polynomial normalization does not change the base-coordinate family. -/
theorem normalizePolynomialFrame_sameBase (F : Frame (Polynomial R)) (G : Frame R)
    (h : SameBase (F.map Polynomial.constantCoeff) G) :
    SameBase (normalizePolynomialFrame F G h) F :=
  F.scale_sameBase _

/-- The normalized ordinary-polynomial frame starts at exactly the chosen frame. -/
@[simp]
theorem normalizePolynomialFrame_at_zero (F : Frame (Polynomial R)) (G : Frame R)
    (h : SameBase (F.map Polynomial.constantCoeff) G) :
    (normalizePolynomialFrame F G h).map Polynomial.constantCoeff = G := by
  rw [normalizePolynomialFrame, Frame.map_scale]
  have hu : Units.map Polynomial.constantCoeff.toMonoidHom
      (Units.map (Polynomial.C : R →+* Polynomial R).toMonoidHom (comparisonUnit h)) =
      comparisonUnit h := by
    apply Units.ext
    simp
  rw [hu, scale_comparison h]

/-- Ordinary-polynomial coefficient specialization commutes with a ring map. -/
theorem Frame.specializePolynomial_map (F : Frame (Polynomial R)) (θ : R →+* S) :
    (F.map (Polynomial.mapRingHom θ)).map Polynomial.constantCoeff =
      (F.map Polynomial.constantCoeff).map θ := by
  apply Frame.ext <;> simp [Frame.map]

/-- Ordinary-polynomial covariance under a normalized fiber scaling. -/
theorem normalized_univariate_lift_scaling_equivariance [IsReduced R]
    (F : Frame (Polynomial R)) (F₀ : Frame R)
    (hzero : F.map Polynomial.constantCoeff = F₀)
    (θ : R →+* R) (u : Rˣ)
    (href : F₀.map θ = F₀.scale u)
    (hbase : SameBase (F.map (Polynomial.mapRingHom θ)) F) :
    F.map (Polynomial.mapRingHom θ) =
      F.scale (Units.map (Polynomial.C : R →+* Polynomial R).toMonoidHom u) := by
  apply normalized_univariate_unique
  · exact sameBase_trans hbase (sameBase_symm (F.scale_sameBase _))
  · rw [Frame.specializePolynomial_map, hzero, href, Frame.map_scale, hzero]
    congr 1
    apply Units.ext
    simp

end StableCoordinate.FrameLift

end OAI
