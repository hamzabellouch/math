import OAI.AlgebraicGeometry.StableCoordinate.FrameLiftUniqueness

namespace OAI

/-!
# Normalizing a polynomial determinant frame

A choice of trivialization gives a frame above the desired quadric base, but
its specialization need not be the prescribed initial frame.  A constant unit
rescaling corrects it.  This construction needs no domain or reducedness
hypothesis; those hypotheses enter only the separate uniqueness theorem.
-/

namespace StableCoordinate.FrameLift

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Fiber scaling: the positive-weight column is multiplied by a unit and the
negative-weight row by its inverse. -/
def Frame.scale (F : Frame R) (u : Rˣ) : Frame R where
  a := (u : R) * F.a
  d := (u : R) * F.d
  b := (↑u⁻¹ : R) * F.b
  c := (↑u⁻¹ : R) * F.c
  determinant := by
    calc
      ((u : R) * F.a) * ((↑u⁻¹ : R) * F.c) -
          ((↑u⁻¹ : R) * F.b) * ((u : R) * F.d) =
          ((u : R) * (↑u⁻¹ : R)) * (F.a * F.c - F.b * F.d) := by ring
      _ = 1 := by simp [F.determinant]

@[simp]
theorem Frame.scale_one (F : Frame R) : F.scale 1 = F := by
  apply Frame.ext <;> simp [Frame.scale]

@[simp]
theorem Frame.scale_mul (F : Frame R) (u v : Rˣ) :
    (F.scale u).scale v = F.scale (v * u) := by
  apply Frame.ext <;> simp [Frame.scale, mul_assoc, mul_left_comm, mul_comm]

/-- Scaling acts within a fiber of the map to the quadric. -/
theorem Frame.scale_sameBase (F : Frame R) (u : Rˣ) : SameBase (F.scale u) F := by
  dsimp [SameBase, Frame.scale]
  constructor
  · calc
      ((u : R) * F.a) * ((↑u⁻¹ : R) * F.b) =
          ((u : R) * (↑u⁻¹ : R)) * (F.a * F.b) := by ring
      _ = F.a * F.b := by simp
  constructor
  · calc
      ((u : R) * F.d) * ((↑u⁻¹ : R) * F.c) =
          ((u : R) * (↑u⁻¹ : R)) * (F.d * F.c) := by ring
      _ = F.d * F.c := by simp
  · calc
      ((u : R) * F.d) * ((↑u⁻¹ : R) * F.b) =
          ((u : R) * (↑u⁻¹ : R)) * (F.d * F.b) := by ring
      _ = F.d * F.b := by simp

@[simp]
theorem Frame.map_scale (F : Frame R) (u : Rˣ) (f : R →+* S) :
    (F.scale u).map f = (F.map f).scale (Units.map f.toMonoidHom u) := by
  apply Frame.ext <;> simp [Frame.scale, Frame.map]

/-- The comparison unit sends the first frame exactly to the second. -/
theorem scale_comparison {F G : Frame R} (h : SameBase F G) :
    F.scale (comparisonUnit h) = G := by
  apply Frame.ext
  · exact comparison_a h
  · exact comparison_d h
  · exact comparison_b h
  · exact comparison_c h

/-- Transitivity of equality of the three base coordinates. -/
theorem sameBase_trans {F G H : Frame R} (hFG : SameBase F G) (hGH : SameBase G H) :
    SameBase F H :=
  ⟨hFG.1.trans hGH.1, hFG.2.1.trans hGH.2.1, hFG.2.2.trans hGH.2.2⟩

section Polynomial

open MvPolynomial

variable {σ : Type*}

/-- Correct an arbitrary polynomial lift to the prescribed initial frame by a
constant, invertible fiber scaling. -/
noncomputable def normalizeFrame (F : Frame (MvPolynomial σ R)) (G : Frame R)
    (h : SameBase (F.map constantCoeff) G) : Frame (MvPolynomial σ R) :=
  F.scale (Units.map C.toMonoidHom (comparisonUnit h))

/-- Normalization leaves all three base-coordinate polynomials unchanged. -/
theorem normalizeFrame_sameBase (F : Frame (MvPolynomial σ R)) (G : Frame R)
    (h : SameBase (F.map constantCoeff) G) : SameBase (normalizeFrame F G h) F :=
  F.scale_sameBase _

/-- The normalized polynomial lift has exactly the specified initial frame. -/
@[simp]
theorem normalizeFrame_at_zero (F : Frame (MvPolynomial σ R)) (G : Frame R)
    (h : SameBase (F.map constantCoeff) G) :
    (normalizeFrame F G h).map constantCoeff = G := by
  rw [normalizeFrame, Frame.map_scale]
  have hu : Units.map constantCoeff.toMonoidHom
      (Units.map (C : R →+* MvPolynomial σ R).toMonoidHom (comparisonUnit h)) =
      comparisonUnit h := by
    apply Units.ext
    simp
  rw [hu, scale_comparison h]

/-- Normalization is canonical over a reduced ring. -/
theorem normalizeFrame_unique [IsReduced R]
    (F : Frame (MvPolynomial σ R)) (G : Frame R)
    (h : SameBase (F.map constantCoeff) G)
    (F' : Frame (MvPolynomial σ R)) (hbase : SameBase F' F)
    (hzero : F'.map constantCoeff = G) : F' = normalizeFrame F G h := by
  apply normalized_polynomial_unique
  · exact ⟨hbase.1.trans (normalizeFrame_sameBase F G h).1.symm,
      hbase.2.1.trans (normalizeFrame_sameBase F G h).2.1.symm,
      hbase.2.2.trans (normalizeFrame_sameBase F G h).2.2.symm⟩
  · rw [hzero, normalizeFrame_at_zero]

/-- Coefficient specialization commutes with a coefficient-ring homomorphism. -/
theorem Frame.specialize_map (F : Frame (MvPolynomial σ R)) (θ : R →+* S) :
    (F.map (MvPolynomial.map θ)).map constantCoeff =
      (F.map constantCoeff).map θ := by
  apply Frame.ext <;> simp [Frame.map]

/-- A normalized lift automatically commutes with a fiber scaling whenever
its base-coordinate polynomials are unchanged by that scaling.

For the source's multiplicative fiber action, apply this over the coefficient
ring containing an invertible scaling parameter.  The hypothesis on base
coordinates is checked on the embedded quadric algebra. -/
theorem normalized_lift_scaling_equivariance [IsReduced R]
    (F : Frame (MvPolynomial σ R)) (F₀ : Frame R)
    (hzero : F.map constantCoeff = F₀)
    (θ : R →+* R) (u : Rˣ)
    (href : F₀.map θ = F₀.scale u)
    (hbase : SameBase (F.map (MvPolynomial.map θ)) F) :
    F.map (MvPolynomial.map θ) =
      F.scale (Units.map (C : R →+* MvPolynomial σ R).toMonoidHom u) := by
  apply normalized_polynomial_unique
  · exact sameBase_trans hbase (sameBase_symm (F.scale_sameBase _))
  · rw [Frame.specialize_map, hzero, href, Frame.map_scale, hzero]
    congr 1
    apply Units.ext
    simp

end Polynomial

end StableCoordinate.FrameLift

end OAI
