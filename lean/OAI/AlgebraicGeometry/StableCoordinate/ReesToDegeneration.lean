import OAI.AlgebraicGeometry.StableCoordinate.AssociatedGradedPresentation
import OAI.AlgebraicGeometry.StableCoordinate.GradedDegeneration
import OAI.AlgebraicGeometry.StableCoordinate.CoordinateLeadingDerivation
import OAI.AlgebraicGeometry.StableCoordinate.FactorialClosure

namespace OAI

/-!
# Homogeneous transport from the actual Rees algebra to the degeneration

The concrete presentation equivalence preserves every integer degree in both
directions.  This is proved from homogeneous polynomial representatives and
the exact lower-step criterion for initial forms.  Consequently actual leading
derivations, including their nonzero positive-degree invariants, transport to
the canonical degeneration ring without any additional grading assumptions.
-/

noncomputable section

namespace StableCoordinate.ReesToDegeneration

open MvPolynomial Obstruction Filtration FilteredRees
open GradedPresentationMap AssociatedGradedPresentation WeightedInitial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Homogeneous source polynomials belong to their exact filtration piece. -/
theorem homogeneous_mem_piece {p : P k 5} {d : ℤ}
    (hp : p.IsWeightedHomogeneous presentationWeight d) : p ∈ piece k d := by
  rw [piece_eq_boundedSubmodule]
  exact fun m hm => (hp hm).le

/-- Removing the degree-`d` part of a bounded source polynomial lowers its
filtration index by one, even if `d` is negative. -/
theorem sub_top_mem_piece {p : P k 5} {d : ℤ} (hp : p ∈ piece k d) :
    p - weightedHomogeneousComponent presentationWeight d p ∈ piece k (d - 1) := by
  rw [piece_eq_boundedSubmodule] at hp ⊢
  exact bounded_sub_top hp

/-- The homogeneous component's symbol is exactly the symbol of any bounded
representative in the same degree. -/
theorem sourceInitial_eq_gradedMap_component
    (φ : P k 5 →ₐ[k] A) (d : ℤ) (p : piece k d) :
    sourceInitial φ d p =
      gradedMap φ (weightedHomogeneousComponent presentationWeight d (p : P k 5)) := by
  let q := weightedHomogeneousComponent presentationWeight d (p : P k 5)
  have hqhom : q.IsWeightedHomogeneous presentationWeight d :=
    weightedHomogeneousComponent_isWeightedHomogeneous d (p : P k 5)
  have hq : q ∈ piece k d := homogeneous_mem_piece hqhom
  have hsub : (p : P k 5) - q ∈ piece k (d - 1) := sub_top_mem_piece p.property
  have hinit : sourceInitial φ d p = sourceInitial φ d ⟨q, hq⟩ := by
    apply sub_eq_zero.mp
    rw [← map_sub (sourceInitial φ d)]
    rw [sourceInitial_apply, initial_eq_zero_iff]
    exact ⟨(p : P k 5) - q, hsub, rfl⟩
  rw [hinit, sourceInitial_apply]
  symm
  apply gradedMap_of_homogeneous
  intro m hm
  rw [AssociatedGradedPresentation.monomialWeight_eq_weight]
  exact hqhom (mem_support_iff.mp hm)

/-- Every initial form has a homogeneous polynomial representative in exactly
the same integer degree. -/
theorem initial_has_homogeneous_representative
    (φ : P k 5 →ₐ[k] A) (d : ℤ) (a : imagePiece φ d) :
    ∃ p : P k 5, p.IsWeightedHomogeneous presentationWeight d ∧
      gradedMap φ p = initial (imagePiece φ) (imagePiece_mono φ) d a := by
  rcases a with ⟨a, p, hp, rfl⟩
  refine ⟨weightedHomogeneousComponent presentationWeight d p,
    weightedHomogeneousComponent_isWeightedHomogeneous d p, ?_⟩
  exact (sourceInitial_eq_gradedMap_component φ d ⟨p, hp⟩).symm

variable (k) [IsDomain k]

/-- The concrete quotient equivalence preserves a homogeneous piece in both
directions; its image is precisely the set of degree-`d` initial forms. -/
theorem mem_gPiece_iff (d : ℤ) (g : G k) :
    g ∈ gPiece k d ↔ ∃ a : imagePiece (quotientMap k) d,
      associatedGradedEquiv k g =
        initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k)) d a := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p.IsWeightedHomogeneous presentationWeight d := hp
    refine ⟨⟨quotientMap k p, p, homogeneous_mem_piece hp', rfl⟩, ?_⟩
    change associatedGradedEquiv k (Ideal.Quotient.mk (idealG k) p) = _
    rw [associatedGradedEquiv_mk]
    apply gradedMap_of_homogeneous
    intro m hm
    rw [AssociatedGradedPresentation.monomialWeight_eq_weight]
    exact hp' (mem_support_iff.mp hm)
  · rintro ⟨a, ha⟩
    obtain ⟨p, hp, he⟩ := initial_has_homogeneous_representative (quotientMap k) d a
    have hg : g = Ideal.Quotient.mk (idealG k) p := by
      apply (associatedGradedEquiv k).injective
      rw [ha, associatedGradedEquiv_mk, ← he]
    rw [hg]
    exact mk_mem_gPiece k hp

/-- The actual degree-zero source subalgebra is proper: the initial symbol of
the positive-weight variable `F` (index three) is provably nonzero. -/
theorem source_degreeZeroSubalgebra_ne_top :
    degreeZeroSubalgebra (imagePiece (quotientMap k)) ≠ ⊤ := by
  have hne : associatedGradedEquiv k (gX k 3) ≠ 0 := by
    intro h
    exact gX_ne_zero k 3 ((associatedGradedEquiv k).injective (by simpa using h))
  rw [associatedGradedEquiv_gX] at hne
  exact degreeZeroSubalgebra_ne_top_of_initial_ne_zero
    (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k))
    (by simp [monomialWeight] : 0 < monomialWeight (Finsupp.single (3 : Fin 5) 1))
    (variableElement (quotientMap k) 3) hne

/-- Conjugation through the proved, concrete associated-graded equivalence. -/
def transportDerivation (D : Derivation k (associatedGraded k) (associatedGraded k)) :
    Derivation k (G k) (G k) :=
  CoordinateDerivation.transport (associatedGradedEquiv k).symm D

@[simp] theorem transportDerivation_apply
    (D : Derivation k (associatedGraded k) (associatedGraded k)) (g : G k) :
    transportDerivation k D g =
      (associatedGradedEquiv k).symm (D (associatedGradedEquiv k g)) := rfl

/-- Local nilpotence is retained under the concrete transport. -/
theorem transportDerivation_locallyNilpotent
    (D : Derivation k (associatedGraded k) (associatedGraded k))
    (hD : IsLocallyNilpotent (k := k) (A := associatedGraded k) D) :
    IsLocallyNilpotent (transportDerivation k D) := by
  unfold transportDerivation IsLocallyNilpotent
  exact CoordinateDerivation.transport_locallyNilpotent _ D hD

/-- A nonzero leading derivation remains nonzero in the canonical presentation. -/
theorem transportDerivation_ne_zero
    (D : Derivation k (associatedGraded k) (associatedGraded k)) (hD : D ≠ 0) :
    transportDerivation k D ≠ 0 := by
  unfold transportDerivation
  exact CoordinateDerivation.transport_ne_zero _ D hD

/-- The integer shift on initial forms is the actual `gPiece` shift on the
canonical degeneration, with no reversal or truncation of negative degrees. -/
theorem transportDerivation_homogeneous
    (D : Derivation k (associatedGraded k) (associatedGraded k)) (m : ℤ)
    (hD : ∀ (d : ℤ) (a : imagePiece (quotientMap k) d),
      ∃ b : imagePiece (quotientMap k) (d + m),
        D (initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k)) d a) =
          initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k)) (d + m) b) :
    ∀ (d : ℤ) (g : G k), g ∈ gPiece k d →
      transportDerivation k D g ∈ gPiece k (d + m) := by
  intro d g hg
  obtain ⟨a, ha⟩ := (mem_gPiece_iff k d g).mp hg
  obtain ⟨b, hb⟩ := hD d a
  refine (mem_gPiece_iff k (d + m) _).mpr ⟨b, ?_⟩
  simp only [transportDerivation_apply, AlgEquiv.apply_symm_apply, ha, hb]

/-- The negative distinguished symbol is exactly the image of `gX 0`. -/
theorem associatedGradedEquiv_p :
    associatedGradedEquiv k (gX k 0) =
      initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k)) (-1)
        ⟨quotientMap k (X 0), image_X_zero_mem_neg_one (quotientMap k)⟩ := by
  rw [associatedGradedEquiv_gX]
  unfold initial
  congr 1
  apply Subtype.ext
  simp [homogeneous, monomialWeight, variableElement]

/-- A hypothetical polynomial coordinate system in the source ring produces
the exact nonzero homogeneous LND and positive homogeneous invariant needed
by the canonical degeneration-to-quadric argument.  Properness, separation,
and homogeneous compatibility are all proved, not added as assumptions. -/
theorem coordinate_produces_degeneration_lnd [IsNoetherianRing k]
    (e : P k 4 ≃ₐ[k] Obstruction.A k) (hp : e (X 0) = aX k 0) :
    ∃ (m : ℤ) (D : Derivation k (G k) (G k)),
      D ≠ 0 ∧ IsLocallyNilpotent D ∧
      (∀ (n : ℤ) (g : G k), g ∈ gPiece k n → D g ∈ gPiece k (n + m)) ∧
      D (gX k 0) = 0 ∧
      ∃ (d : ℤ) (η : G k), 0 < d ∧ η ∈ gPiece k d ∧ η ≠ 0 ∧ D η = 0 := by
  obtain ⟨m, δ, hδ, hln, hshift, hpδ, d, a, hd, hane, haδ⟩ :=
    coordinate_produces_leading_lnd_of_noetherian_domain
      (quotientMap k) (fun a => Ideal.Quotient.mk_surjective a)
      (source_degreeZeroSubalgebra_ne_top k) e hp
  refine ⟨m, transportDerivation k δ, transportDerivation_ne_zero k δ hδ,
    transportDerivation_locallyNilpotent k δ hln,
    transportDerivation_homogeneous k δ m hshift, ?_,
    d, (associatedGradedEquiv k).symm
      (initial (imagePiece (quotientMap k)) (imagePiece_mono (quotientMap k)) d a),
    hd, ?_, ?_, ?_⟩
  · rw [transportDerivation_apply, associatedGradedEquiv_p, hpδ, map_zero]
  · exact (mem_gPiece_iff k d _).mpr ⟨a, (associatedGradedEquiv k).apply_symm_apply _⟩
  · intro h
    apply hane
    have he := congrArg (associatedGradedEquiv k) h
    simpa only [AlgEquiv.apply_symm_apply, map_zero] using he
  · rw [transportDerivation_apply, AlgEquiv.apply_symm_apply, haδ, map_zero]

end StableCoordinate.ReesToDegeneration

end

end OAI
