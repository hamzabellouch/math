import OAI.Analysis.BoundedHochschild.ProperlyInfiniteColumns
import OAI.Analysis.BoundedHochschild.TypeICentralPieces

namespace OAI

/-! Corner transport and finiteness obstructions for properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def partialIsoFromCorner {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) : PartialIso M :=
  ⟨((v : Corner p hp) : M), congrArg Subtype.val v.mul_star_mul⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_initial {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).initial = ((v.initial : Corner p hp) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma partialIsoFromCorner_final {p : M} (hp : IsStarProjection p)
    (v : PartialIso (Corner p hp)) :
    (partialIsoFromCorner hp v).final = ((v.final : Corner p hp) : M) := rfl

omit [StarOrderedRing M] in
lemma properlyInfinite_from_corner {p : M} (hp : IsStarProjection p)
    {q : Corner p hp} (h : ProperlyInfiniteProjection q) : ProperlyInfiniteProjection (q : M) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  exact ⟨partialIsoFromCorner hp v, partialIsoFromCorner hp w,
    congrArg Subtype.val hvi, congrArg Subtype.val hwi,
    hvf, hwf, congrArg Subtype.val ho⟩

lemma properlyInfinite_finite_eq_zero {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfinite : FiniteCorner p) : p = 0 := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  have hv : v.final = p := hfinite (v : M) (partialIso_left_support hp v hvf)
    (partialIso_right_support hp v (hvi ▸ le_rfl)) hvi
  have hw : w.final = p := hfinite (w : M) (partialIso_left_support hp w hwf)
    (partialIso_right_support hp w (hwi ▸ le_rfl)) hwi
  rw [hv, hw, hp.isIdempotentElem.eq] at ho
  exact ho

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteAlgebra_of_equiv {N : Type*} [CStarAlgebra N]
    (φ : M ≃⋆ₐ[ℂ] N) (h : FiniteAlgebra N) : FiniteAlgebra M := by
  intro a ha
  apply φ.injective
  change φ (a * star a) = φ 1
  rw [map_mul, map_star, map_one]
  exact h (φ a) (by rw [← map_star, ← map_mul, ha, map_one])

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_equivalent (v : PartialIso M) (h : FiniteCorner v.final) :
    FiniteCorner v.initial := by
  apply (finiteCorner_iff v.initial v.initial_proj).mpr
  exact finiteAlgebra_of_equiv (partialIsoCornerEquiv v)
    ((finiteCorner_iff v.final v.final_proj).mp h)

lemma properlyInfinite_central_cut {p z : M} (hp : IsStarProjection p)
    (hz : CentralProjection z) (h : ProperlyInfiniteProjection p) :
    ProperlyInfiniteProjection (z * p) := by
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := h
  let v' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) v
  let w' := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) w
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hvle : v'.final ≤ z * p := by
    apply (v'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (v.final_proj.le_iff_mul_eq_left hp).mp hvf]
  have hwle : w'.final ≤ z * p := by
    apply (w'.final_proj.le_iff_mul_eq_left hzp).mpr
    rw [centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq),
      (w.final_proj.le_iff_mul_eq_left hp).mp hwf]
  refine ⟨v', w', ?_, ?_, hvle, hwle, ?_⟩
  · rw [centralCutPartialIso_initial, hvi]
  · rw [centralCutPartialIso_initial, hwi]
  · rw [centralCutPartialIso_final, centralCutPartialIso_final,
      central_idempotent_mul z hz.1.isIdempotentElem.eq (fun a => (hz.2 a).eq), ho, mul_zero]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every infinite corner contains a nonzero properly infinite projection. -/
theorem exists_properlyInfinite_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (h : ¬ FiniteCorner p) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  have hn : ¬ FiniteAlgebra (Corner p hp) := fun hfin => h ((finiteCorner_iff p hp).mpr hfin)
  simp only [FiniteAlgebra, not_forall] at hn
  obtain ⟨v, hvi, hvf⟩ := hn
  obtain ⟨q, hq, hq0, hproper⟩ := nonunitary_isometry_has_properlyInfinite_projection
    (cornerPredualEquiv p hp e) hvi hvf
  exact ⟨(q : M), corner_projection_coe p hp hq, corner_projection_le p hp hq,
    fun hz => hq0 (Subtype.ext hz), properlyInfinite_from_corner hp hproper⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
