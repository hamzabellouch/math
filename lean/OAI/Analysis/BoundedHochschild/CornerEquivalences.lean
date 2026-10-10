import OAI.Analysis.BoundedHochschild.Conditional

namespace OAI

/-!
# Structural transport for actual corners and algebra equivalences

Nested corners flatten to the corresponding ambient corner. Type I corners
and the absence of a type I central part are invariant under an actual star
algebra equivalence. These facts are algebraic and require no trace.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

section Nested
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A corner within a corner is the corner of its ambient projection. -/
def nestedCornerEquiv {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) :
    Corner q hq ≃⋆ₐ[ℂ] Corner (q : M) (corner_projection_coe p hp hq) where
  toFun a := ⟨((a : Corner p hp) : M),
    congrArg Subtype.val a.property.1, congrArg Subtype.val a.property.2⟩
  invFun b := ⟨⟨(b : M), by
      constructor
      · calc
          p * (b : M) = p * ((q : M) * (b : M)) := by rw [b.property.1]
          _ = (b : M) := by rw [← mul_assoc, q.property.1, b.property.1]
      · calc
          (b : M) * p = ((b : M) * (q : M)) * p := by rw [b.property.2]
          _ = (b : M) := by rw [mul_assoc, q.property.2, b.property.2]⟩,
    Subtype.ext b.property.1, Subtype.ext b.property.2⟩
  left_inv a := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma nestedCornerEquiv_apply {p : M} (hp : IsStarProjection p)
    (q : Corner p hp) (hq : IsStarProjection q) (a : Corner q hq) :
    ((nestedCornerEquiv hp q hq a : Corner (q : M) (corner_projection_coe p hp hq)) : M) =
      ((a : Corner p hp) : M) := rfl

end Nested

section Transport
variable {M N : Type*} [CStarAlgebra M] [CStarAlgebra N]
  [PartialOrder M] [StarOrderedRing M] [PartialOrder N] [StarOrderedRing N]

/-- An algebra equivalence induces an equivalence between corresponding corners. -/
def popaCornerEquiv (φ : M ≃⋆ₐ[ℂ] N) {p : M} (hp : IsStarProjection p) :
    PopaCorner.algebra hp ≃⋆ₐ[ℂ] PopaCorner.algebra (hp.map φ) where
  toFun a := ⟨φ (a : M), by
    constructor
    · change φ p * φ (a : M) = φ (a : M)
      rw [← map_mul, a.property.1]
    · change φ (a : M) * φ p = φ (a : M)
      rw [← map_mul, a.property.2]⟩
  invFun b := ⟨φ.symm (b : N), by
    constructor
    · apply φ.injective
      change φ (p * φ.symm (b : N)) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.1
    · apply φ.injective
      change φ (φ.symm (b : N) * p) = φ (φ.symm (b : N))
      rw [map_mul, φ.apply_symm_apply]
      exact b.property.2⟩
  left_inv a := Subtype.ext (φ.symm_apply_apply (a : M))
  right_inv b := Subtype.ext (φ.apply_symm_apply (b : N))
  map_add' a b := Subtype.ext (map_add φ (a : M) (b : M))
  map_mul' a b := Subtype.ext (map_mul φ (a : M) (b : M))
  map_smul' c a := Subtype.ext (map_smul φ c (a : M))
  map_star' a := Subtype.ext (map_star φ (a : M))

/-- Abelianness of a projection is transported by a star algebra equivalence. -/
lemma abelianProjection_map_equiv (φ : M ≃⋆ₐ[ℂ] N) {p : M}
    (hp : IsStarProjection p) (hab : PopaTypeII.AbelianProjection hp) :
    PopaTypeII.AbelianProjection (hp.map φ) := by
  let E := popaCornerEquiv φ hp
  intro a b
  simpa only [E.apply_symm_apply] using (hab (E.symm a) (E.symm b)).map E

/-- The type I condition is invariant under changing the algebra presentation. -/
lemma typeICorner_map_equiv (φ : M ≃⋆ₐ[ℂ] N) {z : M}
    (hz : IsStarProjection z) (hI : PopaTypeII.TypeICorner hz) :
    PopaTypeII.TypeICorner (hz.map φ) := by
  intro p hp hpz hp0
  have hpp : IsStarProjection (φ.symm p) := hp.map φ.symm
  have hle : φ.symm p ≤ z := by
    simpa only [φ.symm_apply_apply] using OrderHomClass.mono φ.symm hpz
  have hp0' : φ.symm p ≠ 0 := by
    intro hzero
    apply hp0
    simpa only [φ.apply_symm_apply, map_zero] using congrArg φ hzero
  obtain ⟨q, hq, hqp, hq0, hqa⟩ := hI (φ.symm p) hpp hle hp0'
  refine ⟨φ q, hq.map φ, ?_, ?_, abelianProjection_map_equiv φ hq hqa⟩
  · simpa only [φ.apply_symm_apply] using OrderHomClass.mono φ hqp
  · intro hzero
    apply hq0
    simpa only [φ.symm_apply_apply, map_zero] using congrArg φ.symm hzero

/-- Absence of a type I central part needs no trace for transport. -/
theorem noTypeICentralPart_map_equiv (φ : M ≃⋆ₐ[ℂ] N)
    (hM : PopaTypeII.NoTypeICentralPart M) : PopaTypeII.NoTypeICentralPart N := by
  intro z hz hzc hz0 hI
  have hzM : IsStarProjection (φ.symm z) := hz.map φ.symm
  have hzcM : PopaCenter.Central (φ.symm z) := by
    intro a
    apply φ.injective
    change φ (φ.symm z * a) = φ (a * φ.symm z)
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact (hzc (φ a)).eq
  have hz0M : φ.symm z ≠ 0 := by
    intro hzero
    apply hz0
    simpa only [φ.apply_symm_apply, map_zero] using congrArg φ hzero
  exact hM (φ.symm z) hzM hzcM hz0M (typeICorner_map_equiv φ.symm hz hI)

/-- The type I central condition is a property of the star algebra. -/
theorem noTypeICentralPart_equiv (φ : M ≃⋆ₐ[ℂ] N) :
    PopaTypeII.NoTypeICentralPart M ↔ PopaTypeII.NoTypeICentralPart N :=
  ⟨noTypeICentralPart_map_equiv φ, noTypeICentralPart_map_equiv φ.symm⟩

end Transport

end KadisonRingrose
end BoundedHochschild

end

end OAI
