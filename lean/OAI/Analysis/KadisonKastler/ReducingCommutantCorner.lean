import OAI.Analysis.KadisonKastler.FactorProjectionSeparatesCommutant
import OAI.Analysis.KadisonKastler.NormalEquivOnto
import OAI.Analysis.KadisonKastler.CornerFactorStructure

namespace OAI

/-! # The commutant on a reducing subspace is the represented corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

omit [CompleteSpace H] in
/-- An operator commuting with the subspace projection preserves the subspace. -/
theorem invariant_of_commutes_starProjection (T : H →L[ℂ] H)
    (hT : E.starProjection * T = T * E.starProjection) :
    ∀ x ∈ E, T x ∈ E := by
  intro x hx
  apply Submodule.starProjection_eq_self_iff.mp
  have hh := congrArg (fun A : H →L[ℂ] H => A x) hT
  change E.starProjection (T x) = T (E.starProjection x) at hh
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at hh
  exact hh

omit [CompleteSpace H] in
theorem cornerExtension_mul_reducing (S : E →L[ℂ] E) (T : H →L[ℂ] H)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (S * cornerCompression E T) = cornerExtension E S * T := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    cornerExtension E S * (E.starProjection * T * E.starProjection) =
        cornerExtension E S * T * E.starProjection := by
      rw [← mul_assoc, ← mul_assoc, cornerExtension_mul_starProjection]
    _ = cornerExtension E S * (E.starProjection * T) := by rw [mul_assoc, hT]
    _ = cornerExtension E S * T := by rw [← mul_assoc, cornerExtension_mul_starProjection]

omit [CompleteSpace H] in
theorem reducing_mul_cornerExtension (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    cornerExtension E (cornerCompression E T * S) = T * cornerExtension E S := by
  rw [cornerExtension_mul, cornerExtension_compression]
  calc
    E.starProjection * T * E.starProjection * cornerExtension E S =
        E.starProjection * T * cornerExtension E S := by
      rw [mul_assoc (E.starProjection * T), starProjection_mul_cornerExtension]
    _ = T * E.starProjection * cornerExtension E S := by rw [hT]
    _ = T * cornerExtension E S := by rw [mul_assoc, starProjection_mul_cornerExtension]

omit [CompleteSpace H] in
theorem commutes_corner_iff (T : H →L[ℂ] H) (S : E →L[ℂ] E)
    (hT : E.starProjection * T = T * E.starProjection) :
    Commute (cornerCompression E T) S ↔ Commute T (cornerExtension E S) := by
  constructor
  · intro h
    have hh := congrArg (cornerExtension E) h.eq
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT] at hh
    exact hh
  · intro h
    apply cornerExtension_injective
    rw [reducing_mul_cornerExtension E T S hT, cornerExtension_mul_reducing E S T hT]
    exact h.eq

/-- Restrict the original algebra to a subspace reduced by it. -/
def commutantReducingHom (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) :
    Algebra M →⋆ₐ[ℂ] (E →L[ℂ] E) :=
  reducingRestriction E M.toStarSubalgebra (fun a =>
    invariant_of_commutes_starProjection E a.val
      (VonNeumannAlgebra.mem_commutant_iff.mp hE a.val a.property).symm)

theorem commutantReducingHom_apply (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) (a : Algebra M) :
    commutantReducingHom E M hE a = cornerCompression E a.val := rfl

/-- The full commutant of the restricted algebra is exactly the corner
of the original commutant, with extension by zero identifying operators. -/
theorem commutant_reducingClosure (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) :
    (generatedVonNeumannAlgebra (commutantReducingHom E M hE).range).commutant =
      representedCorner E M.commutant hE := by
  apply VonNeumannAlgebra.ext
  intro S
  rw [mem_representedCorner]
  constructor
  · intro hS
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hS
      (commutantReducingHom E M hE ⟨a, ha⟩)
      (subset_generatedVonNeumannAlgebra _ ⟨⟨a, ha⟩, rfl⟩)
    exact (commutes_corner_iff E a S
      (VonNeumannAlgebra.mem_commutant_iff.mp hE a ha).symm).mp hc
  · intro hS
    have hs : S ∈ Set.centralizer
        (Set.range (fun b : Algebra M => commutantReducingHom E M hE b)) := by
      rintro a ⟨b, rfl⟩
      exact ((commutes_corner_iff E b.val S
        (VonNeumannAlgebra.mem_commutant_iff.mp hE b.val b.property).symm).mpr
          (VonNeumannAlgebra.mem_commutant_iff.mp hS b.val b.property)).eq
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    change a ∈ (generatedVonNeumannAlgebra
      (commutantReducingHom E M hE).range : Set (E →L[ℂ] E)) at ha
    rw [generatedVonNeumannAlgebra_coe] at ha
    exact (ha S hs).symm

/-- Full central support of the reducing projection makes restriction faithful. -/
theorem commutantReducingHom_injective (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (hN : ScalarCenter M.commutant) :
    Function.Injective (commutantReducingHom E M hE) := by
  intro a b hab
  let x : Algebra M := a - b
  have hx : commutantReducingHom E M hE x = 0 := by
    rw [map_sub, hab, sub_self]
  have hxc : cornerCompression E x.val = 0 := hx
  have he := congrArg (cornerExtension E) hxc
  rw [cornerExtension_compression, map_zero] at he
  have hp := isStarProjection_starProjection (U := E)
  have hc : E.starProjection * x.val = x.val * E.starProjection :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hE x.val x.property).symm
  have hxp : x.val * E.starProjection = 0 := by
    rw [hc, mul_assoc, hp.isIdempotentElem.eq] at he
    exact he
  let p : AlgebraProjection M.commutant :=
    ⟨⟨E.starProjection, hE⟩,
      ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩⟩
  have hp0 : p.val ≠ 0 := fun h => hE0 (congrArg Subtype.val h)
  have hxN : x.val ∈ M.commutant.commutant := by
    rw [VonNeumannAlgebra.commutant_commutant]
    change x.val ∈ M.toSubalgebra
    exact x.property
  have hz := commutant_eq_zero_of_mul_factor_projection M.commutant hN p hp0
    x.val hxN hxp
  exact sub_eq_zero.mp (Subtype.ext hz)

/-- Restriction preserves bounded weak-operator limits coefficientwise. -/
theorem commutantReducingHom_boundedWeakNormal (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M.commutant) :
    BoundedWeakNormal M (commutantReducingHom E M hE) := by
  intro ι l a b C ha hb x y
  have he (c : Algebra M) (z : E) :
      (commutantReducingHom E M hE c z : H) = c.val z :=
    reducingRestriction_coe_apply E M.toStarSubalgebra _ c z
  simpa only [Submodule.coe_inner, ← he] using hb x.val y.val

end

end KadisonKastler

end OAI
