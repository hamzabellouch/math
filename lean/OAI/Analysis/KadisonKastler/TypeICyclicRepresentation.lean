import OAI.Analysis.KadisonKastler.PublishedTypeIInjectivity
import OAI.Analysis.KadisonKastler.ReducingRestriction
import OAI.Analysis.FactorGeneration.Subfactors
import OAI.Analysis.FactorGeneration.FiniteComparison

namespace OAI

/-! # The irreducible cyclic representation afforded by a minimal projection

A nonzero vector in a minimal projection determines a faithful irreducible
cyclic representation of a factor.  The construction uses the actual closed
orbit in the given Hilbert space; no classification theorem is invoked.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

abbrev typeICyclicSpace (M : VonNeumannAlgebra H) (ξ : H) :=
  vectorOrbitClosure M.toStarSubalgebra ξ

def typeICyclicVector (M : VonNeumannAlgebra H) (ξ : H) : typeICyclicSpace M ξ :=
  ⟨ξ, mem_vectorOrbitClosure _ _⟩

def typeICyclicOperator (ξ : H) (a : Algebra M) :
    typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ :=
  a.val.restrict (fun _ hy => vectorOrbitClosure_invariant _ _ a hy)

@[simp] theorem typeICyclicOperator_apply (ξ : H) (a : Algebra M)
    (y : typeICyclicSpace M ξ) : (typeICyclicOperator ξ a y : H) = a.val y := rfl

theorem typeICyclicOperator_star (ξ : H) (a : Algebra M) :
    typeICyclicOperator ξ (star a) = star (typeICyclicOperator ξ a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val (star a.val x.val) =
    inner ℂ y (star (typeICyclicOperator ξ a) x)
  simp only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

def typeICyclicHom (ξ : H) : Algebra M →⋆ₐ[ℂ]
    (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) where
  toFun := typeICyclicOperator ξ
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl
  map_zero' := by ext y; rfl
  map_add' _ _ := by ext y; rfl
  commutes' _ := by ext y; rfl
  map_star' := typeICyclicOperator_star ξ

@[simp] theorem typeICyclicHom_apply (ξ : H) (a : Algebra M)
    (y : typeICyclicSpace M ξ) : (typeICyclicHom ξ a y : H) = a.val y := rfl

theorem typeICyclicHom_cyclic (ξ : H) :
    DenseRange (fun a : Algebra M => typeICyclicHom ξ a (typeICyclicVector M ξ)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  exact ⟨typeICyclicHom ξ a (typeICyclicVector M ξ), ⟨a, rfl⟩, ha⟩

theorem exists_nonzero_fixed_vector (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ ξ : H, ξ ≠ 0 ∧ p.val.val ξ = ξ := by
  have hn : p.val.val ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : H, p.val.val x ≠ 0 := by
    by_contra h
    apply hn
    ext x
    simpa using (not_exists.mp h x)
  refine ⟨p.val.val x, hx, ?_⟩
  exact congrArg (fun a : Algebra M => a.val x) p.property.isIdempotentElem.eq

private theorem minimal_corner_scalar (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (a : Algebra M)
    (hl : p.val * a = a) (hr : a * p.val = a) : ∃ z : ℂ, a = z • p.val := by
  apply corner_scalar_of_projections p _ a hl hr
  intro q hq
  exact (hp.2 q hq).imp id (congrArg Subtype.val)

/-- Evaluation at a nonzero vector in a minimal projection is faithful on
the right ideal supported by that projection. -/
theorem minimal_right_ideal_separating (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) (a : Algebra M) (hap : a * p.val = a)
    (haξ : a.val ξ = 0) : a = 0 := by
  have hpa : p.val * star a = star a := by
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq] using congrArg star hap
  obtain ⟨z, hz⟩ := minimal_corner_scalar p hp (star a * a)
    (by rw [← mul_assoc, hpa]) (by rw [mul_assoc, hap])
  have he : z • ξ = 0 := by
    have he := congrArg (fun b : Algebra M => b.val ξ) hz
    change star a.val (a.val ξ) = z • p.val.val ξ at he
    rw [haξ, map_zero, hpξ] at he
    exact he.symm
  have hz0 : z = 0 := (smul_eq_zero.mp he).resolve_right hξ
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  rw [hz, hz0, zero_smul]

/-- The cyclic restriction of a factor at a minimal projection is faithful. -/
theorem typeICyclicHom_injective (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) : Function.Injective (typeICyclicHom (M := M) ξ) := by
  have hker (a : Algebra M) (ha : typeICyclicHom ξ a = 0) : a = 0 := by
    have hlink (b : Algebra M) : a * b * p.val = 0 := by
      apply minimal_right_ideal_separating p hp ξ hξ hpξ
      · rw [mul_assoc, p.property.isIdempotentElem.eq]
      · have he := congrArg (fun T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
          (T (typeICyclicHom ξ b (typeICyclicVector M ξ)) : H)) ha
        change a.val (b.val ξ) = 0 at he
        change a.val (b.val (p.val.val ξ)) = 0
        rwa [hpξ]
    have hK : projectionOrbitClosure p ≤ a.val.ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro y ⟨b, x, rfl⟩
        exact congrArg (fun c : Algebra M => c.val x) (hlink b)
      · exact a.val.isClosed_ker
    have he : a * (centralSupport p).val = 0 := by
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      exact hK ((projectionOrbitClosure p).starProjection_apply_mem x)
    have hfactor (c : Algebra M) (hc : ∀ b : Algebra M, b * c = c * b) :
        ∃ z : ℂ, c = z • (1 : Algebra M) := by
      obtain ⟨z, hz⟩ := hM c.val c.property (fun b hb =>
        congrArg Subtype.val (hc ⟨b, hb⟩))
      exact ⟨z, Subtype.ext hz⟩
    rwa [centralSupport_eq_one_of_factor hfactor p hp.1, mul_one] at he
  intro a b hab
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hab, sub_self]

theorem typeICyclicHom_norm (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) (a : Algebra M) : ‖typeICyclicHom ξ a‖ = ‖a‖ := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  exact NonUnitalStarAlgHom.norm_map (typeICyclicHom ξ)
    (typeICyclicHom_injective hM p hp ξ hξ hpξ) a

/-- The minimal projection restricts to a rank-one projection. -/
theorem typeICyclicProjection_range (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hpξ : p.val.val ξ = ξ)
    (y : typeICyclicSpace M ξ) :
    ∃ z : ℂ, typeICyclicHom ξ p.val y = z • typeICyclicVector M ξ := by
  let L : Submodule ℂ H := Submodule.span ℂ {ξ}
  have hclosed : IsClosed (L : Set H) := L.closed_of_finiteDimensional
  have hK : typeICyclicSpace M ξ ≤ L.comap p.val.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨a, rfl⟩
      obtain ⟨z, hz⟩ := minimal_corner_scalar p hp (p.val * a * p.val)
        (by rw [← mul_assoc, ← mul_assoc, p.property.isIdempotentElem.eq])
        (by rw [mul_assoc, p.property.isIdempotentElem.eq])
      have he := congrArg (fun b : Algebra M => b.val ξ) hz
      change p.val.val (a.val (p.val.val ξ)) = z • p.val.val ξ at he
      rw [hpξ] at he
      change p.val.val (a.val ξ) ∈ L
      rw [he]
      exact L.smul_mem z (Submodule.subset_span (Set.mem_singleton ξ))
    · exact hclosed.preimage p.val.val.continuous
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp (hK y.property)
  exact ⟨z, Subtype.ext hz.symm⟩

/-- Every operator commuting with this cyclic representation is scalar. -/
theorem typeICyclicHom_commutant (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hpξ : p.val.val ξ = ξ)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)
    (hT : ∀ a : Algebra M, typeICyclicHom ξ a * T = T * typeICyclicHom ξ a) :
    ∃ z : ℂ, T = z • 1 := by
  have hfix : typeICyclicHom ξ p.val (T (typeICyclicVector M ξ)) =
      T (typeICyclicVector M ξ) := by
    have he := congrArg (fun S : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
      S (typeICyclicVector M ξ)) (hT p.val)
    have hpfix : typeICyclicHom ξ p.val (typeICyclicVector M ξ) =
        typeICyclicVector M ξ := Subtype.ext hpξ
    change typeICyclicHom ξ p.val (T (typeICyclicVector M ξ)) =
      T (typeICyclicHom ξ p.val (typeICyclicVector M ξ)) at he
    rwa [hpfix] at he
  obtain ⟨z, hz⟩ := typeICyclicProjection_range p hp ξ hpξ (T (typeICyclicVector M ξ))
  rw [hfix] at hz
  refine ⟨z, ?_⟩
  apply DFunLike.ext'
  apply (typeICyclicHom_cyclic (M := M) ξ).equalizer T.continuous (z • (1 :
    typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ)).continuous
  funext a
  have he := congrArg (fun S : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ =>
    S (typeICyclicVector M ξ)) (hT a)
  change typeICyclicHom ξ a (T (typeICyclicVector M ξ)) =
    T (typeICyclicHom ξ a (typeICyclicVector M ξ)) at he
  change T (typeICyclicHom ξ a (typeICyclicVector M ξ)) =
    z • typeICyclicHom ξ a (typeICyclicVector M ξ)
  rw [← he, hz, map_smul]

end

end KadisonKastler

end OAI
