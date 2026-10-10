import OAI.NumberTheory.DukePrimeDegree.Dynamics.RationalCentralizer

namespace OAI

/-!
# Centralizers of actual lattice stabilizers

The matrix centralizer of an arbitrary family of rational matrices is
spanned over `ℝ` by its rational matrices. Finite dimensionality reduces
the family to a basis of its rational span. This applies, in particular,
to the integral stabilizer of a homogeneous orbit in the lattice space.
The identification of that centralizer with the real block algebra is
kept separate from this rational linear algebra statement.
-/

noncomputable section
open Matrix Module Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

private lemma commute_cast_of_mem_span
    (B : κ → Matrix ι ι ℚ) (M : Matrix ι ι ℝ)
    (hM : ∀ k, Commute M (rationalMatrixCast (B k)))
    {v : Matrix ι ι ℚ} (hv : v ∈ Submodule.span ℚ (Set.range B)) :
    Commute M (rationalMatrixCast v) := by
  let P : Submodule ℚ (Matrix ι ι ℚ) :=
    (Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ))).toSubmodule.comap rationalMatrixCast
  have hP : Submodule.span ℚ (Set.range B) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change rationalMatrixCast (B k) ∈ Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ))
    rw [Subalgebra.mem_centralizer_iff]
    intro X hX
    have he : X = M := Set.mem_singleton_iff.mp hX
    simpa only [he] using (hM k).eq
  have H := hP hv
  change rationalMatrixCast v ∈ Subalgebra.centralizer ℚ ({M} : Set (Matrix ι ι ℝ)) at H
  exact (Subalgebra.mem_centralizer_iff ℚ).mp H M (by simp)

lemma commute_rationalMatrixCast_iff (M N : Matrix ι ι ℚ) :
    Commute (rationalMatrixCast M) (rationalMatrixCast N) ↔ Commute M N := by
  change Commute ((Algebra.ofId ℚ ℝ).mapMatrix M) ((Algebra.ofId ℚ ℝ).mapMatrix N) ↔ _
  apply commute_map_iff
  exact Matrix.map_injective (FaithfulSMul.algebraMap_injective ℚ ℝ)

/-- No finiteness assumption on the matrix family is needed: only its
linear span matters, and that span has finite dimension. -/
theorem real_commutant_eq_span_rational_family (B : κ → Matrix ι ι ℚ) :
    (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      Submodule.span ℝ
        (rationalMatrixCast '' ((commutatorFamily B).ker : Set (Matrix ι ι ℚ))) := by
  let S := Submodule.span ℚ (Set.range B)
  let b := Module.finBasis ℚ S
  let C : Fin (Module.finrank ℚ S) → Matrix ι ι ℚ := fun i => (b i).val
  have hS : Submodule.span ℚ (Set.range C) = S := by
    have h := congrArg (Submodule.map S.subtype) b.span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top,
      Function.comp_def, Submodule.subtype_apply, C] using h
  have hreal : (commutatorFamily (fun k => rationalMatrixCast (B k))).ker =
      (commutatorFamily (fun i => rationalMatrixCast (C i))).ker := by
    ext M
    rw [mem_commutatorFamily_ker, mem_commutatorFamily_ker]
    constructor
    · intro h i
      exact commute_cast_of_mem_span B M h (b i).property
    · intro h k
      apply commute_cast_of_mem_span C M h
      rw [hS]
      exact Submodule.subset_span ⟨k, rfl⟩
  have hrat : (commutatorFamily B).ker = (commutatorFamily C).ker := by
    ext M
    have H : rationalMatrixCast M ∈ (commutatorFamily (fun k => rationalMatrixCast (B k))).ker ↔
        rationalMatrixCast M ∈ (commutatorFamily (fun i => rationalMatrixCast (C i))).ker := by
      rw [hreal]
    simpa only [mem_commutatorFamily_ker, commute_rationalMatrixCast_iff] using H
  rw [hreal, real_commutant_eq_span_rational, ← hrat]

/-- Integral elements whose conjugates lie in the given actual orbit
group. These are precisely its lattice stabilizer in matrix coordinates. -/
def latticeOrbitStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  H.comap ((MulAut.conj g⁻¹).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

/-- These conjugated integral elements fix the actual lattice point. -/
theorem latticeOrbitStabilizer_fixes {n : ℕ} (g : G n) (H : Subgroup (G n))
    (γ : latticeOrbitStabilizer g H) :
    rightAction (Quotient.mk _ g)
      ((MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val)) =
        (Quotient.mk _ g : X n) := by
  change Quotient.mk _ (g * (MulAut.conj g⁻¹)
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val)) = Quotient.mk _ g
  apply Quotient.sound
  change QuotientGroup.rightRel (integralGroup n) _ _
  rw [QuotientGroup.rightRel_apply]
  have hi : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val ∈ integralGroup n :=
    ⟨γ.val, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using (integralGroup n).inv_mem hi

/-- Conversely, every element of the orbit group fixing this lattice
point comes from its integral stabilizer. -/
theorem exists_latticeOrbitStabilizer_of_fixed {n : ℕ}
    (g : G n) (H : Subgroup (G n)) (h : G n) (hh : h ∈ H)
    (hfix : rightAction (Quotient.mk _ g) h = (Quotient.mk _ g : X n)) :
    ∃ γ : latticeOrbitStabilizer g H,
      (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.val) = h := by
  change Quotient.mk _ (g * h) = Quotient.mk _ g at hfix
  have hrel := Quotient.exact hfix
  change QuotientGroup.rightRel (integralGroup n) (g * h) g at hrel
  rw [QuotientGroup.rightRel_apply] at hrel
  have hrel' := (integralGroup n).inv_mem hrel
  obtain ⟨γ, hγ⟩ := hrel'
  have hconj : (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) = h := by
    rw [hγ]
    simp [mul_assoc]
  refine ⟨⟨γ, ?_⟩, hconj⟩
  change (MulAut.conj g⁻¹) (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) ∈ H
  rw [hconj]
  exact hh

/-- The rational matrices of the actual integral orbit stabilizer. -/
def latticeStabilizerMatrix {n : ℕ} (g : G n) (H : Subgroup (G n))
    (γ : latticeOrbitStabilizer g H) : Matrix (Fin n) (Fin n) ℚ :=
  γ.val.val.map (Int.castRingHom ℚ)

/-- The centralizer of an actual homogeneous-orbit stabilizer is
rational. The orbit group is arbitrary; no density or homogeneity
classification is built into this statement. -/
theorem latticeStabilizer_commutant_rational {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    (commutatorFamily (fun γ => rationalMatrixCast (latticeStabilizerMatrix g H γ))).ker =
      Submodule.span ℝ (rationalMatrixCast ''
        ((commutatorFamily (latticeStabilizerMatrix g H)).ker :
          Set (Matrix (Fin n) (Fin n) ℚ))) :=
  real_commutant_eq_span_rational_family (latticeStabilizerMatrix g H)

end DukePrimeDegree

end

end OAI
