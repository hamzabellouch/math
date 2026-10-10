import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SheafExactness
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentLattices
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentTorsion

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

theorem intersection_finite_general [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let D := Submodule.torsion K[T;T⁻¹] M
  let q := D.mkQ.restrictScalars K
  let : Module.Finite K D := torsion_finite Submodule.torsion_isTorsion
  have ha : A.map q ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • q (s j.1))) := by
    apply (Submodule.map_mono hA).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  have hb : B.map q ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • q (t j.1))) := by
    apply (Submodule.map_mono hB).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  let := intersection_finite (A.map q) (B.map q) (fun i => q (s i))
    (fun i => q (t i)) ha hb
  let f : ↥(A ⊓ B) →ₗ[K] ↥(A.map q ⊓ B.map q) :=
    (q.comp (A ⊓ B).subtype).codRestrict _ (fun x =>
      ⟨Submodule.mem_map.mpr ⟨x.val,x.property.1,rfl⟩,
        Submodule.mem_map.mpr ⟨x.val,x.property.2,rfl⟩⟩)
  let g : f.ker →ₗ[K] D :=
    (((A ⊓ B).subtype.comp f.ker.subtype).codRestrict (D.restrictScalars K)
      (fun x => by
        have h : q x.val.val = 0 := congrArg Subtype.val x.property
        exact (Submodule.Quotient.mk_eq_zero D).mp h))
  let : Module.Finite K f.ker := Module.Finite.of_injective g (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D => (z : M)) h)
  let : Module.Finite K (↥(A ⊓ B) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
