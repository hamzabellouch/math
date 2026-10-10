import Mathlib

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.LaurentLattices
noncomputable section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance laurent_finiteType : Algebra.FiniteType K K[T;T⁻¹] := by
  let : IsScalarTower K K[X] K[T;T⁻¹] := IsScalarTower.of_algebraMap_eq (fun c => by
    simp only [Polynomial.algebraMap_eq, algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      ← LaurentPolynomial.C_eq_algebraMap])
  let : Algebra.FinitePresentation K[X] K[T;T⁻¹] :=
    IsLocalization.Away.finitePresentation (Polynomial.X : K[X])
  let : Algebra.FiniteType K[X] K[T;T⁻¹] := inferInstance
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X]) inferInstance

lemma quotient_finite (a : K[T;T⁻¹]) (ha : a ≠ 0) :
    Module.Finite K (K[T;T⁻¹] ⧸ Ideal.span {a}) := by
  let : IsPrincipalIdealRing K[T;T⁻¹] := ⟨fun ideal => by
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X])) K[T;T⁻¹] ideal]
    exact (IsPrincipalIdealRing.principal (ideal.under K[X])).map_ringHom _⟩
  have hlen := isFiniteLength_quotient_span_singleton K[T;T⁻¹]
    (mem_nonZeroDivisors_of_ne_zero ha)
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  let : IsArtinianRing (K[T;T⁻¹] ⧸ Ideal.span {a}) :=
    isArtinian_of_tower K[T;T⁻¹] inferInstance
  exact Module.finite_of_isArtinianRing K _

theorem torsion_finite {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M] [Module.Finite K[T;T⁻¹] M]
    (hM : Module.IsTorsion K[T;T⁻¹] M) : Module.Finite K M := by
  obtain ⟨a,ha,hn⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBy K[T;T⁻¹] M a := fun x =>
    Submodule.mem_annihilator.mp ha x trivial
  let hset : Module.IsTorsionBySet K[T;T⁻¹] M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let := hset.module
  let : IsScalarTower K[T;T⁻¹] (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : IsScalarTower K (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : Module.Finite (K[T;T⁻¹] ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite K[T;T⁻¹] _ M
  let := quotient_finite a (nonZeroDivisors.ne_zero hn)
  exact Module.Finite.trans (K[T;T⁻¹] ⧸ Ideal.span {a}) M
end
end MaximalSeshadri.LaurentLattices
end


end
end

end OAI
