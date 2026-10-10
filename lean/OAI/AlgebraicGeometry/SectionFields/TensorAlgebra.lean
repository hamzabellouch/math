import Mathlib

namespace OAI

/-! Tensor localizations, Galois invariants and normality of scalar extensions. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section

 

theorem algebraMap_surjective_of_isAlgebraic_tensorSelf_domain
    (K A : Type*) [Field K] [Field A] [Algebra K A]
    [Algebra.IsAlgebraic K A] [IsDomain (A ⊗[K] A)] :
    Function.Surjective (algebraMap K A) := by
  have hfield := Algebra.TensorProduct.isField_of_isAlgebraic K A A
    (Or.inl (inferInstance : Algebra.IsAlgebraic K A))
  have hd := IntermediateField.LinearDisjoint.of_isField' hfield
    (AlgHom.id K A) (AlgHom.id K A)
  have he := hd.eq_bot_of_self
  intro x
  apply IntermediateField.mem_bot.mp
  rw [← he]
  exact ⟨x, rfl⟩

variable (K A L M : Type*) [Field K] [CommRing A] [Field L] [Field M]
  [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]

 
@[instance_reducible] def tensorFractionAlgebra : Algebra (A ⊗[K] L) (M ⊗[K] L) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K L)).toAlgebra

lemma tensorFraction_isLocalization [IsFractionRing A M] :
    letI := tensorFractionAlgebra K A L M
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] L) (nonZeroDivisors A)) (M ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  let : IsScalarTower A (A ⊗[K] L) (M ⊗[K] L) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K L)
        (a ⊗ₜ[K] (1 : L))
      simp
  apply IsLocalization.tensorProduct_tensorProduct K L (nonZeroDivisors A) M
  ext l
  simp [RingHom.algebraMap_toAlgebra]

lemma tensorFraction_domain [IsDomain (A ⊗[K] L)] [IsFractionRing A M] :
    IsDomain (M ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  have : Nontrivial A := (algebraMap A M).domain_nontrivial
  let := tensorFraction_isLocalization K A L M
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M ⊗[K] L)
    (M := Algebra.algebraMapSubmonoid (A ⊗[K] L) (nonZeroDivisors A))
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  apply nonZeroDivisors.ne_zero ha
  apply Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := L)
    (RingHom.injective (algebraMap K L))
  change a ⊗ₜ[K] (1 : L) = (0 : A) ⊗ₜ[K] (1 : L)
  change a ⊗ₜ[K] (1 : L) = 0 at h
  simpa only [TensorProduct.zero_tmul] using h

 

@[instance_reducible] noncomputable def tensorFractionField [IsDomain (A ⊗[K] L)]
    [IsFractionRing A M] [Module.Finite K L] : Field (M ⊗[K] L) := by
  letI := tensorFraction_domain K A L M
  exact fieldOfFiniteDimensional M (M ⊗[K] L)

lemma tensorFraction_isFractionRing [IsDomain (A ⊗[K] L)]
    [IsFractionRing A M] [Module.Finite K L] :
    letI := tensorFractionAlgebra K A L M
    IsFractionRing (A ⊗[K] L) (M ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isLocalization K A L M
  let := tensorFractionField K A L M
  have hinj : Function.Injective (algebraMap (A ⊗[K] L) (M ⊗[K] L)) := by
    apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid (A ⊗[K] L)
      (nonZeroDivisors A))
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    have hn : Nontrivial A := (algebraMap A M).domain_nontrivial
    apply nonZeroDivisors.ne_zero ha
    apply Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := L)
      (RingHom.injective (algebraMap K L))
    change a ⊗ₜ[K] (1 : L) = (0 : A) ⊗ₜ[K] (1 : L)
    change a ⊗ₜ[K] (1 : L) = 0 at h
    simpa only [TensorProduct.zero_tmul] using h
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid (A ⊗[K] L)
    (nonZeroDivisors A)) (nonZeroDivisors (A ⊗[K] L))
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    have hn : Nontrivial A := (algebraMap A M).domain_nontrivial
    apply nonZeroDivisors.ne_zero ha
    apply Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := A) (B := L)
      (RingHom.injective (algebraMap K L))
    change a ⊗ₜ[K] (1 : L) = (0 : A) ⊗ₜ[K] (1 : L)
    change a ⊗ₜ[K] (1 : L) = 0 at h
    simpa only [TensorProduct.zero_tmul] using h
  · intro r hr
    exact isUnit_iff_ne_zero.mpr (fun hz => nonZeroDivisors.ne_zero hr
      (hinj (hz.trans (map_zero _).symm)))

end

 

theorem tensor_invariant_descends
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [IsGalois K L] [Algebra K M]
    (x : L ⊗[K] M)
    (hx : ∀ σ : Gal(L/K),
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) x = x) :
    ∃ m : M, (1 : L) ⊗ₜ[K] m = x := by
  classical
  let b := Module.Free.chooseBasis K M
  let c := b.baseChange L
  have hrepr (σ : Gal(L/K)) (y : L ⊗[K] M) (i) :
      c.repr (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) y) i =
        σ (c.repr y i) := by
    induction y using TensorProduct.inductionOn with
    | tmul l m => simp [c, Algebra.smul_def]
    | add y z hy hz => simp [hy, hz]
  have hcoeff (i) : ∃ a : K, algebraMap K L a = c.repr x i := by
    apply Algebra.IsInvariant.isInvariant (G := Gal(L/K))
    intro σ
    change σ (c.repr x i) = c.repr x i
    rw [← hrepr, hx]
  choose a ha using hcoeff
  refine ⟨∑ i ∈ (c.repr x).support, a i • b i, ?_⟩
  apply c.repr.injective
  ext i
  simp only [c, Module.Basis.baseChange_repr_tmul, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ (c.repr x).support
  · have hi' : ((b.baseChange L).repr x) i ≠ 0 := Finsupp.mem_support_iff.mp hi
    simpa [hi', Algebra.smul_def, c] using ha i
  · have hxi : c.repr x i = 0 := Finsupp.notMem_support_iff.mp hi
    change ((b.baseChange L).repr x) i = 0 at hxi
    simp [hxi]

@[instance_reducible] noncomputable def tensorGaloisAction
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] : MulSemiringAction (Gal(L/K)) (L ⊗[K] M) where
  smul σ x := Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) x
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _
  one_smul x := by
    change Algebra.TensorProduct.map (1 : Gal(L/K)).toAlgHom (AlgHom.id K M) x = x
    induction x using TensorProduct.inductionOn with
    | tmul l m => simp
    | add x y hx hy => simp [hx, hy]
  mul_smul σ τ x := by
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K M) x =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M)
        (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K M) x)
    induction x using TensorProduct.inductionOn with
    | tmul l m => simp
    | add x y hx hy => simp [hx, hy]

 
theorem tensor_invariant_unit_descends
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [IsGalois K L] [Algebra K M]
    (x : (L ⊗[K] M)ˣ)
    (hx : ∀ σ : Gal(L/K),
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K M) (x : L ⊗[K] M) = x) :
    ∃ m : Mˣ, Units.map Algebra.TensorProduct.includeRight.toMonoidHom m = x := by
  obtain ⟨m, hm⟩ := tensor_invariant_descends K L M (x : L ⊗[K] M) hx
  have hm0 : m ≠ 0 := by
    intro hz
    simp only [hz, TensorProduct.tmul_zero] at hm
    exact (Units.ne_zero x) hm.symm
  exact ⟨Units.mk0 m hm0, Units.ext hm⟩

open scoped TensorProduct

 

lemma tensor_galois_coefficient
    (K L M : Type*) [Field K] [Field L] [CommRing M]
    [Algebra K L] [Algebra K M] [IsGalois K L] [Module.Finite K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (i : ι) (x : M ⊗[K] L) :
    (b.baseChange M).repr x i ⊗ₜ[K] (1 : L) =
      ∑ σ : Gal(L/K), Algebra.TensorProduct.map (AlgHom.id K M) σ.toAlgHom
        ((1 : M) ⊗ₜ[K] b.traceDual i * x) := by
  classical
  have hb (l : L) : b.repr l i = Algebra.trace K L (l * b.traceDual i) := by
    simpa only [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply] using
      (b.traceDual.traceDual_repr_apply l i)
  induction x using TensorProduct.inductionOn with
  | tmul m l =>
      simp only [Module.Basis.baseChange_repr_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
      rw [← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms,
        mul_comm (b.traceDual i), ← hb]
      rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, TensorProduct.add_tmul, mul_add, Finset.sum_add_distrib,
        hx, hy]

 
noncomputable def tensorRightGaloisAlgHom
    (K A L M : Type*) [Field K] [CommRing A] [Field L] [CommRing M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    (σ : Gal(L/K)) : (M ⊗[K] L) →ₐ[A] (M ⊗[K] L) where
  __ := (Algebra.TensorProduct.map (AlgHom.id K M) σ.toAlgHom).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.map (AlgHom.id K M) σ.toAlgHom
      (algebraMap A M a ⊗ₜ[K] (1 : L)) = algebraMap A M a ⊗ₜ[K] (1 : L)
    simp

lemma tensorFraction_isScalarTower
    (K A L M : Type*) [Field K] [CommRing A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M] :
    letI := tensorFractionAlgebra K A L M
    IsScalarTower A (A ⊗[K] L) (M ⊗[K] L) := by
  let := tensorFractionAlgebra K A L M
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change _ = Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K L)
    (a ⊗ₜ[K] (1 : L))
  simp

 

theorem tensor_isIntegrallyClosed_of_galois
    (K A L M : Type*) [Field K] [CommRing A] [IsDomain A] [Field L] [Field M]
    [Algebra K A] [Algebra K L] [Algebra K M] [Algebra A M] [IsScalarTower K A M]
    [IsFractionRing A M] [IsIntegrallyClosed A] [IsGalois K L] [Module.Finite K L]
    [IsDomain (A ⊗[K] L)] : IsIntegrallyClosed (A ⊗[K] L) := by
  classical
  let := tensorFractionAlgebra K A L M
  let := tensorFraction_isScalarTower K A L M
  let := tensorFraction_isFractionRing K A L M
  let := tensorFractionField K A L M
  apply (isIntegrallyClosed_iff (M ⊗[K] L)).mpr
  intro x hx
  have hxA : IsIntegral A x := isIntegral_trans x hx
  let b := Module.finBasis K L
  have hint (l : L) : IsIntegral A ((1 : M) ⊗ₜ[K] l) := by
    have h := (Algebra.IsIntegral.isIntegral l : IsIntegral K l).map
      (Algebra.TensorProduct.includeRight : L →ₐ[K] M ⊗[K] L)
    exact h.tower_top
  have hcoeff (i) : ∃ a : A, algebraMap A M a = (b.baseChange M).repr x i := by
    apply IsIntegrallyClosed.isIntegral_iff.mp
    apply (isIntegral_algebraMap_iff (B := M ⊗[K] L)).mp
    change IsIntegral A ((b.baseChange M).repr x i ⊗ₜ[K] (1 : L))
    rw [tensor_galois_coefficient K L M b i x]
    exact IsIntegral.sum _ fun σ _ => (hint (b.traceDual i) |>.mul hxA).map
      (tensorRightGaloisAlgHom K A L M σ)
  choose a ha using hcoeff
  refine ⟨∑ i, a i ⊗ₜ[K] b i, ?_⟩
  rw [map_sum, ← (b.baseChange M).sum_repr x]
  apply Finset.sum_congr rfl
  intro i _
  change Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A M) (AlgHom.id K L)
    (a i ⊗ₜ[K] b i) = _
  simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.toAlgHom_apply,
    AlgHom.id_apply, ha, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

end RelativeDenominators
end

end OAI
