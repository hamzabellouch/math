import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.Derivations

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

lemma finite_self_tensor_dimension_one {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Module.Finite K L] [IsDomain (L ⊗[K] L)] :
    Module.finrank K L = 1 := by
  let : Field (L ⊗[K] L) :=
    (isField_of_isIntegral_of_isField' (R := L) (S := L ⊗[K] L) (Field.toIsField L)).toField
  let μ : L ⊗[K] L →ₐ[L] L := Algebra.TensorProduct.lmul'' K
  have hi : Function.Injective μ := μ.injective
  have hs : Function.Surjective μ := by
    intro x
    exact ⟨x ⊗ₜ[K] 1, by simp [μ, Algebra.TensorProduct.lmul'',
      Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply]⟩
  let e := LinearEquiv.ofBijective μ.toLinearMap ⟨hi, hs⟩
  have he := e.finrank_eq
  simpa only [Module.finrank_baseChange, Module.finrank_self] using he

theorem relative_algebraic_closure_of_self_tensor_domain
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsDomain (F ⊗[K] F)]
    (x : F) (hx : IsAlgebraic K x) : ∃ c : K, algebraMap K F c = x := by
  let L := IntermediateField.adjoin K ({x} : Set F)
  let : Module.Finite K L := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  let ι : L →ₐ[K] F := L.val
  let ψ : L ⊗[K] L →ₐ[K] F ⊗[K] F := Algebra.TensorProduct.map ι ι
  have hi : Function.Injective ψ := by
    exact TensorProduct.map_injective_of_flat_flat ι.toLinearMap ι.toLinearMap
      ι.injective ι.injective
  let : IsDomain (L ⊗[K] L) := hi.isDomain ψ.toRingHom
  have hd : Module.finrank K L = 1 := finite_self_tensor_dimension_one
  let y : L := ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_singleton x)⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd (one_ne_zero : (1 : L) ≠ 0) y
  refine ⟨c, ?_⟩
  have h := congrArg (fun z : L => (z : F)) hc
  simpa [Algebra.smul_def, y] using h

lemma monic_factor_descends {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hclosed : ∀ x : F, IsAlgebraic K x → ∃ c : K, algebraMap K F c = x)
    (p : K[X]) (q : F[X]) (hp : p.Monic) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap K F)) :
    ∃ q₀ : K[X], q₀.map (algebraMap K F) = q := by
  apply (Polynomial.mem_lifts q).mp
  apply (Polynomial.lifts_iff_coeff_lifts q).mpr
  intro n
  exact hclosed (q.coeff n) (Polynomial.isIntegral_coeff_of_dvd p q hp hq hd n).isAlgebraic

theorem irreducible_map_of_relative_closure {K F : Type*} [Field K] [Field F]
    [Algebra K F]
    (hclosed : ∀ x : F, IsAlgebraic K x → ∃ c : K, algebraMap K F c = x)
    (p : K[X]) (hp : p.Monic) (hi : Irreducible p) :
    Irreducible (p.map (algebraMap K F)) := by
  apply ((hp.map (algebraMap K F)).irreducible_iff_natDegree).mpr
  have hinj := Polynomial.map_injective (algebraMap K F) (algebraMap K F).injective
  refine ⟨?_, ?_⟩
  · intro he
    apply hi.ne_one
    apply hinj
    simpa using he
  · intro f g hf hg hfg
    obtain ⟨f₀, rfl⟩ := monic_factor_descends hclosed p f hp hf ⟨g, hfg.symm⟩
    obtain ⟨g₀, rfl⟩ := monic_factor_descends hclosed p g hp hg
      ⟨f₀.map (algebraMap K F), by rw [mul_comm]; exact hfg.symm⟩
    have he : f₀ * g₀ = p := hinj (by simpa using hfg)
    obtain hfu | hgu := hi.isUnit_or_isUnit he.symm
    · left
      exact natDegree_eq_zero_of_isUnit (hfu.map (Polynomial.mapRingHom (algebraMap K F)))
    · right
      exact natDegree_eq_zero_of_isUnit (hgu.map (Polynomial.mapRingHom (algebraMap K F)))

def rootBaseChangeEquiv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (p : K[X]) : F ⊗[K] AdjoinRoot p ≃ₐ[F] AdjoinRoot (p.map (algebraMap K F)) := by
  let p' : (F ⊗[K] K)[X] := p.map Algebra.TensorProduct.includeRight.toRingHom
  refine (AdjoinRoot.tensorAlgEquiv p p' rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid K F F) p'
      (p.map (algebraMap K F)) ?_)
  apply Associated.of_eq
  dsimp [p']
  rw [Polynomial.map_map]
  congr 1
  ext x
  simp [Algebra.smul_def]

theorem finite_separable_tensor_isDomain {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K E
  let p := minpoly K pb.gen
  have hp : p.Monic := minpoly.monic pb.isIntegral_gen
  have hi : Irreducible p := minpoly.irreducible pb.isIntegral_gen
  have hm : Irreducible (p.map (algebraMap K F)) :=
    irreducible_map_of_relative_closure
      relative_algebraic_closure_of_self_tensor_domain p hp hi
  let : IsDomain (AdjoinRoot (p.map (algebraMap K F))) :=
    AdjoinRoot.isDomain_of_prime hm.prime
  let e : AdjoinRoot p ≃ₐ[K] E := AdjoinRoot.equiv' p pb
    (by simp [p, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
      ) (minpoly.aeval K pb.gen)
  let e' : F ⊗[K] E ≃ₐ[F] AdjoinRoot (p.map (algebraMap K F)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e.symm).trans (rootBaseChangeEquiv p)
  exact e'.injective.isDomain e'.toRingHom

lemma tensor_sum_in_intermediate_range {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (L : IntermediateField K E) (s : Finset (F × E))
    (hs : ∀ q ∈ s, q.2 ∈ L) :
    (∑ q ∈ s, q.1 ⊗ₜ[K] q.2) ∈
      (Algebra.TensorProduct.map (AlgHom.id K F) L.val).range := by
  apply Subalgebra.sum_mem
  intro q hq
  exact ⟨q.1 ⊗ₜ[K] (⟨q.2, hs q hq⟩ : L), rfl⟩

theorem separable_tensor_isDomain {K F E : Type*}
    [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    [Algebra.IsSeparable K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  classical
  let : Nontrivial (F ⊗[K] E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K F E
      (algebraMap K F).injective (algebraMap K E).injective
  let : NoZeroDivisors (F ⊗[K] E) := ⟨fun {x y} hxy => by
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨t, hy⟩ := TensorProduct.exists_finset y
    let u : Finset E := (s ∪ t).image Prod.snd
    let L := IntermediateField.adjoin K (u : Set E)
    let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin
      (fun z _ => Algebra.IsSeparable.isIntegral K z)
    let : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K E L.val
    let : IsDomain (F ⊗[K] L) := finite_separable_tensor_isDomain
    let ψ : F ⊗[K] L →ₐ[K] F ⊗[K] E :=
      Algebra.TensorProduct.map (AlgHom.id K F) L.val
    have hi : Function.Injective ψ :=
      TensorProduct.map_injective_of_flat_flat (AlgHom.id K F).toLinearMap
        L.val.toLinearMap Function.injective_id L.val.injective
    have hs : ∀ q ∈ s, q.2 ∈ L := by
      intro q hq
      apply IntermediateField.subset_adjoin
      exact Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hq, rfl⟩
    have ht : ∀ q ∈ t, q.2 ∈ L := by
      intro q hq
      apply IntermediateField.subset_adjoin
      exact Finset.mem_image.mpr ⟨q, Finset.mem_union_right _ hq, rfl⟩
    obtain ⟨x', hx'⟩ := hx.symm ▸ tensor_sum_in_intermediate_range L s hs
    obtain ⟨y', hy'⟩ := hy.symm ▸ tensor_sum_in_intermediate_range L t ht
    change ψ x' = x at hx'
    change ψ y' = y at hy'
    have hzero : x' * y' = 0 := hi (by simpa only [map_mul, map_zero, hx', hy'] using hxy)
    obtain hxz | hyz := mul_eq_zero.mp hzero
    · left
      rw [← hx', hxz, map_zero]
    · right
      rw [← hy', hyz, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem tensorProduct_isDomain_general {K A B : Type}
    [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra K A] [Algebra K B] : IsDomain (A ⊗[K] B) := by
  classical
  let : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective
  let : NoZeroDivisors (A ⊗[K] B) := ⟨fun {x y} hxy => by
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨t, hy⟩ := TensorProduct.exists_finset y
    let u : Finset A := (s ∪ t).image Prod.fst
    let C := Algebra.adjoin K (u : Set A)
    let : Algebra.FiniteType K C := Algebra.FiniteType.adjoin_of_finite u.finite_toSet
    let : IsDomain (C ⊗[K] B) := MaximalSeshadri.tensorProduct_isDomain
    let ψ : C ⊗[K] B →ₐ[K] A ⊗[K] B :=
      Algebra.TensorProduct.map C.val (AlgHom.id K B)
    have hi : Function.Injective ψ :=
      TensorProduct.map_injective_of_flat_flat C.val.toLinearMap
        (AlgHom.id K B).toLinearMap Subtype.val_injective Function.injective_id
    have hr (v : Finset (A × B)) (hv : v ⊆ s ∪ t) :
        (∑ q ∈ v, q.1 ⊗ₜ[K] q.2) ∈ ψ.range := by
      apply Subalgebra.sum_mem
      intro q hq
      have hqc : q.1 ∈ C := Algebra.subset_adjoin
        (Finset.mem_image.mpr ⟨q, hv hq, rfl⟩)
      exact ⟨(⟨q.1, hqc⟩ : C) ⊗ₜ[K] q.2, rfl⟩
    obtain ⟨x', hx'⟩ := hx.symm ▸ hr s Finset.subset_union_left
    obtain ⟨y', hy'⟩ := hy.symm ▸ hr t Finset.subset_union_right
    change ψ x' = x at hx'
    change ψ y' = y at hy'
    have hz : x' * y' = 0 := hi (by simpa only [map_mul, map_zero, hx', hy'] using hxy)
    obtain hxz | hyz := mul_eq_zero.mp hz
    · left
      rw [← hx', hxz, map_zero]
    · right
      rw [← hy', hyz, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

theorem self_tensor_domain_geometrically_domain {K F E : Type}
    [Field K] [CharZero K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [IsDomain (F ⊗[K] F)] :
    IsDomain (F ⊗[K] E) := by
  let Ω := AlgebraicClosure K
  let M := AlgebraicClosure E
  let ι : Ω →ₐ[K] M := IsAlgClosed.lift
  let : Algebra Ω M := ι.toRingHom.toAlgebra
  let : IsScalarTower K Ω M := IsScalarTower.of_algebraMap_eq fun z => (ι.commutes z).symm
  let : IsDomain (F ⊗[K] Ω) := separable_tensor_isDomain
  let e₁ := Algebra.TensorProduct.comm K Ω F
  let : IsDomain (Ω ⊗[K] F) := e₁.injective.isDomain e₁.toRingHom
  let : IsDomain (M ⊗[Ω] (Ω ⊗[K] F)) := tensorProduct_isDomain_general
  let e₂ := Algebra.TensorProduct.cancelBaseChange K Ω Ω M F
  let : IsDomain (M ⊗[K] F) := e₂.symm.injective.isDomain e₂.symm.toRingHom
  let e₃ := Algebra.TensorProduct.comm K F M
  let : IsDomain (F ⊗[K] M) := e₃.injective.isDomain e₃.toRingHom
  let η : E →ₐ[K] M := IsScalarTower.toAlgHom K E M
  let ψ : F ⊗[K] E →ₐ[K] F ⊗[K] M :=
    Algebra.TensorProduct.map (AlgHom.id K F) η
  have hi : Function.Injective ψ :=
    TensorProduct.map_injective_of_flat_flat (AlgHom.id K F).toLinearMap
      η.toLinearMap Function.injective_id η.injective
  exact hi.isDomain ψ.toRingHom

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem tensor_localization_isDomain {K A C B : Type}
    [Field K] [CommRing A] [IsDomain A] [CommRing C] [Nontrivial C]
    [CommRing B] [Algebra K A] [Algebra K C] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B]
    (M : Submonoid A) [IsLocalization M B]
    (hM : M ≤ nonZeroDivisors A) [IsDomain (A ⊗[K] C)] :
    IsDomain (B ⊗[K] C) := by
  let f : A ⊗[K] C →ₐ[K] B ⊗[K] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A B) (AlgHom.id K C)
  let : Algebra (A ⊗[K] C) (B ⊗[K] C) := f.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[K] C) (B ⊗[K] C) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change (algebraMap A B a) ⊗ₜ[K] (1 : C) = f (a ⊗ₜ[K] 1)
      simp [f]
  let : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[K] C) M) (B ⊗[K] C) :=
    IsLocalization.tensorProduct_tensorProduct K C M B (by
      ext c
      change f (1 ⊗ₜ[K] c) = 1 ⊗ₜ[K] c
      simp [f])
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M :=
    Algebra.algebraMapSubmonoid (A ⊗[K] C) M)
  rintro z ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  have hi : Function.Injective (Algebra.TensorProduct.includeLeft :
      A →ₐ[K] A ⊗[K] C) :=
    Algebra.TensorProduct.includeLeft_injective (algebraMap K C).injective
  exact fun hz => (mem_nonZeroDivisors_iff_ne_zero.mp (hM ha)) (hi (by
    simpa using hz))

theorem fraction_self_tensor_isDomain {K A : Type}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [IsDomain (A ⊗[K] A)] :
    IsDomain (FractionRing A ⊗[K] FractionRing A) := by
  let F := FractionRing A
  let : IsDomain (F ⊗[K] A) :=
    tensor_localization_isDomain (nonZeroDivisors A) le_rfl
  let e := Algebra.TensorProduct.comm K A F
  let : IsDomain (A ⊗[K] F) := e.injective.isDomain e.toRingHom
  exact tensor_localization_isDomain (nonZeroDivisors A) le_rfl

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem self_tensor_domain_geometrically_domain_algebra {K A E : Type}
    [Field K] [CharZero K]
    [CommRing A] [IsDomain A] [Field E] [Algebra K A] [Algebra K E]
    [IsDomain (A ⊗[K] A)] : IsDomain (A ⊗[K] E) := by
  let F := FractionRing A
  let : IsDomain (F ⊗[K] F) := fraction_self_tensor_isDomain
  let : IsDomain (F ⊗[K] E) := self_tensor_domain_geometrically_domain
  let ι : A →ₐ[K] F := IsScalarTower.toAlgHom K A F
  let ψ : A ⊗[K] E →ₐ[K] F ⊗[K] E :=
    Algebra.TensorProduct.map ι (AlgHom.id K E)
  have hi : Function.Injective ψ :=
    TensorProduct.map_injective_of_flat_flat ι.toLinearMap (AlgHom.id K E).toLinearMap
      (IsFractionRing.injective A F) Function.injective_id
  exact hi.isDomain ψ.toRingHom

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
