import OAI.NumberTheory.SiegelZeros.Differentials.KoszulTopDifferential
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularSequenceAugmentation

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W30
open Module

variable {R A B C : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

lemma range_comp_eq_of_surjective (f : B →ₗ[R] C) (g : A →ₗ[R] B)
    (hg : Function.Surjective g) : LinearMap.range (f.comp g) = LinearMap.range f := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨g a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

theorem scalar_sub_range (e : A ≃ₗ[R] R) (g : B →ₗ[R] R) (r : R)
    (I : Ideal R) (hg : LinearMap.range g = I) :
    LinearMap.range
      (r • e.toLinearMap.comp (LinearMap.fst R A B) -
        g.comp (LinearMap.snd R A B)) = I ⊔ Ideal.span {r} := by
  let T : (A × B) →ₗ[R] (B × R) :=
    (-(LinearMap.snd R A B)).prod (e.toLinearMap.comp (LinearMap.fst R A B))
  have hT : Function.Surjective T := by
    rintro ⟨b, z⟩
    refine ⟨(e.symm z, -b), ?_⟩
    change (-(-b), e (e.symm z)) = (b, z)
    simp only [neg_neg, e.apply_symm_apply]
  have hmap : r • e.toLinearMap.comp (LinearMap.fst R A B) -
      g.comp (LinearMap.snd R A B) = (coneBottom g r).comp T := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change r • e a - g b = g (-b) + r • e a
    rw [map_neg]
    abel
  rw [hmap, range_comp_eq_of_surjective _ _ hT, coneBottom_range_eq_sup g r I hg]

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (e : P.X (n + 1) ≃ₗ[S] S) (I : Ideal S)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap) =
      I ⊔ Ideal.span {r} := by
  let E := dualProdDualEquivDual S (P.X (n + 1)) (P.X n)
  let F := (W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
    ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap
  have hmap : F.comp E.toLinearMap =
      r • (W31.topDualCoordinate e).toLinearMap.comp
          (LinearMap.fst S (Dual S (P.X (n + 1))) (Dual S (P.X n))) -
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap).comp
          (LinearMap.snd S (Dual S (P.X (n + 1))) (Dual S (P.X n))) := by
    apply LinearMap.ext
    rintro ⟨α, β⟩
    exact W31.scalarConeTopDualCoordinate_boundary P r n hbound e α β
  change LinearMap.range F = _
  rw [← range_comp_eq_of_surjective F E.toLinearMap E.surjective, hmap]
  exact scalar_sub_range (W31.topDualCoordinate e) _ r I hI

end SiegelZerosAwei.W30

end

section

namespace SiegelZerosAwei.W30
open Module

variable {R A B : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

theorem regular_on_dual (r : R) (hr : IsSMulRegular R r) :
    IsSMulRegular (Dual R A) r := by
  intro α β h
  apply LinearMap.ext
  intro a
  apply hr
  exact congrArg (fun φ : Dual R A => φ a) h

theorem coordinate_quotient_exact (f : A →ₗ[R] B) (e : B ≃ₗ[R] R)
    (I : Ideal R) (hI : LinearMap.range (e.toLinearMap.comp f) = I) :
    LinearMap.range f = LinearMap.ker (I.mkQ.comp e.toLinearMap) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    change I.mkQ (e (f a)) = 0
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    rw [← hI]
    exact ⟨a, rfl⟩
  · intro hb
    have hm : e b ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hb
    rw [← hI] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, e.injective ha⟩

theorem coordinate_quotient_surjective (e : B ≃ₗ[R] R) (I : Ideal R) :
    Function.Surjective (I.mkQ.comp e.toLinearMap) :=
  I.mkQ_surjective.comp e.surjective

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_zero_injective_of_regular
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (hr : IsSMulRegular S r) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  intro α β h
  apply dualConeBottom_injective_of_regular (P.d 1 0).hom r (regular_on_dual r hr)
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  exact (he α).trans (h.trans (he β).symm)

theorem scalarCone_dual_zero_injective
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  intro α β h
  apply dualConeBottom_injective (P.d 1 0).hom r hinj
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  exact (he α).trans (h.trans (he β).symm)

theorem scalarCone_first_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hbound : ∀ k, 0 < k → Subsingleton (P.X k)) (e : P.X 0 ≃ₗ[S] S) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r 0 hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d 1 0).hom.dualMap) = Ideal.span {r} := by
  have he (α : Dual S (P.X 0)) :
      W31.scalarConeTopDualCoordinate P r 0 hbound e
        (((scalarConeComplex P r).d 1 0).hom.dualMap α) =
          r * W31.topDualCoordinate e α := by
    rw [W31.scalarConeTopDualCoordinate_apply]
    exact W31.scalarConeFirstTopBoundary_eval P r α (e.symm 1)
  ext z
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨W31.topDualCoordinate e α, ?_⟩
    exact hα.symm.trans (he α)
  · rintro ⟨a, ha⟩
    refine ⟨(W31.topDualCoordinate e).symm a, ?_⟩
    change W31.scalarConeTopDualCoordinate P r 0 hbound e
      (((scalarConeComplex P r).d 1 0).hom.dualMap ((W31.topDualCoordinate e).symm a)) = z
    rw [he, LinearEquiv.apply_symm_apply]
    exact ha.symm

end SiegelZerosAwei.W30

end

end SiegelZeros

end OAI
