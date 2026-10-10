import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualBottom
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulTopAugmentation

namespace OAI

namespace PiExponentSiegelAux.W30
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
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective_of_regular (P.d 1 0).hom r (regular_on_dual r hr)
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

theorem scalarCone_dual_zero_injective
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective (P.d 1 0).hom r hinj
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

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

end PiExponentSiegelAux.W30

end OAI
