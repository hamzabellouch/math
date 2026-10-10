import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualTransport

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module R X] [Module R Y] [Module R Z]

def dualConeBottom (g : Y →ₗ[R] Z) (r : R) :
    Dual R Z →ₗ[R] (Dual R Y × Dual R Z) :=
  g.dualMap.prod (r • LinearMap.id)

@[simp] theorem dualConeBottom_apply (g : Y →ₗ[R] Z) (r : R) (α : Dual R Z) :
    dualConeBottom g r α = (α.comp g, r • α) := rfl

theorem coneBottom_dual_equiv (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R Y Z).toLinearMap.comp (dualConeBottom g r) =
      (coneBottom g r).dualMap := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  rintro ⟨y, z⟩
  change α (g y) + r • α z = α (g y + r • z)
  rw [map_add, map_smul]

theorem dualConeBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R)
    (hex : LinearMap.range g.dualMap = LinearMap.ker f.dualMap)
    (hinj : Function.Injective g.dualMap) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hex) α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hex]
      exact ha
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

theorem dualConeBottom_injective (g : Y →ₗ[R] Z) (r : R)
    (hinj : Function.Injective g.dualMap) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hinj (congrArg Prod.fst h)

theorem dualConeBottom_injective_of_regular (g : Y →ₗ[R] Z) (r : R)
    (hr : IsSMulRegular (Dual R Z) r) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hr (congrArg Prod.snd h)

theorem dualConeBottom_endpoint_exact {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hinj : Function.Injective g.dualMap) (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_one_exact (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hex : LinearMap.range (P.d 1 0).hom.dualMap =
      LinearMap.ker (P.d 2 1).hom.dualMap)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl S (Dual S (P.X 0)))
    (dualProdDualEquivDual S (P.X 1) (P.X 0))
    (dualProdDualEquivDual S (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_exact _ _ r hex hinj

end PiExponentSiegelAux.W30

end OAI
