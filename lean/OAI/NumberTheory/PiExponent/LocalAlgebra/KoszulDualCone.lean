import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceResolution

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [Module R X] [Module R Y] [Module R Z] [Module R W]

def dualConeDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (Dual R Y × Dual R Z) →ₗ[R] (Dual R X × Dual R Y) :=
  (f.dualMap.comp (LinearMap.fst R _ _)).prod
    (r • LinearMap.fst R _ _ - g.dualMap.comp (LinearMap.snd R _ _))

@[simp] theorem dualConeDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    dualConeDifferential f g r (α, β) = (α.comp f, r • α - β.comp g) := rfl

theorem coneDifferential_dual_precomposition (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    (α.coprod β).comp (coneDifferential f g r) =
      (α.comp f).coprod (r • α - β.comp g) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change α (f x + r • y) + β (-g y) = α (f x) + (r • α - β.comp g) y
  change α (f x + r • y) + β (-g y) =
    α (f x) + (r • α y - β (g y))
  simp only [map_add, map_smul, map_neg, sub_eq_add_neg]
  abel

theorem coneDifferential_dual_equiv (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R X Y).toLinearMap.comp (dualConeDifferential f g r) =
      (coneDifferential f g r).dualMap.comp (dualProdDualEquivDual R Y Z).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨α, β⟩
  exact (coneDifferential_dual_precomposition f g r α β).symm

theorem dualConeDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgf : LinearMap.range g.dualMap = LinearMap.ker f.dualMap) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    have hfg : f.dualMap (g.dualMap α) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hgf) α
    have hgh : g.dualMap (h.dualMap β) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker h.dualMap g.dualMap hhg) β
    apply Prod.ext
    · exact hfg
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      simp only [map_sub, map_smul, hgh, sub_zero, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgf]
      exact ha
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end PiExponentSiegelAux.W30

end OAI
