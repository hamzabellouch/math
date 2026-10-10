import OAI.Algebra.AuslanderReiten.Stable.RawSourceDegrees
import OAI.Algebra.AuslanderReiten.Cocycles.ReversedCocycleMap

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

def rawCokernelAtMap (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    RawCokernelAt K a →ₗ[R] RawCokernelAt L b :=
  (rawCokernelAtEquiv L b).toLinearMap.comp
    ((reversedCokernelMap (k := k) x a b hab).comp
      (rawCokernelAtEquiv K a).symm.toLinearMap)

@[simp]
theorem rawCokernelAtMap_mk (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b)
    (z : K.X (-a)) :
    rawCokernelAtMap (k := k) x a b hab (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-a) (-b) (by omega)).hom z) := by
  change rawCokernelAtEquiv L b
    (reversedCokernelMap (k := k) x a b hab
      ((rawCokernelAtEquiv K a).symm (Submodule.Quotient.mk z))) = _
  rw [rawCokernelAtEquiv_symm_mk, reversedCokernelMap_mk]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := -b) (i' := b) (neg_neg b)).hom.hom
      ((reversedComponent x.val a b hab).hom
        ((K.extendXIso negIndexEmbedding (i := -a) (i' := a) (neg_neg a)).inv.hom z))) = _
  simp [reversedComponent]

theorem rawSourceAt_eq_map (x : Cocycle K L n) :
    rawSourceAt x = rawCokernelAtMap (k := k) x n 0 (by omega) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (K.d (-(n+1)) (-n)).hom) z
  erw [rawSourceAt_mk (k := k), rawCokernelAtMap_mk]
  rfl

include k in

theorem rawCocycleComponent_comm (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    x.val.v (-(a+1)) (-(b+1)) (by omega) ≫ L.d (-(b+1)) (-b) =
      K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega) := by
  have hx := congrArg (fun z : Cochain K L (n+1) => z.v (-(a+1)) (-b) (by omega))
    (show δ n (n+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by omega) (-(b+1)) (-a) (by omega) (by omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  have hh : (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) +
      (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) = 0 := by
    rw [← two_smul k, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hh).symm

theorem rawCokernelAtMap_cover (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    (rawCokernelAtInclusion L b).comp
      (rawCokernelAtMap (k := k) x (a+1) (b+1) (by omega)) =
    (x.val.v (-a) (-b) (by omega)).hom.comp (rawCokernelAtInclusion K a) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(a+1+1)) (-(a+1))).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawCokernelAtMap_mk]
  exact congrArg (fun f => f.hom z) (rawCocycleComponent_comm (k := k) x a b hab)

theorem rawSourceAt_product (x : Cocycle K L n) (y : Cocycle L M m) :
    rawSourceAt (cocycleProduct x y) =
      (rawSourceAt y).comp (rawCokernelAtMap (k := k) x (n+m) m rfl) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+m+1)) (-(n+m))).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawSourceAt_mk (k := k), rawCokernelAtMap_mk, rawSourceAt_mk (k := k)]
  change Submodule.Quotient.mk
    (((x.val.comp y.val rfl).v (-(n+m)) 0 (by omega)).hom z) = _
  rw [Cochain.comp_v _ _ rfl (-(n+m)) (-m) 0 (by omega) (by omega)]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
