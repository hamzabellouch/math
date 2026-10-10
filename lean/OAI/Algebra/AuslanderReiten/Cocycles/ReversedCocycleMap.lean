import OAI.Algebra.AuslanderReiten.Stable.SourceStableCoordinates
import OAI.Algebra.AuslanderReiten.Complete.CompleteStableDualityAt

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

def reversedComponent (x : Cochain K L n) (a b : ℤ) (hab : a=n+b) :
    (chainOfCochain K).X a ⟶ (chainOfCochain L).X b :=
  (K.extendXIso negIndexEmbedding (i := -a) (i' := a) (neg_neg a)).hom ≫
    x.v (-a) (-b) (by omega) ≫
      (L.extendXIso negIndexEmbedding (i := -b) (i' := b) (neg_neg b)).inv

include k

theorem reversedComponent_comm (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    reversedComponent x.val (a+1) (b+1) (by omega) ≫ (chainOfCochain L).d (b+1) b =
      (chainOfCochain K).d (a+1) a ≫ reversedComponent x.val a b hab := by
  have hx := congrArg (fun z : Cochain K L (n+1) => z.v (-(a+1)) (-b) (by omega))
    (show δ n (n+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by omega) (-(b+1)) (-a) (by omega) (by omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  have he : x.val.v (-(a+1)) (-(b+1)) (by omega) ≫ L.d (-(b+1)) (-b) =
      K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega) := by
    have hh : (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) +
        (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) = 0 := by
      rw [← two_smul k, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hh).symm
  rw [L.extend_d_eq negIndexEmbedding (neg_neg (b+1)) (neg_neg b),
    K.extend_d_eq negIndexEmbedding (neg_neg (a+1)) (neg_neg a)]
  simp only [reversedComponent, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z =>
    (K.extendXIso negIndexEmbedding (neg_neg (a+1))).hom ≫ z ≫
      (L.extendXIso negIndexEmbedding (neg_neg b)).inv) he

def reversedCokernelMap (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    Cokernel (chainOfCochain K) a →ₗ[R] Cokernel (chainOfCochain L) b :=
  (LinearMap.range ((chainOfCochain K).d (a+1) a).hom).liftQ
    ((LinearMap.range ((chainOfCochain L).d (b+1) b).hom).mkQ.comp
      (reversedComponent x.val a b hab).hom) (by
        rintro _ ⟨y,rfl⟩
        change Submodule.Quotient.mk
          ((reversedComponent x.val a b hab).hom (((chainOfCochain K).d (a+1) a).hom y)) = 0
        have hh := congrArg (fun f => f.hom y) (reversedComponent_comm (k := k) x a b hab)
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨(reversedComponent x.val (a+1) (b+1) (by omega)).hom y, hh⟩)

@[simp] theorem reversedCokernelMap_mk (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b)
    (y : (chainOfCochain K).X a) :
    reversedCokernelMap (k := k) x a b hab (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((reversedComponent x.val a b hab).hom y) := rfl

theorem sourceCocycleMap_eq_reversed (x : Cocycle K L n) :
    sourceCocycleMap x = reversedCokernelMap (k := k) x n 0 (by omega) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    rw [sourceCocycleMap_mk (k := k), reversedCokernelMap_mk]
    rfl

omit k [Field k] [Algebra k R] [CharP k 2] in
theorem reversedComponent_product (x : Cochain K L n) (y : Cochain L M m)
    (a b c : ℤ) (hab : a=n+b) (hbc : b=m+c) :
    reversedComponent (x.comp y rfl) a c (by omega) =
      reversedComponent x a b hab ≫ reversedComponent y b c hbc := by
  simp only [reversedComponent, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Cochain.comp_v x y rfl (-a) (-b) (-c) (by omega) (by omega)]
  simp only [Category.assoc]

theorem reversedCokernelMap_product (x : Cocycle K L n) (y : Cocycle L M m)
    (a b c : ℤ) (hab : a=n+b) (hbc : b=m+c) :
    reversedCokernelMap (k := k) (cocycleProduct x y) a c (by omega) =
      (reversedCokernelMap (k := k) y b c hbc).comp (reversedCokernelMap (k := k) x a b hab) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    simp only [LinearMap.comp_apply, reversedCokernelMap_mk]
    exact congrArg Submodule.Quotient.mk
      (congrArg (fun f => f.hom z) (reversedComponent_product x.val y.val a b c hab hbc))

theorem reversedCokernelMap_syzygy (x : Cocycle K L n)
    (hK : ExactProjectiveComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (a b : ℤ) (hab : a=n+b) :
    (syzygyInclusion hL b).comp (reversedCokernelMap (k := k) x (a+1) (b+1) (by omega)) =
      (reversedComponent x.val a b hab).hom.comp (syzygyInclusion hK a) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    simp only [LinearMap.comp_apply, reversedCokernelMap_mk, syzygyInclusion_mk]
    exact congrArg (fun f => f.hom z) (reversedComponent_comm (k := k) x a b hab)

end ArExplicit.CompleteComparison

end

end OAI
