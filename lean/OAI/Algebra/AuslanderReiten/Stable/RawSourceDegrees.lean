import OAI.Algebra.AuslanderReiten.Stable.RawSourceStable

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)

abbrev RawCokernelAt := K.X (-n) ⧸ LinearMap.range (K.d (-(n+1)) (-n)).hom

def rawCokernelAtEquiv : Cokernel (chainOfCochain K) n ≃ₗ[R] RawCokernelAt K n :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -(n+1)) (i' := n+1) (neg_neg (n+1))).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).toLinearEquiv
    (congrArg ModuleCat.Hom.hom
      (reverseShortComplexIso K (-(n+1)) (-n) (-(n-1)) (n+1) n (n-1)
        (neg_neg (n+1)) (neg_neg n) (neg_neg (n-1))).hom.comm₁₂).symm

@[simp]
theorem rawCokernelAtEquiv_symm_mk (z : K.X (-n)) :
    (rawCokernelAtEquiv K n).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).inv.hom z) := rfl

def rawCokernelAtInclusion : RawCokernelAt K (n+1) →ₗ[R] K.X (-n) :=
  (LinearMap.range (K.d (-(n+1+1)) (-(n+1))).hom).liftQ
    (K.d (-(n+1)) (-n)).hom
    (LinearMap.range_le_ker_iff.mpr
      (congrArg ModuleCat.Hom.hom (K.d_comp_d (-(n+1+1)) (-(n+1)) (-n))))

theorem rawCokernelAtInclusion_cover :
    ((LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ).comp
      (rawCokernelAtInclusion K n) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+1+1)) (-(n+1))).hom) z
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩

variable {k : Type u} [Field k] [Algebra k R]
variable {K n} {L M : CochainComplex (ModuleCat.{u} R) ℤ}

def rawSourceAt (x : Cocycle K L n) : RawCokernelAt K n →ₗ[R] CochainCokernel L :=
  (cochainCokernelLinearEquiv L).toLinearMap.comp
    ((sourceCocycleMap x).comp (rawCokernelAtEquiv K n).symm.toLinearMap)

include k in
@[simp]
theorem rawSourceAt_mk [CharP k 2] (x : Cocycle K L n) (z : K.X (-n)) :
    rawSourceAt x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-n) 0 (by omega)).hom z) := by
  change cochainCokernelLinearEquiv L
    (sourceCocycleMap x ((rawCokernelAtEquiv K n).symm (Submodule.Quotient.mk z))) = _
  rw [rawCokernelAtEquiv_symm_mk, sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      ((sourceCocycleComponent x).hom
        ((K.extendXIso negIndexEmbedding (i := -n) (i' := n) (neg_neg n)).inv.hom z))) = _
  simp [sourceCocycleComponent]

include k in
theorem rawSourceAt_postcomp [CharP k 2] (x : Cocycle K L n) (f : L ⟶ M) :
    rawSourceAt (x.postcomp f) = (cochainCokernelMap f).comp (rawSourceAt x) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.d (-(n+1)) (-n)).hom) z
  change rawSourceAt (x.postcomp f) (Submodule.Quotient.mk z) =
    cochainCokernelMap f (rawSourceAt x (Submodule.Quotient.mk z))
  rw [rawSourceAt_mk (k := k), rawSourceAt_mk (k := k)]
  change Submodule.Quotient.mk
    (((x.val.comp (Cochain.ofHom f) (add_zero n)).v (-n) 0 (by omega)).hom z) = _
  rw [Cochain.comp_v _ _ (add_zero n) (-n) 0 0 (by omega) (by omega), Cochain.ofHom_v]
  rfl

def rawSourceAtStableEquiv (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    CohomologyClass K L n ≃+ StableHom R (RawCokernelAt K n) (CochainCokernel L) :=
  (fullHomSourceStableLinearEquiv (k := k) K L n hK hL).toAddEquiv.trans
    (((StableIsomorphism.ofLinearEquiv (rawCokernelAtEquiv K n).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem rawSourceAtStableEquiv_mk
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (x : Cocycle K L n) :
    rawSourceAtStableEquiv (k := k) K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (rawSourceAt x) := by
  simp only [rawSourceAtStableEquiv, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  erw [fullHomSourceStableLinearEquiv_mk hK hL x]
  rw [StableHom.comp_classOf, StableHom.comp_classOf]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
