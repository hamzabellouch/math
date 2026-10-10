import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.FractionDerivation
variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]

open TrivSqZeroExt

def dualMap (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt K K where
  toFun r := inl (algebraMap R K r) + inr (algebraMap R K (D r))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' := by
    intro r s
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        map_add, add_zero, zero_add]
  map_mul' := by
    intro r s
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        fst_mul, snd_mul, add_zero, zero_add, Derivation.leibniz,
        smul_eq_mul, map_add, map_mul, op_smul_eq_mul, mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        algebraMap_eq_inl', Derivation.map_algebraMap, map_zero, add_zero,
        ← IsScalarTower.algebraMap_apply k R K]

omit [IsFractionRing R K] in
@[simp] lemma dualMap_fst (D : Derivation k R R) (r : R) :
    fst (dualMap D r : TrivSqZeroExt K K) = algebraMap R K r := by
  simp only [dualMap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, fst_add, fst_inl, fst_inr, add_zero]

omit [IsFractionRing R K] in
@[simp] lemma dualMap_snd (D : Derivation k R R) (r : R) :
    snd (dualMap D r : TrivSqZeroExt K K) = algebraMap R K (D r) := by
  simp only [dualMap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, snd_add, snd_inl, snd_inr, zero_add]

def dualLift (D : Derivation k R R) : K →ₐ[k] TrivSqZeroExt K K :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors R) (S := K) (f := dualMap D) (by
    intro y
    apply isUnit_iff_isUnit_fst.mpr
    rw [dualMap_fst]
    exact IsLocalization.map_units K y)

lemma dualLift_algebraMap (D : Derivation k R R) (r : R) :
    dualLift D (algebraMap R K r) = dualMap D r :=
  IsLocalization.lift_eq _ r

lemma dualLift_fst (D : Derivation k R R) (z : K) : fst (dualLift D z) = z := by
  have h : (fstHom k K K).comp (dualLift D) = AlgHom.id k K := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom,
      AlgHom.comp_apply, dualLift_algebraMap, AlgHom.id_apply]
    exact dualMap_fst D r
  exact DFunLike.congr_fun h z

def extend (D : Derivation k R R) : Derivation k K K :=
  Derivation.mk' (((sndHom K K).restrictScalars k).comp (dualLift D).toLinearMap) (by
    intro x y
    change snd (dualLift D (x*y)) = x * snd (dualLift D y) + y * snd (dualLift D x)
    rw [map_mul, snd_mul, dualLift_fst, dualLift_fst]
    simp only [smul_eq_mul, op_smul_eq_mul, mul_comm])

@[simp] lemma extend_algebraMap (D : Derivation k R R) (r : R) :
    extend D (algebraMap R K r) = algebraMap R K (D r) := by
  change snd (dualLift D (algebraMap R K r)) = _
  rw [dualLift_algebraMap]
  exact dualMap_snd D r

lemma iterate_algebraMap (D : Derivation k R R) (r : R) (n : ℕ) :
    (extend D : K → K)^[n] (algebraMap R K r) = algebraMap R K ((D : R → R)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, extend_algebraMap,
      Function.iterate_succ_apply']

end ComplexCancellation.FractionDerivation

end

end OAI
