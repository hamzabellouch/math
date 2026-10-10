import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.PolynomialDerivation
open TrivSqZeroExt
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def dual (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt R R where
  toFun r := inl r + inr (D r)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
@[simp] lemma dual_fst (D : Derivation k R R) (r : R) : fst (dual D r)=r := by simp [dual]
@[simp] lemma dual_snd (D : Derivation k R R) (r : R) : snd (dual D r)=D r := by simp [dual]
def fromDual (g : R →ₐ[k] TrivSqZeroExt R R)
    (hg : ∀ r, fst (g r)=r) : Derivation k R R :=
  Derivation.mk' (((sndHom R R).restrictScalars k).comp g.toLinearMap) (by
    intro r s
    change snd (g (r*s)) = r * snd (g s)+s * snd (g r)
    rw [map_mul,snd_mul,hg,hg]
    simp only [smul_eq_mul,op_smul_eq_mul,mul_comm])
variable {S : Type*} [CommRing S] [Algebra k S]
def along (f : R →ₐ[k] S) (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt S S where
  toFun r := inl (f r)+inr (f (D r))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
@[simp] lemma along_fst (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    fst (along f D r)=f r := by simp [along]
@[simp] lemma along_snd (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    snd (along f D r)=f (D r) := by simp [along]

variable {ι : Type*}
def mvDual (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[k] TrivSqZeroExt (MvPolynomial ι R) (MvPolynomial ι R) where
  __ := MvPolynomial.eval₂Hom (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).toRingHom
    (fun i => inl (MvPolynomial.X i)+inr (d i))
  commutes' a := by
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C (algebraMap k R a)) = _
    rw [MvPolynomial.eval₂_C]
    exact (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).commutes a
lemma mvDual_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mvDual D d (MvPolynomial.C r)=inl (MvPolynomial.C r)+inr (MvPolynomial.C (D r)) :=
  MvPolynomial.eval₂_C _ _ _
lemma mvDual_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mvDual D d (MvPolynomial.X i)=inl (MvPolynomial.X i)+inr (d i) :=
  MvPolynomial.eval₂_X _ _ _
lemma mvDual_fst (D : Derivation k R R) (d : ι → MvPolynomial ι R) (p : MvPolynomial ι R) :
    fst (mvDual D d p)=p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [mvDual_C]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [mvDual_X,hp]
def mv (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    Derivation k (MvPolynomial ι R) (MvPolynomial ι R) := fromDual (mvDual D d) (mvDual_fst D d)
@[simp] lemma mv_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mv D d (MvPolynomial.C r)=MvPolynomial.C (D r) := by
  change snd (mvDual D d (MvPolynomial.C r))=_
  simp [mvDual_C]
@[simp] lemma mv_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mv D d (MvPolynomial.X i)=d i := by
  change snd (mvDual D d (MvPolynomial.X i))=_
  simp [mvDual_X]
end ComplexCancellation.PolynomialDerivation

end

end OAI
