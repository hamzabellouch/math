import Mathlib

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R S : Type*} [CommRing R] [CommRing S]

def mapRing (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

@[simp] lemma mapRing_coeff (f : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (mapRing f x).coeff n=f (x.coeff n) := rfl

@[simp] lemma mapRing_single (f : R →+* S) (n : ℤ) (r : R) :
    mapRing f (single n r)=single n (f r) := by
  ext k
  by_cases h : k=n <;> simp [h]

@[simp] lemma mapRing_C (f : R →+* S) (r : R) : mapRing f (C r)=C (f r) :=
  mapRing_single f 0 r

lemma mapRing_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (mapRing f) := by
  intro x y h
  ext k
  exact hf (congrArg (fun z : LaurentSeries S=>z.coeff k) h)

section Linear
variable {K V W : Type*} [Semiring K] [AddCommMonoid V] [AddCommMonoid W]
  [Module K V] [Module K W]

def mapLinear (f : V →ₗ[K] W) : LaurentSeries V →ₗ[K] LaurentSeries W where
  toFun x := x.map f
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_smul' r x := by ext k; exact f.map_smul r (x.coeff k)

@[simp] lemma mapLinear_coeff (f : V →ₗ[K] W) (x : LaurentSeries V) (k : ℤ) :
    (mapLinear f x).coeff k=f (x.coeff k) := rfl
end Linear

noncomputable def zUnit (n : ℤ) : (LaurentSeries R)ˣ where
  val := single (-n) 1
  inv := single n 1
  val_inv := by simp [single_mul_single]
  inv_val := by simp [single_mul_single]

@[simp] lemma zUnit_val (n : ℤ) : (zUnit (R:=R) n : LaurentSeries R)=single (-n) 1 := rfl

@[simp] lemma zUnit_map (f : R →+* S) (n : ℤ) :
    Units.map (mapRing f).toMonoidHom (zUnit n)=zUnit n := by
  apply Units.ext
  simp

noncomputable def oneSubUnit (c : R) : (PowerSeries R)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff (φ:=1-PowerSeries.C c*PowerSeries.X) |>.mpr (by simp)).unit

@[simp] lemma oneSubUnit_val (c : R) :
    (oneSubUnit c : PowerSeries R)=1-PowerSeries.C c*PowerSeries.X := by
  exact IsUnit.unit_spec _

noncomputable def affineUnit (c : R) : (LaurentSeries R)ˣ :=
  -zUnit (R:=R) 1 * Units.map (ofPowerSeries ℤ R).toMonoidHom (oneSubUnit c)

@[simp] lemma affineUnit_val (c : R) :
    (affineUnit c : LaurentSeries R)=C c-(zUnit (R:=R) 1 : LaurentSeries R) := by
  change -(single (-1:ℤ) (1:R)) * ((ofPowerSeries ℤ R) (oneSubUnit c : PowerSeries R)) = _
  rw [oneSubUnit_val,PowerSeries.coe_sub,PowerSeries.coe_one,PowerSeries.coe_mul,
    PowerSeries.coe_C,PowerSeries.coe_X,zUnit_val]
  rw [mul_sub,mul_one,neg_mul]
  have h : single (-1:ℤ) (1:R) * (C c * single 1 1)=C c := by
    rw [← mul_assoc]
    change single (-1:ℤ) (1:R) * single 0 c * single 1 1=single 0 c
    simp [single_mul_single]
  rw [h]
  ring

@[simp] lemma affineUnit_map (f : R →+* S) (c : R) :
    Units.map (mapRing f).toMonoidHom (affineUnit c)=affineUnit (f c) := by
  apply Units.ext
  simp

noncomputable def polynomial : Polynomial R →+* LaurentSeries R :=
  Polynomial.eval₂RingHom C (zUnit (R:=R) 1 : LaurentSeries R)

@[simp] lemma polynomial_C (r : R) : polynomial (Polynomial.C r)=C r := by
  simp [polynomial]

@[simp] lemma polynomial_X : polynomial (Polynomial.X : Polynomial R)=(zUnit (R:=R) 1 : LaurentSeries R) := by
  simp [polynomial]

noncomputable def polynomialAlg (K : Type*) [CommSemiring K] [Algebra K R] :
    Polynomial R →ₐ[K] LaurentSeries R where
  __ := polynomial
  commutes' k := by
    change polynomial ((algebraMap K (Polynomial R)) k)=(algebraMap K (LaurentSeries R)) k
    rw [Polynomial.algebraMap_apply,polynomial_C]
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, PowerSeries.coe_C]

lemma polynomial_monomial (n : ℕ) (r : R) :
    polynomial (Polynomial.monomial n r)=single (-(n:ℤ)) r := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,polynomial_C,polynomial_X,zUnit_val,
    single_pow]
  change single 0 r * single _ _=_
  simp [single_mul_single]

lemma polynomial_map (f : R →+* S) (p : Polynomial R) :
    mapRing f (polynomial p)=polynomial (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | monomial n r => simp [polynomial_monomial]

lemma polynomial_coeff (p : Polynomial R) (n : ℕ) :
    (polynomial p).coeff (-(n:ℤ))=p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,Polynomial.coeff_add,hp,hq]
  | monomial k r => simp [polynomial_monomial,coeff_single,Polynomial.coeff_monomial,eq_comm]

lemma polynomial_coeff_positive (p : Polynomial R) (n : ℤ) (hn : 0<n) :
    (polynomial p).coeff n=0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,coeff_add,hp,hq,add_zero]
  | monomial k r =>
    rw [polynomial_monomial,coeff_single,ite_eq_right]
    omega

lemma polynomial_injective : Function.Injective (polynomial (R:=R)) := by
  intro p q h
  ext n
  simpa only [polynomial_coeff] using congrArg (fun x : LaurentSeries R=>x.coeff (-(n:ℤ))) h

end ElementaryPositivity.LaurentAtInfinity

end

end OAI
