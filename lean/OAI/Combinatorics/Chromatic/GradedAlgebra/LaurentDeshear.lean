import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegrade

namespace OAI

section
namespace ElementaryPositivity.Deshear
open PowerSeries HahnSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma single_central (z : ℤ) (f : HahnSeries ℤ R) :
    single z 1 * f = f * single z 1 := by
  apply HahnSeries.ext
  funext e
  simp only [coeff_single_mul, coeff_mul_single, one_mul, mul_one]
lemma shift_mul (z w : ℤ) (f g : HahnSeries ℤ R) :
    single (z+w) 1 * (f*g) = (single z 1*f)*(single w 1*g) := by
  rw [show (1 : R)=1*1 from (one_mul _).symm, ←single_mul_single]
  simp only [one_mul]
  calc
    _ = single z 1*(single w 1*f)*g := by simp only [mul_assoc]
    _ = single z 1*(f*single w 1)*g := by rw [single_central w f]
    _ = _ := by simp only [mul_assoc]

def deshear (B : ℕ) (f : PowerSeries (PowerSeries R)) : PowerSeries (HahnSeries ℤ R) :=
  PowerSeries.mk fun d => single (-(B : ℤ)*(d : ℤ)) 1 * ofPowerSeries ℤ R (coeff d f)
lemma deshear_coeff (B : ℕ) (f : PowerSeries (PowerSeries R)) (d : ℕ) :
    coeff d (deshear B f) = single (-(B : ℤ)*(d : ℤ)) 1 * ofPowerSeries ℤ R (coeff d f) := by
  rw [deshear, coeff_mk]
lemma deshear_read (B : ℕ) (f : PowerSeries (PowerSeries R)) (d : ℕ) (z : ℤ) :
    (coeff d (deshear B f)).coeff z =
      (ofPowerSeries ℤ R (coeff d f)).coeff (z+(B : ℤ)*(d : ℤ)) := by
  rw [deshear_coeff, coeff_single_mul, one_mul]
  congr 1
  ring
lemma deshear_zero (B : ℕ) : deshear (R:=R) B 0=0 := by
  apply PowerSeries.ext
  intro d
  simp [deshear_coeff]
lemma deshear_one (B : ℕ) : deshear (R:=R) B 1=1 := by
  apply PowerSeries.ext
  intro d
  rw [deshear_coeff]
  by_cases hd : d=0
  · subst d
    simp
  · simp [PowerSeries.coeff_one,hd]
lemma deshear_add (B : ℕ) (f g : PowerSeries (PowerSeries R)) :
    deshear B (f+g)=deshear B f+deshear B g := by
  apply PowerSeries.ext
  intro d
  simp only [deshear_coeff,map_add,mul_add]
lemma deshear_mul (B : ℕ) (f g : PowerSeries (PowerSeries R)) :
    deshear B (f*g)=deshear B f*deshear B g := by
  apply PowerSeries.ext
  intro d
  rw [deshear_coeff,PowerSeries.coeff_mul,PowerSeries.coeff_mul,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [map_mul,deshear_coeff,deshear_coeff]
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [←shift_mul]
  congr 2
  rw [←H,Nat.cast_add,mul_add]

def deshearHom (B : ℕ) : PowerSeries (PowerSeries R) →+* PowerSeries (HahnSeries ℤ R) where
  toFun := deshear B
  map_zero' := deshear_zero B
  map_one' := deshear_one B
  map_add' := deshear_add B
  map_mul' := deshear_mul B
end
end ElementaryPositivity.Deshear

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
local instance laurentDeshearRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentDeshearAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentDeshearAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentDeshearNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance laurentDeshearNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma LaurentBounded.bi_shear {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) : BiBounded v Ω δ (κ+B • δ) f := by
  intro n m hm
  obtain ⟨hd,hk,hn⟩:=hf n m hm
  change 0≤δ m ∧ 0≤κ m+(B:ℤ)*δ m ∧ (n:ℤ)≤δ m+(κ m+(B:ℤ)*δ m)
  exact ⟨hd,by nlinarith,by nlinarith⟩

lemma laurentHomogenize_shear_coeff (f : Torus v Ω)
    (hf : ∀m,f m≠0 → 0≤δ m ∧ 0≤κ m+(B:ℤ)*δ m)
    (d : ℕ) (z : ℤ) (hz : 0≤z+(B:ℤ)*(d:ℤ)) :
    (coeff d (laurentHomogenize v Ω δ κ f)).coeff z =
      coeff (z+(B:ℤ)*(d:ℤ)).toNat (coeff d (biHomogenize v Ω δ (κ+B • δ) f)) := by
  ext m
  rw [laurentHomogenize_coeff,biHomogenize_coeff]
  by_cases hm : f m=0
  · simp [hm]
  obtain ⟨hd,hk⟩:=hf m hm
  change (if d=(δ m).toNat ∧ z=κ m then f m else 0)=
    if d=(δ m).toNat ∧ (z+(B:ℤ)*(d:ℤ)).toNat=(κ m+(B:ℤ)*δ m).toNat then f m else 0
  by_cases he : d=(δ m).toNat
  · have hD : δ m=(d:ℤ) := by rw [he,Int.toNat_of_nonneg hd]
    rw [hD] at hk ⊢
    have H : (z+(B:ℤ)*(d:ℤ)).toNat=(κ m+(B:ℤ)*(d:ℤ)).toNat ↔ z=κ m := by omega
    simp only [Int.toNat_natCast, true_and, H, eq_self]
  · simp only [he,false_and,ite_false]

lemma laurentRegrade_eq_deshear (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) :
    laurentRegrade v Ω δ κ B f hf = Deshear.deshear B (boundedBiRegrade v Ω δ (κ+B • δ) f) := by
  apply PowerSeries.ext
  intro d
  apply HahnSeries.ext
  funext z
  rw [laurentRegrade_coeff,Deshear.deshear_read]
  by_cases hz : 0≤z+(B:ℤ)*(d:ℤ)
  · have hcast : ((z+(B:ℤ)*(d:ℤ)).toNat:ℤ)=z+(B:ℤ)*(d:ℤ) := Int.toNat_of_nonneg hz
    rw [←hcast,HahnSeries.ofPowerSeries_apply_coeff,boundedBiRegrade_coeff]
    have hN : (z+(B+1:ℤ)*(d:ℤ)).toNat=d+(z+(B:ℤ)*(d:ℤ)).toNat := by
      rw [show z+(B+1:ℤ)*(d:ℤ)=(d:ℤ)+(z+(B:ℤ)*(d:ℤ)) by ring,
        Int.toNat_add (Int.natCast_nonneg d) hz,Int.toNat_natCast]
    rw [hN]
    apply Finset.sum_congr rfl
    intro n hn
    exact laurentHomogenize_shear_coeff v Ω δ κ B (coeff n f)
      (fun m hm=>⟨(hf n m hm).1,by have H:=(hf n m hm).2.1; nlinarith⟩) d z hz
  · have hneg : z+(B:ℤ)*(d:ℤ)<0 := lt_of_not_ge hz
    rw [HahnSeries.ofPowerSeries_apply,HahnSeries.embDomain_of_notMem_range]
    · apply Finset.sum_eq_zero
      intro n hn
      apply hf.laurent_vanish v Ω δ κ B d n z
      left
      nlinarith
    · rintro ⟨n,hn⟩
      simp only [Nat.castOrderEmbedding_apply] at hn
      omega

lemma laurentRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    laurentRegrade v Ω δ κ B (f*g) (hf.mul v Ω δ κ B hg)=
      laurentRegrade v Ω δ κ B f hf*laurentRegrade v Ω δ κ B g hg := by
  rw [laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,
    boundedBiRegrade_mul v Ω δ (κ+B • δ) (hf.bi_shear v Ω δ κ B) (hg.bi_shear v Ω δ κ B),
    Deshear.deshear_mul]
lemma laurentRegrade_add {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    laurentRegrade v Ω δ κ B (f+g) (hf.add v Ω δ κ B hg)=
      laurentRegrade v Ω δ κ B f hf+laurentRegrade v Ω δ κ B g hg := by
  rw [laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,laurentRegrade_eq_deshear,
    boundedBiRegrade_add,Deshear.deshear_add]
lemma laurentRegrade_zero : laurentRegrade v Ω δ κ B 0 (LaurentBounded.zero v Ω δ κ B)=0 := by
  rw [laurentRegrade_eq_deshear,boundedBiRegrade_zero,Deshear.deshear_zero]
lemma laurentRegrade_one : laurentRegrade v Ω δ κ B 1 (LaurentBounded.one v Ω δ κ B)=1 := by
  rw [laurentRegrade_eq_deshear,boundedBiRegrade_one,Deshear.deshear_one]

def laurentBoundedSubring : Subring (PowerSeries (Torus v Ω)) where
  carrier := LaurentBounded v Ω δ κ B
  zero_mem' := LaurentBounded.zero v Ω δ κ B
  one_mem' := LaurentBounded.one v Ω δ κ B
  add_mem' := LaurentBounded.add v Ω δ κ B
  neg_mem' := LaurentBounded.neg v Ω δ κ B
  mul_mem' := LaurentBounded.mul v Ω δ κ B

def laurentRegradeHom : laurentBoundedSubring v Ω δ κ B →+* PowerSeries (HahnSeries ℤ (Torus v Ω)) where
  toFun f := laurentRegrade v Ω δ κ B f.val f.property
  map_zero' := laurentRegrade_zero v Ω δ κ B
  map_one' := laurentRegrade_one v Ω δ κ B
  map_add' f g := laurentRegrade_add v Ω δ κ B f.property g.property
  map_mul' f g := laurentRegrade_mul v Ω δ κ B f.property g.property
end
end ElementaryPositivity.QuantumTorus

end

end OAI
