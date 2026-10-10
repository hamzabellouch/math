import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open HahnSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (p : M)
local instance laurentRayRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRayAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRayAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance laurentRayNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def laurentRay (f : HahnSeries ℤ R) : HahnSeries ℤ (Torus v Ω) where
  coeff n:=Torus.monomial v Ω (n • p) (f.coeff n)
  isPWO_support':=f.isPWO_support.mono (by
    intro n hn
    change Torus.monomial v Ω (n • p) (f.coeff n)≠0 at hn
    change f.coeff n≠0
    intro he
    exact hn (by rw [he]; exact Finsupp.single_zero _))
lemma laurentRay_coeff (f : HahnSeries ℤ R) (n : ℤ) :
    (laurentRay v Ω p f).coeff n=Torus.monomial v Ω (n • p) (f.coeff n) := rfl
lemma laurentRay_support (f : HahnSeries ℤ R) : (laurentRay v Ω p f).support=f.support := by
  ext n
  simp only [HahnSeries.mem_support,laurentRay_coeff]
  constructor
  · intro hn hz
    apply hn
    rw [hz]
    exact Finsupp.single_zero _
  · intro hn hz
    have H:=congrArg (fun a : Torus v Ω=>a (n • p)) hz
    exact hn (by simpa [Torus.monomial] using H)
lemma laurentRay_zero : laurentRay v Ω p 0=0 := by
  apply HahnSeries.ext
  funext n
  simp [laurentRay_coeff]
lemma laurentRay_add (f g : HahnSeries ℤ R) :
    laurentRay v Ω p (f+g)=laurentRay v Ω p f+laurentRay v Ω p g := by
  apply HahnSeries.ext
  funext n
  simp [laurentRay_coeff,Torus.monomial]
lemma laurentRay_single (n : ℤ) (a : R) :
    laurentRay v Ω p (HahnSeries.single n a)=HahnSeries.single n (Torus.monomial v Ω (n • p) a) := by
  apply HahnSeries.ext
  funext j
  simp only [laurentRay_coeff,HahnSeries.coeff_single]
  by_cases hj : j=n
  · subst j; simp
  · simp [hj,Torus.monomial]
lemma laurentRay_one : laurentRay v Ω p 1=1 := by
  change laurentRay v Ω p (HahnSeries.single 0 1)=HahnSeries.single 0 1
  rw [laurentRay_single,zero_smul]
  rfl
lemma laurentRay_mul (hp : Ω p p=0) (f g : HahnSeries ℤ R) :
    laurentRay v Ω p (f*g)=laurentRay v Ω p f*laurentRay v Ω p g := by
  classical
  apply HahnSeries.ext
  funext n
  rw [laurentRay_coeff,HahnSeries.coeff_mul,HahnSeries.coeff_mul]
  have HS : Finset.antidiagonal (laurentRay v Ω p f).isPWO_support
      (laurentRay v Ω p g).isPWO_support n=
      Finset.antidiagonal f.isPWO_support g.isPWO_support n := by
    ext ij
    simp only [Finset.mem_antidiagonal,laurentRay_support]
  rw [HS]
  change (Finsupp.singleAddHom (n • p)) _=_
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have H:=(Finset.mem_antidiagonal.mp hij).2.2
  simp only [laurentRay_coeff,Torus.monomial_mul_monomial,map_zsmul,
    AddMonoidHom.zsmul_apply,hp,smul_zero,zpow_zero,Units.val_one,mul_one]
  rw [←add_zsmul,H]
  rfl

def laurentRayHom (hp : Ω p p=0) : HahnSeries ℤ R →+* HahnSeries ℤ (Torus v Ω) where
  toFun:=laurentRay v Ω p
  map_zero':=laurentRay_zero v Ω p
  map_one':=laurentRay_one v Ω p
  map_add':=laurentRay_add v Ω p
  map_mul':=laurentRay_mul v Ω p hp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
