import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalPureAction
import OAI.Combinatorics.Chromatic.Walls.LaurentCompletion

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def purePower : PowerSeries K →+* HahnSeries ℤ (Torus v Ω) :=
  (laurentRayHom v Ω p (hΩ p)).comp (HahnSeries.ofPowerSeries ℤ K)
lemma purePower_eq (f : PowerSeries K) :
    purePower v Ω hΩ p f=HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f) := by
  apply HahnSeries.ext
  funext n
  change Torus.monomial v Ω (n • p) ((HahnSeries.ofPowerSeries ℤ K f).coeff n)=_
  rcases le_or_gt 0 n with hn|hn
  · lift n to ℕ using hn with j hj
    rw [HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff,coeff_raySeries]
    simp only [natCast_zsmul]
  · have H : (HahnSeries.ofPowerSeries ℤ K f).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    have H' : (HahnSeries.ofPowerSeries ℤ (Torus v Ω) (raySeries v Ω p f)).coeff n=0 := by
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_of_notMem_range
      rintro ⟨a,ha⟩
      change (a:ℤ)=n at ha
      omega
    rw [H,H',Torus.monomial_zero]
lemma purePower_commutation (m : M) (f : PowerSeries K) :
    HahnSeries.single 0 (Torus.X v Ω m)*purePower v Ω hΩ p f=
      purePower v Ω hΩ p (rescale (↑(v^(-2*Ω p m)):K) f)*
        HahnSeries.single 0 (Torus.X v Ω m) := by
  have H:=raySeries_twist v Ω hΩ p m (rescale (↑(v^(-2*Ω p m)):K) f)
  rw [rescale_rescale,←Units.val_mul,←zpow_add,
    show -2*Ω p m+2*Ω p m=0 by ring,zpow_zero,Units.val_one,rescale_one] at H
  have HH:=congrArg (HahnSeries.ofPowerSeries ℤ (Torus v Ω)) H
  rw [purePower_eq,purePower_eq]
  simpa only [map_mul,HahnSeries.ofPowerSeries_C,HahnSeries.C_apply,RingHom.id_apply] using HH.symm
lemma purePower_scalar_commute (a : RatFunc K) (f : PowerSeries K) :
    expandScalar v Ω hΩ p a*purePower v Ω hΩ p f=
      purePower v Ω hΩ p f*expandScalar v Ω hΩ p a := by
  change (laurentRayHom v Ω p (hΩ p)) (expandZero a)*
    (laurentRayHom v Ω p (hΩ p)) (HahnSeries.ofPowerSeries ℤ K f)=_
  rw [←map_mul,mul_comm,map_mul]
  rfl
lemma expandedPure_shifted
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℤ) :
    expandScalar v Ω hΩ p (pureRatio v t:RatFunc K)*
      purePower v Ω hΩ p (shiftedElementary v t)=purePower v Ω hΩ p (shiftedElementary v 0) := by
  have H:=congrArg (laurentRayHom v Ω p (hΩ p)) (expandedPure_times_shift v hq t)
  simpa only [map_mul,expandScalar,purePower,RingHom.comp_apply] using H

def pureLaurentUnit : (HahnSeries ℤ (Torus v Ω))ˣ where
  val:=purePower v Ω hΩ p (shiftedElementary v 0)
  inv:=purePower v Ω hΩ p (shiftedElementary v 0)⁻¹
  val_inv:=by
    rw [←map_mul,PowerSeries.mul_inv_cancel _ (by rw [shiftedElementary_constant]; exact one_ne_zero),map_one]
  inv_val:=by
    rw [←map_mul,PowerSeries.inv_mul_cancel _ (by rw [shiftedElementary_constant]; exact one_ne_zero),map_one]
variable (k : M →+ ℤ)
lemma expand_pure_intertwine
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)*
      (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))=
    (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*expandFiber v Ω hΩ k p f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,add_mul,mul_add,hf,hg]
  | single l a=>
    change expandFiber v Ω hΩ k p
      (pureAction v _ _ (FiberTorus.monomial v _ _ l a))*_=_
    rw [pureAction_monomial]
    change expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l
      (a*(pureRatio v (Ω p l):RatFunc K)))*_= _*expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)
    rw [expandFiberAdd_monomial,expandFiberAdd_monomial]
    change (expandScalar v Ω hΩ p (a*(pureRatio v (Ω p l):RatFunc K))*
      HahnSeries.single 0 (Torus.X v Ω l))*purePower v Ω hΩ p (shiftedElementary v 0)=
      purePower v Ω hΩ p (shiftedElementary v 0)*
        (expandScalar v Ω hΩ p a*HahnSeries.single 0 (Torus.X v Ω l))
    rw [map_mul,mul_assoc,mul_assoc,purePower_commutation]
    have H : rescale (↑(v^(-2*Ω p l)):K) (shiftedElementary v 0)=shiftedElementary v (Ω p l) := by
      rw [shiftedElementary_zero]
      rfl
    rw [H,←mul_assoc (expandScalar v Ω hΩ p (pureRatio v (Ω p l):RatFunc K)),
      expandedPure_shifted v Ω hΩ p hq,←mul_assoc,purePower_scalar_commute,mul_assoc]
lemma expand_pure_conjugate
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiber v Ω hΩ k p (pureAction v (complementOmega k Ω) (complementAlpha k p Ω) f)=
      innerHom (pureLaurentUnit v Ω hΩ p) (expandFiber v Ω hΩ k p f) := by
  have H:=congrArg (fun x : HahnSeries ℤ (Torus v Ω)=>x*↑((pureLaurentUnit v Ω hΩ p)⁻¹))
    (expand_pure_intertwine v Ω hΩ p k hq f)
  have hu : (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*↑((pureLaurentUnit v Ω hΩ p)⁻¹)=1 :=
    (pureLaurentUnit v Ω hΩ p).val_inv
  change _=(↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω))*
    expandFiber v Ω hΩ k p f*↑((pureLaurentUnit v Ω hΩ p)⁻¹)
  simpa only [mul_assoc,hu,mul_one] using H
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ κ : M →+ ℤ) (p : M) (hδ : δ p=0) (hκ : κ p=1)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
include hδ hκ in
lemma pure_biSupported (f : PowerSeries K) : BiSupported v Ω δ κ (raySeries v Ω p f) := by
  intro n m hm
  rw [coeff_raySeries] at hm
  have he : m=n • p := by
    by_contra H
    exact hm (Finsupp.single_eq_of_ne H)
  subst m
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one]
  exact ⟨le_rfl,Int.natCast_nonneg _,by omega⟩
include hδ hκ in
lemma biRegrade_pure (f : PowerSeries K) :
    biRegrade v Ω δ κ (raySeries v Ω p f)=PowerSeries.C (raySeries v Ω p f) := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [biRegrade_coeff,coeff_raySeries,biHomogenize_monomial]
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,
    Int.toNat_natCast,coeff_monomial]
  by_cases hd : d=0
  · subst d
    simp [coeff_C,coeff_raySeries]
  · simp [coeff_C,hd]
include hδ hκ in
lemma oldLaurent_pure (f : PowerSeries K) :
    oldLaurent v Ω δ κ (raySeries v Ω p f)=PowerSeries.C (purePower v Ω hΩ p f) := by
  rw [oldLaurent,biRegrade_pure v Ω δ κ p hδ hκ,PowerSeries.map_C,purePower_eq]
include hδ hκ in
lemma oldLaurent_pure_unit :
    oldLaurent v Ω δ κ (rayUnit v Ω p (hΩ p) (shiftedElementary v 0)
      (shiftedElementary_constant v 0)).val=
      PowerSeries.C (↑(pureLaurentUnit v Ω hΩ p):HahnSeries ℤ (Torus v Ω)) :=
  oldLaurent_pure v Ω hΩ δ κ p hδ hκ _
include hδ hκ in
lemma oldLaurent_pure_inverse :
    oldLaurent v Ω δ κ (rayUnit v Ω p (hΩ p) (shiftedElementary v 0)
      (shiftedElementary_constant v 0)).inv=
      PowerSeries.C (↑((pureLaurentUnit v Ω hΩ p)⁻¹):HahnSeries ℤ (Torus v Ω)) :=
  oldLaurent_pure v Ω hΩ δ κ p hδ hκ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
