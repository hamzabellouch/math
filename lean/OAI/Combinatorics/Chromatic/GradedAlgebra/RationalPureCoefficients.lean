import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalCenteredAction
import OAI.Combinatorics.Chromatic.Walls.CenteredUnitRatio

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
def centeredRatio (t : ℤ) : PowerSeries K :=
  rescale (↑(v^(-t)):K)
    (rescale (↑(v^(2*t)):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))*
      (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))⁻¹)
lemma centeredRatio_eq (t : ℤ) : centeredRatio v t=
    rescale (↑(v^t):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K)*
      (shiftedElementary v t)⁻¹) := by
  have hc := shiftedElementary_constant v t
  unfold shiftedElementary at hc
  unfold centeredRatio shiftedElementary
  rw [map_mul,map_mul,rescale_inv_of_const_one _ _ (constant_elementary _ _),
    rescale_inv_of_const_one _ _ hc,rescale_rescale,rescale_rescale]
  congr 1
  · rw [←Units.val_mul,←zpow_add]
    congr 2
    ring_nf
  · rw [←Units.val_mul,←zpow_add]
    congr 3
    ring_nf
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma read_pure_monomial_shift
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (m : M) (j : ℕ) :
    readFiber v Ω k p hp (m+j • p)
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω m)))=coeff j (centeredRatio v (Ω p m)) := by
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp m]
  change (expandZero ((Finsupp.single (off k p hp m)
    (centeredScalar v (k m) (Ω p m)*(pureRatio v (Ω p m):RatFunc K)))
      (off k p hp (m+j • p)))).coeff (k (m+j • p))*
        (↑(v^(k (m+j • p)*complementAlpha k p Ω (off k p hp (m+j • p)))):K)=_
  simp only [map_add,map_nsmul,off_p,smul_zero,add_zero,hp,nsmul_eq_mul,mul_one,
    Finsupp.single_eq_same,complement_pairing Ω hΩ k p hp m]
  rw [map_mul,show expandZero (centeredScalar v (k m) (Ω p m))=
      HahnSeries.single (k m) (↑(v^(-k m*Ω p m)):K) by
      simpa using expand_centeredScalar v (k m) (Ω p m) (1:K),
    expandedPure_ratio v hq]
  rw [add_comm (k m),HahnSeries.coeff_single_mul_add,HahnSeries.ofPowerSeries_apply_coeff,
    centeredRatio_eq,coeff_rescale]
  rw [mul_assoc, mul_comm (coeff j _),←mul_assoc,←Units.val_mul,←zpow_add]
  rw [show -k m*Ω p m+((j:ℤ)+k m)*Ω p m=(Ω p m)*(j:ℤ) by ring,
    zpow_mul,zpow_natCast,Units.val_pow_eq_pow_val]
include hΩ in
lemma old_pure_coeff (m : M) (j : ℕ) :
    coeff j ((rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).val*PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).inv)=
      Torus.monomial v Ω (m+j • p) (coeff j (centeredRatio v (Ω p m))) := by
  rw [ray_adjoint v Ω hΩ,ray_twisted_coefficient v Ω hΩ]
  rfl
include hΩ in
lemma rational_pure_old_coefficient
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (m : M) (j : ℕ) :
    readFiber v Ω k p hp (m+j • p)
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω m)))=
    (coeff j ((rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).val*PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
        (constant_elementary _ _)).inv)) (m+j • p) := by
  rw [read_pure_monomial_shift v Ω hΩ k p hp hq,old_pure_coeff v Ω hΩ]
  exact (Finsupp.single_eq_same).symm
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma mul_X_coeff (f : Torus v Ω) (r m : M) :
    (f*Torus.X v Ω m) (r+m)=f r*(↑(v^(Ω r m)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [add_mul,Finsupp.add_apply,hf,hg]
  | single t a=>
    change (Torus.monomial v Ω t a*Torus.monomial v Ω m 1) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial]
    · simp [Torus.monomial,Ne.symm ht]

lemma X_mul_coeff (f : Torus v Ω) (r m : M) :
    (Torus.X v Ω m*f) (r+m)=f r*(↑(v^(Ω m r)):K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simpa only [mul_add,Finsupp.add_apply,hf,hg] using (_root_.add_mul (f r) (g r) _).symm
  | single t a=>
    change (Torus.monomial v Ω m 1*Torus.monomial v Ω t a) (r+m)=_
    rw [Torus.monomial_mul_monomial]
    by_cases ht : t=r
    · subst t; simp [Torus.monomial,add_comm]
    · have hmt : m+t≠r+m:=by intro hh; apply ht; simpa only [add_comm m t,add_right_cancel_iff] using hh
      simp [Torus.monomial,Ne.symm ht,Ne.symm hmt]

include v Ω in
lemma central_support_zero
    (hv : Function.Injective (fun z : ℤ=>(↑(v^z):K)))
    (hΩ : ∀m,Ω m m=0) (hnd : ∀r≠0,∃m,Ω r m≠0)
    (f : Torus v Ω) (hf : ∀m,f*Torus.X v Ω m=Torus.X v Ω m*f) :
    ∀r≠0,f r=0 := by
  intro r hr
  obtain ⟨m,hm⟩:=hnd r hr
  have H:=congrArg (fun t : Torus v Ω=>t (r+m)) (hf m)
  rw [mul_X_coeff,X_mul_coeff] at H
  by_contra hf
  have he : Ω r m=Ω m r:=hv (mul_left_cancel₀ hf H)
  have hs:=alternating_skew Ω hΩ r m
  omega
end
end ElementaryPositivity.QuantumTorus

end

end OAI
