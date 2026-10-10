import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuantumTorusTrace
import OAI.Combinatorics.Chromatic.Walls.WallUnits

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance raySeriesAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

noncomputable def raySeries (a : M) (f : PowerSeries R) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun n=>Torus.monomial v Ω (n • a) (coeff n f))
@[simp] lemma coeff_raySeries (a : M) (f : PowerSeries R) (n : ℕ) :
    coeff n (raySeries v Ω a f)=Torus.monomial v Ω (n • a) (coeff n f) := by
  rw [raySeries,coeff_mk]
lemma raySeries_one (a : M) : raySeries v Ω a 1=1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_raySeries,coeff_one,coeff_one]
  split_ifs with hn
  · subst n
    rw [zero_nsmul]
    rfl
  · exact Torus.monomial_zero v Ω _
lemma monomial_sum {α : Type*} (s : Finset α) (m : M) (f : α → R) :
    Torus.monomial v Ω m (∑i∈s,f i)=∑i∈s,Torus.monomial v Ω m (f i) := by
  change Finsupp.singleAddHom m (∑i∈s,f i)=∑i∈s,Finsupp.singleAddHom m (f i)
  exact map_sum (Finsupp.singleAddHom m) f s
lemma raySeries_mul (a : M) (ha : Ω a a=0) (f g : PowerSeries R) :
    raySeries v Ω a (f*g)=raySeries v Ω a f*raySeries v Ω a g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_raySeries,coeff_mul,coeff_mul,monomial_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [coeff_raySeries,coeff_raySeries,Torus.monomial_mul_monomial]
  have hz : Ω (p.1 • a) (p.2 • a)=0 := by
    simp only [map_nsmul,AddMonoidHom.nsmul_apply,ha,nsmul_zero]
  rw [hz,zpow_zero,Units.val_one,mul_one,←add_nsmul,he]

lemma raySeries_twist (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries R) :
    raySeries v Ω a f*PowerSeries.C (Torus.X v Ω m)=
    PowerSeries.C (Torus.X v Ω m)*raySeries v Ω a (PowerSeries.rescale (↑(v^(2*Ω a m)):R) f) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_C,coeff_C_mul,coeff_raySeries,coeff_raySeries,coeff_rescale]
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,one_mul]
  rw [add_comm (n • a) m]
  congr 1
  have hn : Ω (n • a) m=(n:ℤ)*Ω a m := by simp [map_nsmul]
  have hn' : Ω m (n • a)= -((n:ℤ)*Ω a m) := by
    rw [alternating_skew Ω hΩ m (n • a),hn]
  rw [hn,hn']
  have he : (↑(v^(2*Ω a m)):R)^n * (↑(v^(-((n:ℤ)*Ω a m))):R)=↑(v^((n:ℤ)*Ω a m)) := by
    rw [←Units.val_pow_eq_pow_val,←zpow_natCast,←zpow_mul,←Units.val_mul,←zpow_add]
    congr 2
    ring
  calc
    coeff n f * ↑(v^((n:ℤ)*Ω a m)) = coeff n f * ((↑(v^(2*Ω a m)):R)^n * ↑(v^(-((n:ℤ)*Ω a m)))) := by rw [he]
    _ = ((↑(v^(2*Ω a m)):R)^n * coeff n f) * ↑(v^(-((n:ℤ)*Ω a m))) := by ring
end
end ElementaryPositivity.QuantumTorus
end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
local instance rayUnitAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def rayUnit (a : M) (ha : Ω a a=0) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (PowerSeries (Torus v Ω))ˣ where
  val:=raySeries v Ω a f
  inv:=raySeries v Ω a f⁻¹
  val_inv:=by
    rw [←raySeries_mul v Ω a ha,PowerSeries.mul_inv_cancel f (by rw [hf]; exact one_ne_zero),raySeries_one]
  inv_val:=by
    rw [←raySeries_mul v Ω a ha,PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero),raySeries_one]

lemma ray_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (rayUnit v Ω a (hΩ a) f hf).val * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a (hΩ a) f hf).inv=
    PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a
      (PowerSeries.rescale (↑(v^(2*Ω a m)):K) f * f⁻¹) := by
  change raySeries v Ω a f * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a f⁻¹=_
  rw [raySeries_twist v Ω hΩ,mul_assoc,←raySeries_mul v Ω a (hΩ a)]

lemma ray_inverse_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (rayUnit v Ω a (hΩ a) f hf).inv * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a (hΩ a) f hf).val=
    PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a
      (PowerSeries.rescale (↑(v^(2*Ω a m)):K) f⁻¹ * f) := by
  change raySeries v Ω a f⁻¹ * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a f=_
  rw [raySeries_twist v Ω hΩ,mul_assoc,←raySeries_mul v Ω a (hΩ a)]
end
end ElementaryPositivity.QuantumTorus
end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance positiveCoefficientsAddGroup : AddGroup (Torus PositiveRay.vUnit Ω) :=
  (Torus.instRing PositiveRay.vUnit Ω).toAddGroup

def PositiveCoefficients (f : PowerSeries (Torus PositiveRay.vUnit Ω)) : Prop :=
  ∀n m,∃p : LaurentPolynomial ℕ,PositiveRay.eval p=coeff n f m

lemma positive_scalar_monomial (m : M) (p : LaurentPolynomial ℕ) (x : M) :
    ∃q : LaurentPolynomial ℕ,PositiveRay.eval q=Torus.monomial PositiveRay.vUnit Ω m (PositiveRay.eval p) x := by
  classical
  by_cases h : m=x
  · subst x
    exact ⟨p,(Finsupp.single_eq_same).symm⟩
  · refine ⟨0,?_⟩
    rw [map_zero]
    exact (Finsupp.single_eq_of_ne (Ne.symm h)).symm

lemma positive_monomial_ray (a m : M) (F : PowerSeries (RatFunc ℚ))
    (hF : PositiveRay.Positive F) :
    PositiveCoefficients Ω (PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) * raySeries PositiveRay.vUnit Ω a F) := by
  obtain ⟨A,rfl⟩:=hF
  intro n x
  rw [coeff_C_mul,coeff_raySeries,Torus.X,Torus.monomial_mul_monomial,one_mul,coeff_map]
  have he : (↑(PositiveRay.vUnit ^ Ω m (n • a)):RatFunc ℚ)=PositiveRay.eval (LaurentPolynomial.T (Ω m (n • a))) := by
    rw [PositiveRay.eval_T]
    simp only [Units.val_zpow_eq_zpow_val,PositiveRay.vUnit,Units.val_mk0]
  rw [he,←map_mul]
  exact positive_scalar_monomial Ω (m+n • a) _ x

lemma positive_elementary_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (k : ℤ) (t : ℕ)
    (ht : Ω a m=(t:ℤ)) :
    PositiveCoefficients Ω (
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (elementary RationalRay.q (RationalRay.v^k))
        (constant_elementary _ _)).val * PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) *
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (elementary RationalRay.q (RationalRay.v^k))
        (constant_elementary _ _)).inv) := by
  rw [ray_adjoint PositiveRay.vUnit Ω hΩ]
  apply positive_monomial_ray
  have he : (↑(PositiveRay.vUnit^(2*Ω a m)):RatFunc ℚ)=RationalRay.q⁻¹^t := by
    rw [ht,inv_pow,RationalRay.q_pow,←zpow_neg]
    change RationalRay.v^(2*(t:ℤ))=RationalRay.v^(-(-2*(t:ℤ)))
    congr 1
    ring
  rw [he]
  exact RationalRay.elementary_ratio_positive k t

lemma complete_constant (q u : RatFunc ℚ) : constantCoeff (complete q u)=1 := by
  simp only [complete,PowerSeries.constantCoeff_inv,constant_elementary,inv_one]

lemma complete_inverse (q u : RatFunc ℚ) : (complete q u)⁻¹=elementary q (-u) := by
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by rw [complete_constant]; exact one_ne_zero)).mpr
  exact PowerSeries.mul_inv_cancel _ (by rw [constant_elementary]; exact one_ne_zero)

lemma positive_complete_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (k : ℤ) (t : ℕ)
    (ht : Ω a m=(t:ℤ)) :
    PositiveCoefficients Ω (
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (complete RationalRay.q (RationalRay.v^k))
        (complete_constant _ _)).val * PowerSeries.C (Torus.X PositiveRay.vUnit Ω m) *
      (rayUnit PositiveRay.vUnit Ω a (hΩ a) (complete RationalRay.q (RationalRay.v^k))
        (complete_constant _ _)).inv) := by
  rw [ray_adjoint PositiveRay.vUnit Ω hΩ]
  apply positive_monomial_ray
  have he : (↑(PositiveRay.vUnit^(2*Ω a m)):RatFunc ℚ)=RationalRay.q⁻¹^t := by
    rw [ht,inv_pow,RationalRay.q_pow,←zpow_neg]
    change RationalRay.v^(2*(t:ℤ))=RationalRay.v^(-(-2*(t:ℤ)))
    congr 1
    ring
  rw [he,complete_inverse]
  exact RationalRay.complete_ratio_positive k t
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
