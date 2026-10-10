import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries
import OAI.Combinatorics.Chromatic.Walls.RationalCutIdentity

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open PowerSeries
noncomputable section
variable {K : Type*} [Field K]
lemma centeredPolynomial_coe (v : Kˣ) (t : ℕ) :
    (centeredPolynomial v t : PowerSeries K)=
      ∏i : Fin t,(1+PowerSeries.C (↑(v^centeredExponent t i):K)*PowerSeries.X) := by
  change Polynomial.coeToPowerSeries.ringHom (centeredPolynomial v t)=_
  rw [centeredPolynomial,map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp
lemma rescale_constant (a b : K) : rescale a (PowerSeries.C b)=PowerSeries.C b := by
  ext n
  rw [coeff_rescale,coeff_C]
  by_cases h:n=0
  · simp [h]
  · simp [h]
lemma centered_rescaled_ratio (v : Kˣ)
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (t : ℕ) :
    rescale (↑(v^(-(t:ℤ))):K)
      (rescale (↑(v^(2*(t:ℤ))):K)
        (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K)) *
        (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))⁻¹)=
      (centeredPolynomial v t : PowerSeries K) := by
  have Hs : (↑(v^(2*(t:ℤ))):K)=(↑(v^(-2:ℤ)):K)⁻¹^t := by
    rw [←Units.val_inv_eq_inv_val,←Units.val_pow_eq_pow_val,←zpow_neg,←zpow_natCast,←zpow_mul]
    congr 2
  rw [Hs,elementary_ratio _ _ (Units.ne_zero _) hq,map_prod,centeredPolynomial_coe]
  simp only [centeredExponent]
  rw [←Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_add,map_one,map_mul,rescale_constant,rescale_X]
  rw [←mul_assoc,←(PowerSeries.C (R:=K)).map_mul]
  congr 2
  have Hq : (↑(v^(-2:ℤ)):K)⁻¹^((i:ℕ)+1)=(↑(v^(2*(((i:ℕ)+1:ℕ):ℤ))):K) := by
    rw [←Units.val_inv_eq_inv_val,←Units.val_pow_eq_pow_val,←zpow_neg,←zpow_natCast,←zpow_mul]
    congr 2
  rw [Hq,←Units.val_mul,←Units.val_mul,←zpow_neg_one,←zpow_add,←zpow_add]
  congr 2
  push_cast
  ring_nf
end
end ElementaryPositivity.WallUnits

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma ray_twisted_coefficient (p m : M) (f : PowerSeries K) (j : ℕ) :
    coeff j (PowerSeries.C (Torus.X v Ω m)*raySeries v Ω p f)=
      Torus.monomial v Ω (m+j • p) (coeff j (rescale (↑(v^(-Ω p m)):K) f)) := by
  have hs : Ω m p= -Ω p m:=by
    have H:=hΩ (m+p)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  rw [coeff_C_mul,coeff_raySeries,Torus.X,Torus.monomial_mul_monomial,one_mul,coeff_rescale]
  congr 1
  rw [map_nsmul,hs,nsmul_eq_mul,←Units.val_pow_eq_pow_val,←zpow_natCast,←zpow_mul]
  rw [mul_comm (j:ℤ),mul_comm]
include hΩ in
lemma normalized_ray_coeff (p m : M) (t j : ℕ) (ht : Ω p m=(t:ℤ))
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) :
    coeff j ((rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
      (constant_elementary _ _)).val*PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω p (hΩ p) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
      (constant_elementary _ _)).inv)=
      Torus.monomial v Ω (m+j • p) ((centeredPolynomial v t).coeff j) := by
  rw [ray_adjoint v Ω hΩ,ray_twisted_coefficient v Ω hΩ,ht,
    centered_rescaled_ratio v hq t,Polynomial.coeff_coe]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
