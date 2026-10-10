import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePowerFourier

namespace OAI

/-! The three local cubic Fourier factors. Positive powers are periodic
modulo three; the trivial cubic power is the exact Ramanujan factor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaPrimeFourier (p : Eisenstein) (hp : primaryPrime p) (n : ℕ)
    (h : Eisenstein) : ℂ :=
  ∑' y : Residues p, (cubicResidueChar p hp y)^n*
    residueFourierChar p hp.2.ne_zero (Ideal.Quotient.mk (modulus p) h*y)

lemma cubicThetaPrimeFourier_gaussSum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] {n : ℕ} (hn : n≠0) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp n h=
      gaussSum (cubicResidueChar p hp ^ n)
        ((residueFourierChar p hp.2.ne_zero).mulShift (Ideal.Quotient.mk (modulus p) h)) := by
  simp only [cubicThetaPrimeFourier,tsum_fintype,gaussSum,MulChar.pow_apply' _ hn,
    AddChar.mulShift_apply]

lemma cubicThetaPrimeFourier_period {p : Eisenstein} (hp : primaryPrime p)
    {n : ℕ} (hn : n≠0) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp (n+3) h=cubicThetaPrimeFourier p hp n h := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  rw [cubicThetaPrimeFourier_gaussSum hp (by omega),cubicThetaPrimeFourier_gaussSum hp hn,
    pow_add,cubicResidueChar_cube hp,mul_one]

lemma cubicThetaPrimeFourier_unit {p : Eisenstein} (hp : primaryPrime p)
    {n : ℕ} (hn : n≠0) (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFourier p hp n h=
      star ((cubicSymbol p h)^n)*cubicThetaPrimeFourier p hp n 1 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hh
  rw [cubicThetaPrimeFourier_gaussSum hp hn,cubicThetaPrimeFourier_gaussSum hp hn]
  have he : (Ideal.Quotient.mk (modulus p)) h=(u:Residues p) := hu.symm
  rw [he,gaussSum_mulShift_eq,← MulChar.star_apply',MulChar.pow_apply' _ hn]
  rw [hu,cubicResidueChar_mk,← cubicSymbol_prime hp,map_one,AddChar.mulShift_one]

theorem cubicThetaPrimeFourier_three {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaPrimeFourier p hp 3 h = if p ∣ h then (norm p:ℂ)-1 else -1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  rw [cubicThetaPrimeFourier_gaussSum hp (by norm_num),cubicResidueChar_cube hp]
  let a := Ideal.Quotient.mk (modulus p) h
  have ha : a=0 ↔ p ∣ h := by
    change Ideal.Quotient.mk (modulus p) h=0 ↔ p ∣ h
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hf : gaussSum (1 : MulChar (Residues p) ℂ)
      ((residueFourierChar p hp.2.ne_zero).mulShift a)=
      (∑ y : Residues p, residueFourierChar p hp.2.ne_zero (a*y))-1 := by
    unfold gaussSum
    simp only [AddChar.mulShift_apply]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [MulChar.map_zero,mul_zero,mul_one,AddChar.map_zero_eq_one,add_zero]
    rw [eq_sub_iff_add_eq]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0:Residues p))]
    simp only [mul_zero,AddChar.map_zero_eq_one]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (Finset.ne_of_mem_erase hy)),one_mul]
  change gaussSum (1 : MulChar (Residues p) ℂ)
    ((residueFourierChar p hp.2.ne_zero).mulShift a)=_
  rw [hf]
  simp_rw [mul_comm a]
  rw [AddChar.sum_mulShift a (residueFourierChar_isPrimitive p hp.2.ne_zero),ha]
  have hc : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [← Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  split_ifs <;> simp_all

end CubicFirstMoment

end

end OAI
