import OAI.Combinatorics.PolynomialVacuum.Algebra.Projectors

namespace OAI

namespace PolynomialVacuumAlgebra

theorem spectral_multiply (a b c A B C : ℂ) :
    (a • Pzero + b • Pone + c • Ptwo) * (A • Pzero + B • Pone + C • Ptwo) =
    (a*A) • Pzero + (b*B) • Pone + (c*C) • Ptwo := by
  simp [add_mul,mul_add,smul_smul,
    Pzero_idempotent,Pone_idempotent,Ptwo_idempotent,Pzero_Pone,Pzero_Ptwo,
    Pone_Pzero,Pone_Ptwo,Ptwo_Pzero,Ptwo_Pone,mul_comm]

theorem exchange_numerator_unitarity (x y : ℂ) :
    exchangeNumerator x y * exchangeNumerator y x =
      (exchangeDenominator x y * exchangeDenominator y x) • (1 : Matrix Pair Pair ℂ) := by
  unfold exchangeNumerator
  rw [spectral_multiply]
  have h0 : ((t^2*y-x)*(T*x-y))*((t^2*x-y)*(T*y-x)) =
      exchangeDenominator x y * exchangeDenominator y x := by
    unfold exchangeDenominator; ring
  have h1 : ((T*y-x)*(t^2*x-y))*((T*x-y)*(t^2*y-x)) =
      exchangeDenominator x y * exchangeDenominator y x := by
    unfold exchangeDenominator; ring
  have h2 : ((t^2*y-x)*(T*y-x))*((t^2*x-y)*(T*x-y)) =
      exchangeDenominator x y * exchangeDenominator y x := by
    unfold exchangeDenominator; ring
  rw [h0,h1,h2,←smul_add,←smul_add,projectors_sum]

theorem exchange_numerator_regular (x : ℂ) :
    exchangeNumerator x x = exchangeDenominator x x • (1 : Matrix Pair Pair ℂ) := by
  unfold exchangeNumerator exchangeDenominator
  have h : (T*x-x)*(t^2*x-x)=(t^2*x-x)*(T*x-x) := mul_comm _ _
  rw [h,←smul_add,←smul_add,projectors_sum]

 

noncomputable def exchangeMatrix (x y : ℂ) : Matrix Pair Pair ℂ :=
  (exchangeDenominator x y)⁻¹ • exchangeNumerator x y

theorem exchange_unitarity (x y : ℂ)
    (hxy : exchangeDenominator x y ≠ 0) (hyx : exchangeDenominator y x ≠ 0) :
    exchangeMatrix x y * exchangeMatrix y x = 1 := by
  unfold exchangeMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,exchange_numerator_unitarity,smul_smul]
  have h : (exchangeDenominator x y)⁻¹ * (exchangeDenominator y x)⁻¹ *
      (exchangeDenominator x y * exchangeDenominator y x) = 1 := by field_simp
  rw [h,one_smul]

theorem exchange_regular (x : ℂ) (hxx : exchangeDenominator x x ≠ 0) :
    exchangeMatrix x x = 1 := by
  unfold exchangeMatrix
  rw [exchange_numerator_regular,smul_smul,inv_mul_cancel₀ hxx,one_smul]

end PolynomialVacuumAlgebra

end OAI
