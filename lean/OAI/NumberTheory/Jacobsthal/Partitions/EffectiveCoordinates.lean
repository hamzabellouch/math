import OAI.NumberTheory.Jacobsthal.Estimates.EffectiveNumerator

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

noncomputable def effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℕ :=
  r.den*badPrimeProduct (fun t => (a t : ℤ)) r qf

noncomputable def effectiveIntercept (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : ℤ :=
  hitNumerator a r qf/(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)

theorem effectiveModulus_pos (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) : 0 < effectiveModulus a r qf :=
  Nat.mul_pos r.pos (badPrimeProduct_pos _ r qf)

theorem effectiveIntercept_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ)*effectiveIntercept a r qf = hitNumerator a r qf := by
  rw [effectiveIntercept,mul_comm]
  exact Int.ediv_mul_cancel (alignedCofactor_dvd_hitNumerator a r qf hq)

theorem hitNumerator_coprime_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (hitNumerator a r qf).natAbs.Coprime (effectiveModulus a r qf) :=
  (hitNumerator_coprime_den a r qf).mul_right (hitNumerator_coprime_bad a r qf hq)

theorem effectiveIntercept_coprime (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (effectiveIntercept a r qf).natAbs.Coprime (effectiveModulus a r qf) := by
  have hdiv : effectiveIntercept a r qf ∣ hitNumerator a r qf := by
    refine ⟨(alignedCofactor (fun t => (a t : ℤ)) r qf : ℤ),?_⟩
    rw [mul_comm]
    exact (effectiveIntercept_identity a r qf hq).symm
  exact (hitNumerator_coprime_effectiveModulus a r qf hq).of_dvd_left
    (Int.natAbs_dvd_natAbs.mpr hdiv)

theorem effective_coordinates_gcd (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    Int.gcd (effectiveIntercept a r qf) (effectiveModulus a r qf : ℤ) = 1 := by
  simpa only [Int.gcd_def,Int.natAbs_natCast] using (effectiveIntercept_coprime a r qf hq).gcd_eq_one

theorem zero_effectiveIntercept_modulus_one (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (hzero : effectiveIntercept a r qf = 0) : effectiveModulus a r qf = 1 := by
  have hh := effective_coordinates_gcd a r qf hq
  simpa only [hzero,Int.gcd_zero_left,Int.natAbs_natCast] using hh

theorem alignedCofactor_coprime_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    (alignedCofactor (fun t => (a t : ℤ)) r qf).Coprime (effectiveModulus a r qf) :=
  (alignedCofactor_coprime_den _ r qf hq).mul_right (alignedCofactor_coprime_bad _ r qf hq)

theorem denominator_full_cofactor (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    r.den*qf = alignedCofactor (fun t => (a t : ℤ)) r qf*effectiveModulus a r qf := by
  calc
    _ = r.den*(alignedCofactor (fun t => (a t : ℤ)) r qf*badPrimeProduct (fun t => (a t : ℤ)) r qf) :=
      congrArg (fun x : ℕ => r.den*x) (alignedCofactor_mul_bad (fun t => (a t : ℤ)) r qf hq).symm
    _ = _ := by unfold effectiveModulus;ring

end ErdosVarianceEffective

end

end Erdos970

end OAI
