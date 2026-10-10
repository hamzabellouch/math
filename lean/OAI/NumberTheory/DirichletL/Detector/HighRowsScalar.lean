import OAI.NumberTheory.DirichletL.Detector.UnramifiedScalar

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem row_even_kzero (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6∣6*r+5+1)]
  by_cases hm : r+1≤m
  · rw [ite_eq_left hm,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    ring
  · rw [ite_eq_right hm,ite_eq_right (by omega)]
    by_cases hb : j=5 ∧ m=r
    · rw [ite_eq_left hb,ite_eq_left (by omega),zero_sub]
    · rw [ite_eq_right hb,ite_eq_right (by omega),sub_self]

theorem row_nonprincipal_kzero (r m j d : ℕ) (hj : j<6) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 0 (j+6*m) =
      if j=d ∧ m=r then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(d+1)) 1
      else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6∣6*r+d+1)]
  rw [show 6*r+d+1=6*r+(d+1) by omega,actualSextic_pow_six_mul_add _ hg hc]
  have he : j+6*m=6*r+d ↔ j=d ∧ m=r := by omega
  simp only [he]

theorem row_squarefree_kone (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
        (if 6*r+1<j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_left (by omega : 6∣6*r)]
    congr 1
    by_cases hb : 6*r+1<j+6*m
    · rw [ite_eq_left hb,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
      ring
    · rw [ite_eq_right hb,ite_eq_right (by omega)]
      by_cases he : j=1 ∧ m=r
      · rw [ite_eq_left he,ite_eq_left (by omega),zero_sub]
      · rw [ite_eq_right he,ite_eq_right (by omega),sub_self]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem row_nonprincipal_kone (r m j d : ℕ) (hj : j<6) (hd0 : 0<d) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 1 (j+6*m) =
      if j=d+1 ∧ m=r then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
            primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^d) 1)
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_right (by omega : ¬6∣6*r+d),
      actualSextic_pow_six_mul_add _ hg hc]
    by_cases he : j=d+1 ∧ m=r
    · rw [ite_eq_left he,ite_eq_left (by omega)]
    · rw [ite_eq_right he,ite_eq_right (by omega),mul_zero]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end SevenEighths.ProbePrimePower
end

end OAI
