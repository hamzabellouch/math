import OAI.NumberTheory.DirichletL.Detector.HighRowsScalar

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_step_six (Q G : ℂ) (r n j : ℕ) :
    gaussValuationTable Q G (r+6) (n+6) (j+6)=Q^6*gaussValuationTable Q G r n j := by
  have hd : 6∣r+6 ↔ 6∣r := by omega
  have hle : n+6+1≤j+6 ↔ n+1≤j := by omega
  have hle' : n+6≤j+6 ↔ n≤j := by omega
  have he : j+6=n+6 ↔ j=n := by omega
  simp only [gaussValuationTable,hd,hle,hle',he]
  split_ifs <;> simp [pow_add] <;> ring

theorem positiveScalar_step_six (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (n+6) k (j+6)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^6*
        positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  rw [positiveScalar_actual_table p hp hg hc,positiveScalar_actual_table p hp hg hc]
  have hp6 (a : ℕ) : actualSextic (Ideal.span {p}) hg^(a+6)=
      actualSextic (Ideal.span {p}) hg^a := by
    rw [pow_add,actualSextic_six _ hg hc,mul_one]
  by_cases hk : k=0
  · simp only [hk,ite_true]
    rw [show n+6+1=(n+1)+6 by omega,hp6,gaussValuationTable_step_six]
  · simp only [ite_eq_right hk]
    by_cases hk1 : k=1
    · subst k
      by_cases hj : 1≤j
      · rw [ite_eq_left ⟨rfl,by omega⟩,ite_eq_left ⟨rfl,hj⟩,hp6,
          show j+6-1=(j-1)+6 by omega,gaussValuationTable_step_six]
        ring
      · have hz : j=0 := by omega
        subst j
        simp only [show (1:ℕ)≤0+6 by omega,show ¬(1:ℕ)≤0 by omega,
          and_true,and_false,ite_true,ite_false,mul_zero]
        simp only [gaussValuationTable]
        split_ifs <;> simp_all ; omega
    · rw [ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem positiveScalar_zero_below (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) (hj : j<n) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · simp only [gaussValuationTable]
    split_ifs <;> simp_all <;> omega
  · have hbelow : j-1<n := by omega
    have hz : gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) n n (j-1)=0 := by
      simp only [gaussValuationTable]
      split_ifs <;> simp_all <;> omega
    rw [hz,mul_zero]
  · rfl

end SevenEighths.ProbePrimePower
end

end OAI
