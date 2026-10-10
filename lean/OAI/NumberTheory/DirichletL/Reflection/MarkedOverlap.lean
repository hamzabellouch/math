import OAI.NumberTheory.DirichletL.Reflection.MarkedRow

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_zero_at_prime (I Q : Ideal Eis) (hI : Supported I)
    (P : FreePrimeIndex I Q) (n : Eis) (hn : n∈P.val.val) : freePrimeRow I hI Q n=0 := by
  unfold freePrimeRow
  change (∏ p : FreePrimeIndex I Q, _)=0
  apply Finset.prod_eq_zero (Finset.mem_univ P)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma primaryGenerator_mem_of_ideal_dvd (P A : Ideal Eis) (hPA : P∣A) : primaryGenerator A∈P := by
  by_cases hz : primaryGenerator A=0
  · rw [hz]
    exact Ideal.zero_mem _
  have ha0 : primaryGenerator A∈Ideal.span {primaryGenerator A} := Ideal.subset_span (by simp)
  have ha : primaryGenerator A∈A := ((primaryGenerator_spec A hz).1.le) ha0
  exact (Ideal.dvd_iff_le.mp hPA) ha

lemma free_row_whole_mark_overlap {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val) (A : Ideal Eis) :
    freePrimeRow I hI Q (primaryGenerator A)*
      (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  by_cases hd : S.ideal i∣A
  · have hn := primaryGenerator_mem_of_ideal_dvd (S.ideal i) A hd
    rw [heq] at hn
    rw [freePrimeRow_zero_at_prime I Q hI P _ hn,zero_mul]
  · have hz : (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hd]
    rw [hz,mul_zero]

theorem markedCompletedT_free_overlap_zero {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val)
    (φ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (φ*freePrimeRow I hI Q) W X
      (fun A => ∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  unfold markedCompletedT
  calc
    _ = ∑' n : Ideal Eis, ∑' b : Ideal Eis, (0:ℂ) := by
      apply tsum_congr
      intro n
      apply tsum_congr
      intro b
      rw [mul_comm φ (freePrimeRow I hI Q),summand_mul_fixed_twist]
      have hgen : primaryGenerator (n*b^3)=primaryGenerator n*(primaryGenerator b)^3 := by
        rw [primaryGenerator_mul,show primaryGenerator (b^3)=primaryGenerator b^3 from map_pow primaryGeneratorHom b 3]
      rw [← hgen]
      have hz := free_row_whole_mark_overlap I Q hI S P i heq (n*b^3)
      calc
        _ = summand φ W X n b*(freePrimeRow I hI Q (primaryGenerator (n*b^3))*
          (∏ j, if S.ideal j∣n*b^3 then (1:ℂ) else 0)) := by ring
        _ = 0 := by rw [hz,mul_zero]
    _ = 0 := by simp

end
end SevenEighths.InverseReflectedPhase

end OAI
