import OAI.NumberTheory.DirichletL.Reflection.MarkedTuples

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

lemma markedCompletedT_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0)
    (W : ℝ→ℂ) (X : ℝ) (mark : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ (m*B) f z) W X mark=
      markedCompletedT (rowTwist Ψ m f z) W X mark := by
  rw [rowTwist_absorb_puncture Ψ m B f z hmLam hm2 hΨzero]

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

lemma rowResidualPart_coprime_enlarged_period (I F Q : Ideal Eis) (m B : Eis)
    (hQ : Q∣Ideal.span {B}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m*B}*F)) := by
  apply rowResidualPart_coprime_period I F Q (m*B)
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_of_dvd_right hQ _

end
end SevenEighths.InverseReflectedPhase

end OAI
