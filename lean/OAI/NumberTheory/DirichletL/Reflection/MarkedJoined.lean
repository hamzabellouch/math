import OAI.NumberTheory.DirichletL.Reflection.MarkedOverlap

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma joined_whole_prime_mark {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (A : Ideal Eis) :
    (∏ i∈(markedSumSlots : Finset (ι⊕σ)),
      if Ideal.span {(G.sum S).generator i}∣A then (1:ℂ) else 0)=
      ∏ i, if S.ideal i∣A then (1:ℂ) else 0 := by
  unfold markedSumSlots
  rw [Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(G.sum S).generator_span]
  rfl

theorem actual_marked_row_eq_joined {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) :
    let Q₀ := Q*Ideal.span {(72:Eis)}
    let G := (freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S
    let j := Sum.elim
      (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ => 0)
    markedCompletedT (rowTwist Ψ m f z) W X (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
      markedCompletedT (D.fixedFactor Ψ Q*unmarkedSexticTwist G.generator G.generator_good j markedSumSlots)
        W X (fun A => ∏ i∈markedSumSlots, if Ideal.span {G.generator i}∣A then (1:ℂ) else 0) := by
  dsimp only
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2,
    free_row_eq_joined_unmarked D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S]
  congr 1
  funext A
  exact (joined_whole_prime_mark (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S A).symm

lemma joined_free_pairwise {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hdis : ∀ P : FreePrimeIndex I Q, ∀ i, S.ideal i≠P.val.val) :
    Pairwise (Function.onFun IsCoprime ((freePrimeFamily I Q hI).sum S).ideal) := by
  apply PrimeFamily.sum_pairwise (freePrimeFamily I Q hI) S
  · exact freePrimeIndex_pairwise_coprime I Q
  · exact hS
  · intro P i
    exact Ideal.isCoprime_of_isMaximal (hdis P i).symm

end
end SevenEighths.InverseReflectedPhase

end OAI
