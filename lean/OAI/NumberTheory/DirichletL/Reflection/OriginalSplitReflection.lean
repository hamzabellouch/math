import OAI.NumberTheory.DirichletL.Reflection.MarkedTuples
import OAI.NumberTheory.DirichletL.Reflection.OriginalSlotSupport

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

theorem actual_marked_slot_split_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L,
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    let physical := fun (h : Eis⧸Ideal.span {c})
      (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))
      (T : Finset σ) (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L) =>
      mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*physical h A T
                  ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  dsimp only
  rw [actual_marked_tuple_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (fun p : ∀ i,L i => slotChoiceFamily L hmax hgood p) hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2
    c hc hcQ G N hN hNp C (fun p => ∏ i,w i (p i)) W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hs :=
    (original_supported_slot_sum D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
      L hmax hgood T w (fun p => mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro t ht
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
