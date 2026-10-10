import OAI.NumberTheory.DirichletL.Reflection.ActualSelected
import OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
import OAI.NumberTheory.DirichletL.Reflection.WholePair

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
lemma sum_subtype_dite_decidable {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p]
    (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable {α : Type*} [Fintype α] (Sp : α→PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_tuple_reflection
    (hS : ∀ p,Pairwise (Function.onFun IsCoprime (Sp p).ideal))
    (hSodd : ∀ p i,ringChar (Eis⧸(Sp p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (Sp p) Q).ideal i))
    (C : ∀ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : α→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : α,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),∑ T : Finset σ,
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
          (∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm ((Sp p.val).ideal t):ℂ)⁻¹)*w p.val*
          mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex K) T) W X := by
  let good := fun p : α => ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val
  let row := fun p : α => markedCompletedT (rowTwist Ψ m f z) W X
    (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0)
  have hzrow (p : α) (hp : ¬good p) : row p=0 := by
    simp only [good,not_forall,not_not] at hp
    obtain ⟨P,i,he⟩ := hp
    exact actual_marked_row_overlap_zero D (Sp p) Ψ Q hmLam hm2 P i he W X
  have hrestrict : (∑ p : α,w p*row p)=∑ p : {p // good p},w p.val*row p.val := by
    calc
      _ = ∑ p : α,if h:good p then w p*row p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hg : good p
        · rw [dite_eq_left hg]
        · rw [dite_eq_right hg,hzrow p hg,mul_zero]
      _ = _ := (sum_subtype_dite_decidable good (fun p _ => w p*row p)).symm
  change (∑ p : α,w p*row p)=_
  rw [hrestrict]
  have he (p : {p // good p}) := actual_marked_selected_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (Sp p.val) (hS p.val) (hSodd p.val) p.property Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN
    (hNp p.val) (C p) W hWcompact lo hi hlo hsupp hW X hX
  dsimp only [row]
  simp_rw [he]
  simp only [Finset.mul_sum,frozenInactiveWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro p hp
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
