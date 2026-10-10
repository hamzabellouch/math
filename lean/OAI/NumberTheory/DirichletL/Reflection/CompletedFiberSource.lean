import OAI.NumberTheory.DirichletL.Reflection.SourcePhysical
import OAI.NumberTheory.DirichletL.Reflection.OriginalActiveReflection
import OAI.NumberTheory.DirichletL.Reflection.FixedLevel

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

def residualOriginalData (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)) :=
  fiberGoodMaskRowData parents J F m hm hF.ne_zero hparents v
    ⟨reconstructFiberRow J (Ideal.span {m}*F) K.val,
      (originalResidualRows_reconstruct parents J (Ideal.span {m}*F) hparents K.val K.property).1⟩

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

abbrev originalResidualAdmissible : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),Admissible K := by
  intro K hK
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact rowResidualPart_admissible I _ hbad

variable (D : ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
    ∀ T : Finset σ,OriginalSplitCompletion (N:=(9:Eis)*c) (a:=(G h).a0) (c:=(G h).c0) (mode:=(G h).mode)
      ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
      (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
      (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
      lists hmax hgood T)

include hJ hQ hcQ hcop hdis hodd hperiod

theorem original_completed_residual_source
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W) (lo hi : ℝ) (hlo : 0<lo)
    (hsupp : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (w : ∀ i,lists i→ℂ) (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val))) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},
      fixedThetaRowCoeff c hc ((residualOriginalData parents J F hF m hm hparents v K).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
          frozenInactiveWeight J F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
            (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
            (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
            lists hmax hgood T (D h A T) (G h).shape (G h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val) W X w K := by
  rcases K with ⟨K,hK⟩
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have hI0 := hparents I (Finset.mem_filter.mp hI).1
  have hrec := reconstructFiberRow_of_original parents J (Ideal.span {m}*F) I hI hI0
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  let K : originalResidualRows parents J (Ideal.span {m}*F) :=
    ⟨rowResidualPart I (Ideal.span {m}*F),Finset.mem_image.mpr ⟨I,Finset.mem_filter.mpr ⟨hIp,hpow,hmask⟩,rfl⟩⟩
  let D0 := residualOriginalData parents J F hF m hm hparents v K
  have hz : Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)}=I := by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
    exact hrec
  have hS : ∀ p : ∀ i,lists i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily lists hmax hgood p).ideal) := by
    intro p i j hij
    apply Ideal.isCoprime_of_isMaximal
    intro he
    change (p i).val=(p j).val at he
    exact Finset.disjoint_left.mp (hdis hij) (p i).property (he.symm ▸ (p j).property)
  have he := actual_marked_active_reflection D0 J I F Q hJ hI0 hF hm
    (ConcretePrimeRowBridge.span_idealGenerator F) hz hbad
    (hcop K.val K.property) hpow.symm hmask.symm lists hmax hgood hS
    (fun p i => hodd i _ (p i).property) Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ.le G ((9:Eis)*c)
    (fun h => mul_dvd_mul_left (9:Eis) (G h).denominator_dvd)
    (fun p => markedRowFamily_period D0 (slotChoiceFamily lists hmax hgood p) Q
      (fun i => hperiod i _ (p i).property) c hcQ)
    (fun h A T b p => D h A T K b p)
    w W hWcompact lo hi hlo hsupp hW X hX
  exact he
end
end SevenEighths.InverseReflectedPhase

end OAI
