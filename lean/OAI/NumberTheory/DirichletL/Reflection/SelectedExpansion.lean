import OAI.NumberTheory.DirichletL.Reflection.SourceSelection
import OAI.NumberTheory.DirichletL.Reflection.MarkedLevel

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

private theorem exists_original_controlled_source
    (c : Eis) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (hP : Pairwise (Function.onFun IsCoprime (Pall).ideal))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode) :
    ∀ h : Eis⧸Ideal.span {c}, ∃ CC : ∀ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N (G h).a0 (G h).c0 (G h).mode,
      ∀ B T, CC (markedActiveSet E B T)=
        originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C h B T) := by
  intro h
  exact exists_marked_source_selection E
    (fun A => ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    ((Pall).activeControlled hP c G N hN hNp h)
    (fun B T => originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C h B T))

private theorem original_controlled_source_sum
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    {N a c : Eis} {mode : Bool}
    (C : ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N a c mode)
    (CC : ∀ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      ControlledStratumArithmetic (fun i : A => (Pall).generator i.val) N a c mode)
    (hCC : ∀ B T, CC (markedActiveSet E B T)=
      originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T (C B T))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight (Pall).generator (Pall).generator_ne_zero
        (mixedPrimeFunction (Pall).generator (Pall).generator_good Jall markedSumSlots) A *
        mixedReflectedValue (CC A) s ((Pall).restrict A).generator_ne_zero hc
          ((Pall).restrict A).generator_good (fun i => Jall i.val)
          (activeMarks A markedSumSlots) W X) =
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
      mixedReflectedValue (C B T) s
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero hc
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
        (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
        (slotIndices B (PrimeIndex K) T) W X := by
  rw [original_fiber_inactive_sum D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S hSodd]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  rw [hCC B T]
  exact original_chosen_reflected_source_eq D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T
    (C B T) s hc W X

theorem original_selected_reflected_expansion
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ i, S.ideal i≠P.val.val)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1) (hQ₀ : Q₀≠0)
    (hφperiod : CanonicalCoefficientClass.FactorsModulo Q₀ φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q₀)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist (Pall).generator (Pall).generator_good Jall markedSumSlots) W X
      (fun A => ∏ i∈markedSumSlots, if Ideal.span {(Pall).generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hP : Pairwise (Function.onFun IsCoprime (Pall).ideal) :=
    joined_free_pairwise D.movingIdeal Q₀ D.movingSupported S hS hdis
  have hodd : ∀ i, ringChar (Eis⧸(Pall).ideal i)≠2 := by
    intro i
    cases i with
    | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
        (Multiset.mem_toFinset.mp P.val.property)).2.2
    | inr t => exact hSodd t
  have hj : ∀ i, Jall i<6 := by
    intro i
    cases i with
    | inl P => exact Nat.mod_lt _ (by norm_num)
    | inr t => norm_num
  have hchoose := exists_original_controlled_source D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S c G N hN hNp hP C
  choose CC hCC using hchoose
  rw [(Pall).marked_reflected_source_of_controlled hP hodd Jall hj markedSumSlots φ hφnorm Q₀ hQ₀ hφperiod
    c hc hcQ G N hN CC W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  exact original_controlled_source_sum D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S hSodd (C h) (CC h) (hCC h) (G h).shape (G h).denominator_ne_zero W X
end
end SevenEighths.InverseReflectedPhase

end OAI
