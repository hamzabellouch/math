import OAI.NumberTheory.DirichletL.Moments.SmoothedRetainedSource
import OAI.NumberTheory.DirichletL.Moments.SecondSourceCost
import OAI.NumberTheory.DirichletL.Moments.SourceRectangle
import OAI.NumberTheory.DirichletL.Moments.CommonRawScale

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalRetainedSource
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0<P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0<D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentSmoothedRetainedSource.source_plain_to_smoothed_retained
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0<C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=>S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=>S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)<Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0<T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤pref:=by dsimp [pref];positivity
  change pref*_≤pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=>S (Sum.inl i.val))
        (fun i I hI=>hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
        (fun i=>hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=>hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0<D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0<E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=>S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=>Wslot i.val)
      (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end SevenEighths.CenteredMomentCanonicalRetainedSource

end

end OAI
