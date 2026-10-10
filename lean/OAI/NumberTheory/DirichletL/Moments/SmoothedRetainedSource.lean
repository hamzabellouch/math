import OAI.NumberTheory.DirichletL.Moments.SourceRetainedEnergy
import OAI.NumberTheory.DirichletL.Moments.PositiveSummability

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSmoothedRetainedSource
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentSourceRetainedEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_smoothed_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
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
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let ω:=fun z:O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hω (z:O):0≤ω z:=by dsimp only [ω];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0<raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0<raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=>hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤_
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)/(raw*∏i,P i)=
      ω z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [ω]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows ω (fun z _=>hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>ω z*
    (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [ω]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=>mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end SevenEighths.CenteredMomentSmoothedRetainedSource

end

end OAI
