import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.RadicalFamily

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentRadicalFamily CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily CenteredMomentAmplificationFamilyEnergy
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSecondChildProfile
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def radicalBound (η:Character)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

theorem radicalBound_error_power (η:Character)(m p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    (radicalBound η m p (errorMovingExponent n):ℝ)=
      ((η.modulus.absNorm:ℝ)*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm)*
        Z^(errorMoving p Z (n+1)):=by
  have hpow:=Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)
  rcases hn with rfl|rfl|rfl <;>
    norm_num only [radicalBound,errorMovingExponent,errorMoving,Nat.cast_mul,
      Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals simp only [ite_false,ite_true,Nat.one_ne_zero,eq_self,
    Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals rw [hpow]; rfl

theorem exists_radical_row (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤radicalBound η m p k ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=>p) (fun _=>hs) (fun _=>2*k)
      (fun _=>Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:Character)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayCharacter χ (primaryGenerator I):=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he:=idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayCharacter χ (primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:goodLambda^2∣p-1)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hN hτ using fun χ:RayCharacter=>exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family (η:Character)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:goodLambda^2∣p-1)(hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=>residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW

theorem original_errors_to_children {ι : Type*} [Fintype ι] (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI
