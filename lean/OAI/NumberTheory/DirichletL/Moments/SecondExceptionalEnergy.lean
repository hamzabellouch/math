import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentSecondExceptionalEnergy
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentHeckeSlots CenteredMomentSecondExceptionalCount UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem actual_exceptional_slots_energy {ι:Type*} [Fintype ι]
    (Q:Ideal O) (hQ0:Q≠0) (hQ:Q≠⊤) (hQ72:Q≤Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩:=exceptional_slots_estimate (ι:=ι) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L):=by
    intro z hz
    exact hpoint Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end SevenEighths.CenteredMomentSecondExceptionalEnergy

end

end OAI
