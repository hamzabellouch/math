import OAI.NumberTheory.DirichletL.Moments.RadialCenteredEnergy
import OAI.NumberTheory.DirichletL.Moments.ExceptionalCappedAmplitude

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentExceptionalCappedAmplitude
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma plain_norm_le_reduction (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (j:Fin 2):
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod₀ (fun i _=>hP i)))

lemma allocated_lower (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,1≤P i) (Z r X:ℝ) (hZ:0<Z) (hX:Z^r≤X) (j:Fin 2):
    Z^r/formalReductionFactor L a P≤X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)<Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

lemma remaining_volume (L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2)))
    (P:ι→ℝ) (hP:∀i,0<P i) (T:ℝ):
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).ne').mpr
  exact raw_scale_identity L a T P

 theorem actual_allocated_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι] [DecidableEq ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,1≤P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀(L:Ideal O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))),
      ∀t X₁ X₂ Y₁ Y₂ T r:ℝ,Z^r≤X₁ → Z^r≤X₂ → Z^r≤Y₁ → Z^r≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖residualCenteredRow (childCharacter η χ) m A z t S β P L a W₁ W₂ X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i:liveIndices L a,128*b i*Ms i)*
          (Real.sqrt ((T*∏i,P i)/formalReductionFactor L a P)/
            Z^(max (r-Real.logb Z (formalReductionFactor L a P)) 0)))^2:=by
  obtain ⟨J,hJ⟩:=actual_canonical_capped_energy a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hbound⟩:=hJ Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs L a t X₁ X₂ Y₁ Y₂ T r hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hp (i:ι):0<P i:=zero_lt_one.trans_le (hP i)
  have hred:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hp i))
  have hh:=hbound (liveIndices L a) Z hZ η χ C D hC U hQC hη m hm hmLam hm2 rows hrows hex hcond Cr M hCr hN
    (fun i=>S i) (fun i=>β i) (fun i=>P i) (fun i=>b i) (fun i=>Ms i)
    (fun i=>hp i) (fun i=>hb i) (fun i=>hMs i) (fun i=>hβ i) (fun i=>hNs i)
    t (X₁/Ideal.absNorm (selectedPlain L a 0)) (X₂/Ideal.absNorm (selectedPlain L a 1))
    (Y₁/Ideal.absNorm (selectedPlain L a 0)) (Y₂/Ideal.absNorm (selectedPlain L a 1))
    (T/selectedNorm L a) (Z^r/formalReductionFactor L a P)
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hred)
    (allocated_lower L a P hP Z r X₁ (zero_lt_one.trans hZ) hX₁ 0)
    (allocated_lower L a P hP Z r X₂ (zero_lt_one.trans hZ) hX₂ 1)
    (allocated_lower L a P hP Z r Y₁ (zero_lt_one.trans hZ) hY₁ 0)
    (allocated_lower L a P hP Z r Y₂ (zero_lt_one.trans hZ) hY₂ 1)
    (by rw [div_mul_div_comm,hXT];rfl) (by rw [div_mul_div_comm,hYT];rfl)
  rw [remaining_volume L a P hp T,max_raw_reduction Z _ r hZ hred] at hh
  exact hh

end SevenEighths.CenteredMomentAllocatedCenteredCapped

end

end OAI
