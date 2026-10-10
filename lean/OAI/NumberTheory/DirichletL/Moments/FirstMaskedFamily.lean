import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceBound

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily CenteredMomentSourceAllocationEnergy
open CenteredMomentAmplificationFamilyEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "fixedBadMask" => (goodLambda*(2:O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

def idealMask (u : O) (I : Ideal O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : O) (β : Ideal O → ℂ) (I : Ideal O) : ℂ := β I * idealMask u I

lemma idealMask_span (u n : O) : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary (u : O) (I : Ideal O) (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma row_mask_factor (η : Character) (u z n : O) :
    rowTwist (elementHom η) (fixedBadMask*u) 1 z n =
      (if IsCoprime n u then (1:ℂ) else 0)*
        rowTwist (elementHom η) fixedBadMask 1 z n := by
  have h := row_mask_mul η fixedBadMask u 1 z n
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda)
  simp only [one_mul] at h
  rw [h]
  split_ifs <;> simp

lemma rowWeight_mask_factor (η : Character) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_first_masked_character (η : Character) (e r : O)
    (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O, elementCoeff τ n =
        rowTwist (elementHom η) fixedBadMask 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n) ∧
      ∀ u n : O,
        rowTwist (elementHom η) (fixedBadMask*u) 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n =
        (if IsCoprime n u then (1:ℂ) else 0)*elementCoeff τ n := by
  obtain ⟨τ,hM,hτ,_⟩ := exists_first_character η fixedBadMask e r fixed_mask_ne_zero
    he hr (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) χ ξ
  refine ⟨τ,hM,hτ,?_⟩
  intro u n
  rw [row_mask_factor,hτ]
  ring

theorem exists_canonical_masked_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : Character) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma sourceGaussEnergy_congr (Q : Finset (Ideal O)) (c f c' f' : Ideal O → ℂ)
    (h : ∀ I ∈ Q, Supported I → c I*f I=c' I*f' I)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : sourceGaussEnergy Q c f W K=sourceGaussEnergy Q c' f' W K := by
  unfold sourceGaussEnergy
  congr 1
  funext I
  exact h I (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2

lemma first_source_energy (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy Q β
      (fun I => rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I)) W K =
    sourceGaussEnergy Q (maskedSource u β) (heightCoeff τ t) W K := by
  apply sourceGaussEnergy_congr
  intro I _ hI
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  simp only [maskedSource]
  ring

lemma maskedSource_eq_of_live (u : O) (β : Ideal O → ℂ)
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  funext I
  by_cases hi : β I=0
  · simp [maskedSource,hi]
  · simp [maskedSource,idealMask,h I hi]

lemma extracted_masked_coefficient (η : Character) (u : O) (C I : Ideal O)
    (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) (f : ℂ) :
    β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I)*f =
      (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I)*
        (rowWeight η fixedBadMask 1 1 t I*f) := by
  rw [map_mul,rowWeight_mask_factor η u I hI t]
  ring

lemma idealMask_generator (R I : Ideal O) :
    idealMask (idealGenerator R) I = if IsCoprime I R then 1 else 0 := by
  rw [idealMask,span_idealGenerator]

lemma maskedSource_punctured (u : O) (R : Ideal O) (β : Ideal O → ℂ) (I : Ideal O) :
    maskedSource u (fun J => if IsCoprime J R then β J else 0) I =
      if IsCoprime I R ∧ IsCoprime I (Ideal.span {u}) then β I else 0 := by
  unfold maskedSource idealMask
  split_ifs <;> simp_all

lemma first_gauss_row (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => β I*
        (rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I))) z =
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => maskedSource u β I*heightCoeff τ t I) z := by
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  dsimp only [maskedSource]
  ring

theorem exists_canonical_source_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      ∀ (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
      sourceGaussEnergy Q₁ β₁ (fun I => rowWeight η (fixedBadMask*u₁) 1 1 t I*
        (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₁ (maskedSource u₁ β₁) (heightCoeff τ₁ t) W K ∧
      sourceGaussEnergy Q₂ β₂ (fun I => rowWeight η (fixedBadMask*u₂) 1 1 t I*
        (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₂ (maskedSource u₂ β₂) (heightCoeff τ₂ t) W K := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩ := exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_⟩
  intro Q₁ Q₂ β₁ β₂ u₁ u₂ t W K
  constructor
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₁ I hI t,h₁ I hI t]
    dsimp only [maskedSource]
    ring
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₂ I hI t,h₂ I hI t]
    dsimp only [maskedSource]
    ring

def rayHeight (p : O) (k : ℕ) (τ : RayCharacter → Character) (t : ℝ) (I : Ideal O) : ℂ :=
  ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I

def extractedSource (η : Character) (u : O) (C : Ideal O)
    (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I

theorem exists_masked_radical_family (η : Character) (p : O)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) fixedBadMask p k) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
          rayHeight p k τ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*residualCharacter p k (primaryGenerator I)=
          idealMask u I*rayHeight p k τ t I) ∧
      ∀ (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p k (primaryGenerator I)) W K =
        sourceGaussEnergy Q (extractedSource η u C β t) (rayHeight p k τ t) W K := by
  obtain ⟨τ,hN,hτ⟩ := exists_radical_family η fixedBadMask p fixed_mask_ne_zero hs hpp
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) k
  refine ⟨τ,hN,hτ,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,mul_assoc,hτ I hI t]
    rfl
  · intro Q u C β t W K
    apply sourceGaussEnergy_congr
    intro I _ hI
    rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
    rfl

theorem exists_masked_error_source (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*
          residualCharacter p (errorMovingExponent n) (primaryGenerator I)=
            rayHeight p (errorMovingExponent n) τ t I) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K =
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (extractedSource η u C β t) (rayHeight p (errorMovingExponent n) τ t) W K := by
  obtain ⟨τ,hN,hτ,_,henergy⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,hτ,?_⟩
  intro S u C β t W K
  rw [←henergy (residualColumns S p hp (n+1)) u C β t W K]
  apply sourceGaussEnergy_congr
  intro I hI _
  rw [residual_column_active S p hp hs n hn I hI]

lemma idealMask_mul (u : O) (C I : Ideal O) :
    idealMask u (C*I)=idealMask u C*idealMask u I := by
  simp only [idealMask,IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

lemma extractedSource_whole_mask (η : Character) (u : O) (C : Ideal O)
    (hC : Supported C) (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) :
    extractedSource η u C β t I =
      maskedSource u β (C*I)*rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource,rowWeight_mask_factor η u C hC t,maskedSource,idealMask_mul]
  ring

lemma extracted_gauss_row (η : Character) (p : O) (k : ℕ) (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
        rayHeight p k τ t I)
    (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
          residualCharacter p k (primaryGenerator I)) z =
    ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p k) χ *
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  rw [←gaussPolynomial_allocation]
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
  simp only [rayHeight,Finset.mul_sum,extractedSource]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem exists_masked_error_rows (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O),
      let Q := residualColumns S p hp (n+1)
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q =>
          (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
            residualCharacter p (n+1) (primaryGenerator I)) z =
      ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p (errorMovingExponent n)) χ *
        gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  obtain ⟨τ,hN,hτ,_,_⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S u C β t z
  dsimp only
  rw [←extracted_gauss_row η p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) u C β t z]
  apply congrArg (fun c => gaussPolynomial Finset.univ
    (sourceGenerator (residualColumns S p hp (n+1)))
    (sourceGenerator_supported (residualColumns S p hp (n+1))) c z)
  funext I
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

lemma paired_gauss_rows (η τ₁ τ₂ : Character) (F₁ F₂ : O → ℂ)
    (h₁ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*F₁ (primaryGenerator I))
    (h₂ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*F₂ (primaryGenerator I))
    (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O) (t : ℝ) (z₁ z₂ : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => β₁ I*
        (rowWeight η (fixedBadMask*u₁) 1 1 t I*F₁ (primaryGenerator I))) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => β₂ I*
        (rowWeight η (fixedBadMask*u₂) 1 1 t I*F₂ (primaryGenerator I))) z₂) =
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => maskedSource u₁ β₁ I*heightCoeff τ₁ t I) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => maskedSource u₂ β₂ I*heightCoeff τ₂ t I) z₂) := by
  rw [first_gauss_row η τ₁ F₁ h₁ Q₁ β₁ u₁ t z₁,
    first_gauss_row η τ₂ F₂ h₂ Q₂ β₂ u₂ t z₂]

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI
