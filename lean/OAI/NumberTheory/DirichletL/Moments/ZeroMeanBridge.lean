import OAI.NumberTheory.DirichletL.Moments.FirstLocalization
import OAI.NumberTheory.DirichletL.Moments.ZeroMode

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentZeroMeanBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentFirstDiscardedEnergy CenteredMomentFirstLocalization
local notation "O" => ActualEisensteinCubic.O

def quotientMean (a : O) (F : Residue a → ℂ) : ℂ :=
  (normValue a : ℂ)⁻¹ * ∑' x : Residue a, F x

lemma normValue_ne_zero (a : O) (ha : a ≠ 0) : normValue a ≠ 0 :=
  by
    rw [normValue_eq_embedding]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem quotientMean_pullback (a m : O) (ha : a ≠ 0) (hm : m ≠ 0)
    (h : a ∣ m) (F : Residue a → ℂ) :
    quotientMean m (fun x => F (frequencyReduction a m h x)) = quotientMean a F := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := right_ne_zero_of_mul hm
  have hh := conductorFourier_lift a b ha hb F 0
  simp only [mul_zero, conductorFourier, map_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one] at hh
  have he : frequencyReduction a (a*b) (dvd_mul_right a b) = conductorReduction a b := rfl
  unfold quotientMean
  rw [he, hh, normValue_mul, Complex.ofReal_mul]
  have ha' : (normValue a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero a ha)
  have hb' : (normValue b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero b hb)
  change ((normValue a : ℂ) * (normValue b : ℂ))⁻¹ *
    ((normValue b : ℂ) * _) = _
  field_simp

def dilationMask (e d : O) (F : Residue d → ℂ) (x : Residue (d*e)) : ℂ :=
  if frequencyReduction e (d*e) (dvd_mul_left e d) x = 0 then
    F (frequencyReduction d (d*e) (dvd_mul_right d e) x) else 0

@[simp] theorem dilationMask_mk (e d : O) (F : Residue d → ℂ) (z : O) :
    dilationMask e d F (Ideal.Quotient.mk _ z) =
      if e ∣ z then F (Ideal.Quotient.mk _ z) else 0 := by
  simp only [dilationMask, frequencyReduction_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem dilationMask_sum (e d : O) (he : e ≠ 0) (F : Residue d → ℂ) :
    (∑' x : Residue (d*e), dilationMask e d F x) =
      ∑' y : Residue d, F (Ideal.Quotient.mk _ e * y) := by
  have hi := scaledResidue_injective d e (d*e) rfl he
  have hz (x : Residue (d*e)) (hx : x ∉ Set.range (scaledResidue d e (d*e) rfl)) :
      dilationMask e d F x = 0 := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [dilationMask_mk]
    split_ifs with h
    · obtain ⟨y,rfl⟩ := h
      exact False.elim (hx ⟨Ideal.Quotient.mk _ y, rfl⟩)
    · rfl
  have hs : Function.support (dilationMask e d F) ⊆ Set.range (scaledResidue d e (d*e) rfl) := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro y
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, dilationMask_mk, ite_eq_left (dvd_mul_right e z), map_mul]

theorem quotientMean_dilation (e d : O) (he : e ≠ 0) (_hd : d ≠ 0)
    (F : Residue d → ℂ) (hF : ∀ x y, F (x*y) = F x * F y) :
    quotientMean (d*e) (dilationMask e d F) =
      (normValue e : ℂ)⁻¹ * F (Ideal.Quotient.mk _ e) * quotientMean d F := by
  rw [quotientMean, dilationMask_sum e d he]
  simp_rw [hF]
  rw [tsum_mul_left, normValue_mul, Complex.ofReal_mul, quotientMean]
  ring

theorem quotientMean_finite_sum {ι : Type*} [Fintype ι]
    (a : O) (ha : a ≠ 0) (F : Residue a → ℂ)
    (d : ι → O) (hd : ∀ i, d i ≠ 0) (G : (i : ι) → Residue (d i) → ℂ)
    (c : ι → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      ∑ i, c i * G i (Ideal.Quotient.mk _ z)) :
    quotientMean a F = ∑ i, c i * quotientMean (d i) (G i) := by
  let m := a * ∏ i, d i
  have hm : m ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have haM : a ∣ m := dvd_mul_right _ _
  have hdM (i : ι) : d i ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) a
  let := finite_quotient_span hm
  let : Fintype (Residue m) := Fintype.ofFinite _
  rw [← quotientMean_pullback a m ha hm haM F]
  have hh (x : Residue m) : F (frequencyReduction a m haM x) =
      ∑ i, c i * G i (frequencyReduction (d i) m (hdM i) x) := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [frequencyReduction_mk] using h z
  simp_rw [quotientMean, hh, tsum_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl := quotientMean_pullback (d i) m (hd i) hm (hdM i) (G i)
  rw [quotientMean, tsum_fintype] at hl
  rw [← Finset.mul_sum, mul_left_comm, hl]
  rfl

theorem row_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (z : O) (v : ℂ) :
    rowCoprimeMask P S z * v =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (if primeSubsetGenerator P E ∣ z then v else 0) := by
  rw [rowCoprimeMask_subsets, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  have hp (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_product_moebius P hp hinj E]
  have he : primeSubsetGenerator P E ∣ z ↔ ∀ i ∈ E, z ∈ P i := by
    rw [← Ideal.mem_span_singleton, primeSubsetGenerator, span_idealGenerator,
      mem_prime_product_iff P hinj E z]
  rw [he]
  split_ifs <;> ring

theorem quotientMean_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (a d : O) (ha : a ≠ 0) (hd : d ≠ 0)
    (F : Residue a → ℂ) (G : Residue d → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y)
    (hFG : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      rowCoprimeMask P S z * G (Ideal.Quotient.mk _ z)) :
    quotientMean a F =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
          G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G := by
  have h := quotientMean_finite_sum a ha F
    (fun E : S.powerset => d * primeSubsetGenerator P E.val)
    (fun E => mul_ne_zero hd (primeSubsetGenerator_ne_zero P E.val))
    (fun E => dilationMask (primeSubsetGenerator P E.val) d G)
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i∈E.val,P i) : ℂ)) (by
      intro z
      rw [hFG, row_mask_expansion P hinj S z]
      simp only [dilationMask_mk]
      exact (Finset.sum_coe_sort S.powerset _).symm)
  simp_rw [quotientMean_dilation _ _ (primeSubsetGenerator_ne_zero P _) hd G hG] at h
  simp only [← mul_assoc] at h
  exact h.trans (Finset.sum_coe_sort S.powerset (fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
      (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
        G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G))

theorem tripleResidue_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y) (x y : Residue (a*(b*r))) :
    tripleResidue a b r χa χb G (x*y) =
      tripleResidue a b r χa χb G x * tripleResidue a b r χa χb G y := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, tripleResidue_mk, tripleResidue_mk, tripleResidue_mk]
  exact tripleRow_mul a b r χa χb G hG u v

theorem original_pair_reduced_mask (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (z : O) :
    idealRowHom z I * star (idealRowHom z J) =
      rowCoprimeMask (fun P : CommonIndex I J => P.val)
        (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) z := by
  rw [original_pair_factor I J hI hJ]
  rw [common_ideal_pair_active (fun P : CommonIndex I J => P.val) (common_good I J hI)
    (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => (leftExponent_pos I J P).ne') (fun P _ => (rightExponent_pos I J P).ne')]
  have hactive : activeFunction I J hI (Ideal.Quotient.mk _ z) =
      finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z :=
    principalSexticRow_mk (activePrime I J) (activeCoprime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) (activeConductor I J)
      (span_finitePrimeModulus _) z
  simp only [tripleRow, hactive]
  convert mul_left_comm
    ((residualCharacter I J hI) (Ideal.Quotient.mk _ z) *
      (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z))
    (rowCoprimeMask (fun P : CommonIndex I J => P.val)
      (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z)
    (finiteSexticRow (activePrime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) z) using 1
  congr 2

theorem original_pair_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    quotientMean (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
      (CenteredMomentRowNorm.pairResidue _ _ hi hj) =
    ∑ E ∈ inactiveSubsets I J,
      (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)) := by
  dsimp only
  have h := quotientMean_mask_expansion (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (principalSupport Finset.univ (leftExponent I J) (rightExponent I J))
    (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
    (residualGenerator I J * (residualGenerator J I * activeConductor I J))
    (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
        (finitePrimeModulus_ne_zero _)))
    (CenteredMomentRowNorm.pairResidue _ _
      ((CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI)
      ((CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ))
    (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (tripleResidue_mul _ _ _ _ _ _ (principalSexticRow_mul _ _ _ _ _ _)) (by
      intro z
      rw [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
        CenteredMomentSourceRow.primary_span_supported J hJ, tripleResidue_mk]
      exact original_pair_reduced_mask I J hI hJ z)
  simpa only [inactiveSubsets, tripleResidue_mk] using h

theorem canonicalZeroTerm_eq_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroTerm I J hI hJ E W K = (K : ℂ) *
      ((UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))) *
      paperRadialFourier W 0 := by
  simp only [canonicalZeroTerm, tripleFourier, map_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, quotientMean, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem canonicalZeroPair_eq_original (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)‖^2 : ℝ) : ℂ) *
        CenteredMomentRowNorm.pairFourier (CompletedGauss.primaryGenerator I) (CompletedGauss.primaryGenerator J)
          hi hj 0) * paperRadialFourier W 0 := by
  dsimp only
  rw [canonicalZeroPair]
  simp_rw [canonicalZeroTerm_eq_mean]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← original_pair_mean I J hI hJ]
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem quotientMean_congr (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : Residue a → ℂ) (G : Residue b → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) = G (Ideal.Quotient.mk _ z)) :
    quotientMean a F = quotientMean b G := by
  have hh := quotientMean_finite_sum a ha F (fun _ : Unit => b) (fun _ => hb)
    (fun _ => G) (fun _ => (1 : ℂ)) (by intro z; simpa using h z)
  simpa using hh

theorem scaled_pairFourier_eq_mean (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (K : ℝ) :
    (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) =
      (K : ℂ) * quotientMean (a*b) (CenteredMomentRowNorm.pairResidue a b ha hb) := by
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem canonicalZeroPair_eq_generators (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (haI : Ideal.span {a} = I) (hbJ : Ideal.span {b} = J) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) *
        paperRadialFourier W 0 := by
  rw [canonicalZeroPair_eq_original, scaled_pairFourier_eq_mean, scaled_pairFourier_eq_mean]
  congr 2
  apply quotientMean_congr
    _ _ (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
  intro z
  simp only [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ, haI, hbJ]

theorem canonical_ideal_zero_sum (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      canonicalZeroPair I.val J.val (hS I.val I.property) (hS J.val J.property) W K) =
      CenteredMomentZeroMode.idealZeroEnergy S hS c K * paperRadialFourier W 0 := by
  rw [CenteredMomentZeroMode.idealZeroEnergy]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [canonicalZeroPair_eq_generators I.val J.val (hS I.val I.property) (hS J.val J.property)
    (CenteredMomentZeroMode.idealColumn S I) (CenteredMomentZeroMode.idealColumn S J)
    (CenteredMomentZeroMode.idealColumn_supported S hS I) (CenteredMomentZeroMode.idealColumn_supported S hS J)
    (CenteredMomentZeroMode.idealColumn_span S I) (CenteredMomentZeroMode.idealColumn_span S J)]
  ring

theorem zeroEnergy_eq_original (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) W K

theorem productColumnCoefficient_mul_whole (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (w : Ideal O → ℂ) (I : Ideal O) :
    productColumnCoefficient S T (fun J L => β J L * w (J*L)) I =
      productColumnCoefficient S T β I * w I := by
  rw [productColumnCoefficient, productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem zeroEnergy_product_eq (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S T : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
      (productColumnCoefficient S T β) W K =
    CenteredMomentZeroMode.productZeroEnergy S T hS hT
      (fun I J => β I J * CenteredMomentHeckeExpansion.rowWeight η m A 1 t (I*J)) K *
      paperRadialFourier W 0 := by
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2)
  have hp := CenteredMomentZeroMode.productColumns_supported S T hS hT
  have hs : CenteredMomentSourceRow.supportedColumns P = P := Finset.filter_eq_self.mpr hp
  have hh := zeroEnergy_eq_original η m A t P (productColumnCoefficient S T β) W K
  simp only [hs] at hh
  rw [hh]
  congr 1
  unfold CenteredMomentZeroMode.productZeroEnergy
  congr 1
  funext I
  exact (productColumnCoefficient_mul_whole S T β
    (CenteredMomentHeckeExpansion.rowWeight η m A 1 t) I).symm

theorem normalized_zeroEnergy_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeFamily.Character) (m A : O) (t : ℝ)
      (S T : Finset (Ideal O)) (_hS : ∀ I ∈ S, Supported I) (_hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I*J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
          (productColumnCoefficient S T β) W K‖ ≤
        C * K * B^2 * ‖paperRadialFourier W 0‖ * X^ε := by
  obtain ⟨C,hC,hc⟩ := CenteredMomentZeroMode.normalized_product_zero_mode_bound ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S T hS hT β W X K B hX hK hB hN hβ
  rw [zeroEnergy_product_eq η m A t S T hS hT]
  apply hc S T hS hT _ W X K B hX hK hB hN
  intro I hi J hj
  rw [norm_mul]
  exact (mul_le_mul (hβ I hi J hj)
    (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t (I*J)
      (mul_ne_zero (hS I hi).1 (hT J hj).1)) (norm_nonneg _) hB).trans_eq (mul_one B)

end SevenEighths.CenteredMomentZeroMeanBridge

end

end OAI
