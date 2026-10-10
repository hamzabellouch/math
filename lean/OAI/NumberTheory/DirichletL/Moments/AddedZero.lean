import OAI.NumberTheory.DirichletL.Moments.ZeroMode
import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import OAI.NumberTheory.DirichletL.Moments.Tail
import OAI.NumberTheory.DirichletL.Moments.Extraction

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle CenteredMomentExtraction
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

theorem pairFourier_one (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    pairFourier u 1 hu supported_one_element h =
      ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) h := by
  have hone (x : Residue (1 : O)) : supportedModulusCharacter 1 supported_one_element x = 1 := by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [supportedModulusCharacter_mk]
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using (idealRowHom n).map_one
  have aux (v : O) (hd : u ∣ v) (hv : v ≠ 0) (he : v = u) :
      (∑' x : Residue v, supportedModulusCharacter u hu (frequencyReduction u v hd x) *
        CubicEisenstein.quotientTrace v hv (Ideal.Quotient.mk _ h * x)) =
      residueGauss u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
        (Ideal.Quotient.mk _ h) := by
    subst v
    apply tsum_congr
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [frequencyReduction_mk]
  rw [← residueGauss_supported_mk u hu h]
  simpa only [pairFourier, pairResidue, hone, star_one, mul_one] using
    aux (u * 1) (dvd_mul_right u 1)
      (mul_ne_zero (supported_element_ne_zero u hu) (supported_element_ne_zero 1 supported_one_element))
      (mul_one u)

theorem gaussRow_zero_sixthRemainder (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) : sixthRemainder (Ideal.span {u}) = 1 := by
  have hg : ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) 0 ≠ 0 := by
    intro hz
    apply hzero
    simp only [gaussRow, hz, zero_div]
  have hm : pairFourier u 1 hu supported_one_element 0 ≠ 0 := by
    rwa [pairFourier_one]
  apply sixthRemainder_eq_of_prime_profile one_ne_zero
  intro P hP
  by_cases hmem : P ∈ normalizedFactors (Ideal.span {u})
  · obtain ⟨hmax, hlam, hodd⟩ := supported_factors_good _ hu P hmem
    let := hmax
    have hv := valuation_profile_of_mean_ne_zero u 1 hu supported_one_element hm P hlam hodd
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, valuation,
      normalizedFactors_one, Multiset.count_zero, Nat.zero_mod] using hv
  · simp only [valuation, Multiset.count_eq_zero.mpr hmem, normalizedFactors_one,
      Multiset.count_zero, Nat.zero_mod]

theorem gaussRow_zero_ideal_sixth_power (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) :
    sixthQuotient (Ideal.span {u}) ^ 6 = Ideal.span {u} := by
  simpa only [gaussRow_zero_sixthRemainder u hu hzero, one_mul] using
    sixth_normal_form (Ideal.span {u}) hu.1

theorem gaussRow_norm_le (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    ‖gaussRow u hu h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  have hb := CenteredMomentTail.normalizedResidueGauss_norm_le u
    (supported_element_ne_zero u hu) (supportedModulusCharacter u hu) (Ideal.Quotient.mk _ h)
  simpa only [normalizedResidueGauss, residueGauss_supported_mk,
    gaussRow] using hb

theorem squarefree_divisor_sixth_of_gauss_zero (u : O)
    (hu : Supported (Ideal.span {u})) (hzero : gaussRow u hu 0 ≠ 0)
    (s : Ideal O) (hs : Squarefree s) (hd : s ∣ Ideal.span {u}) :
    s ^ 6 ∣ Ideal.span {u} := by
  have he := gaussRow_zero_ideal_sixth_power u hu hzero
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

def idealGaussRow (I : Ideal O) (hI : Supported I) (h : O) : ℂ :=
  gaussRow (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h

lemma idealGaussRow_norm_le (I : Ideal O) (hI : Supported I) (h : O) :
    ‖idealGaussRow I hI h‖ ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hb := gaussRow_norm_le (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

lemma idealGaussRow_zero_sixthRemainder (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) : sixthRemainder I = 1 := by
  have hb := gaussRow_zero_sixthRemainder (primaryGenerator I)
    ((supported_span_primaryGenerator_iff I).mpr hI) hz
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

lemma tupleEntry_dvd {r : ℕ} (v : Fin r → Ideal O) (i : Fin r) : v i ∣ tupleProduct v :=
  Finset.dvd_prod_of_mem v (Finset.mem_univ i)

theorem tuple_product_fiber_card {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) :
    (S.filter (fun v => tupleProduct v = I)).card ≤ (idealDivisors I).card ^ r := by
  let T := S.filter (fun v => tupleProduct v = I)
  let f (v : T) : Fin r → idealDivisors I := fun i => ⟨v.val i, by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact tupleEntry_dvd v.val i⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, T] using
    Fintype.card_le_of_injective f hf

def idealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) : ℂ :=
  ∑ I : S, c I.val * idealGaussRow I.val (hS I.val I.property) 0

theorem idealAddedZero_norm_le (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖idealAddedZero S hS c‖ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) := by
  let F := S.filter (fun I => sixthRemainder I = 1)
  have hcount : (F.card : ℝ) ≤ 128 * Y ^ (1 / 6 : ℝ) := by
    simpa only [map_one, Nat.cast_one, div_one] using
      ideal_count_fixed_remainder F 1 one_ne_zero Y hY
        (fun I hI => (hS I (Finset.mem_filter.mp hI).1).1)
        (fun I hI => (Finset.mem_filter.mp hI).2)
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  have hb (I : S) : ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ ≤
      if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 := by
    by_cases hr : sixthRemainder I.val = 1
    · simp only [hr, ite_true, norm_mul]
      exact mul_le_mul (hc I.val I.property)
        ((idealGaussRow_norm_le _ _ _).trans (Real.sqrt_le_sqrt (hN I.val I.property)))
        (norm_nonneg _) hB
    · have hz : idealGaussRow I.val (hS I.val I.property) 0 = 0 := by
        by_contra hn
        exact hr (idealGaussRow_zero_sixthRemainder _ _ hn)
      simp only [hr, ite_false, hz, mul_zero, norm_zero, le_refl]
  calc
    ‖idealAddedZero S hS c‖ ≤ ∑ I : S,
        ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 :=
      Finset.sum_le_sum (fun I _ => hb I)
    _ = (F.card : ℝ) * (B * Real.sqrt Y) := by
      rw [Finset.sum_coe_sort S (fun I => if sixthRemainder I = 1 then B * Real.sqrt Y else 0)]
      rw [← Finset.sum_filter]
      simp only [F, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hB (Real.sqrt_nonneg _))

def normalizedIdealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (T : ℝ) : ℂ := (Real.sqrt T : ℂ)⁻¹ * idealAddedZero S hS c

theorem idealAddedZero_energy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y T : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖normalizedIdealAddedZero S hS c T‖ ^ 2 ≤ 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
  have hb := idealAddedZero_norm_le S hS c B Y hB hY hc hN
  have hp : (Y ^ (1 / 6 : ℝ)) ^ 2 * Y = Y ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY]
    norm_num only [Nat.cast_ofNat]
    conv_lhs => rhs; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add' hY (by norm_num : (1 / 3 : ℝ) + 1 ≠ 0)]
    norm_num
  have hs := sq_le_sq₀ (norm_nonneg (idealAddedZero S hS c)) (by positivity : 0 ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y))
  have hb2 := hs.mpr hb
  have hn : ‖normalizedIdealAddedZero S hS c T‖ ^ 2 = T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 := by
    simp only [normalizedIdealAddedZero, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T), mul_pow, inv_pow,
      Real.sq_sqrt hT.le]
  rw [hn]
  calc
    T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 ≤ T⁻¹ * ((128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hT.le)
    _ = 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY]
      rw [← hp]
      ring

def tupleCoefficient {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v

def tupleColumns {r : ℕ} (S : Finset (Fin r → Ideal O)) : Finset (Ideal O) :=
  S.image tupleProduct

lemma tupleColumns_supported {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) :
    ∀ I ∈ tupleColumns S, Supported I := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  exact hS v hv

theorem tupleCoefficient_norm_le {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖tupleCoefficient S β I‖ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
  calc
    ‖tupleCoefficient S β I‖ ≤ ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ S.filter (fun v => tupleProduct v = I), B :=
      Finset.sum_le_sum (fun v hv => hβ v (Finset.mem_filter.mp hv).1)
    _ = B * ((S.filter (fun v => tupleProduct v = I)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast tuple_product_fiber_card S I hI

theorem tuple_added_zero_energy (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin r → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin r → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hr')
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨16384 * (D ^ r) ^ 2, by positivity, ?_⟩
  intro S hS β B Y T hB hY hT hβ hN
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hδr : δ * (r : ℝ) = ε / 2 := by dsimp [δ]; field_simp
  have hc (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hI0 := (hS v hv).1
    have hn0 : (0 : ℝ) ≤ Ideal.absNorm (tupleProduct v) := Nat.cast_nonneg _
    calc
      ‖tupleCoefficient S β (tupleProduct v)‖ ≤
          B * ((idealDivisors (tupleProduct v)).card : ℝ) ^ r :=
        tupleCoefficient_norm_le S β B hB hβ _ hI0
      _ ≤ B * (D * (Ideal.absNorm (tupleProduct v) : ℝ) ^ δ) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hI0) _) hB
      _ = B * (D ^ r * (Ideal.absNorm (tupleProduct v) : ℝ) ^ (ε / 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn0, hδr]
      _ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
        gcongr
        exact hN v hv
  have hn (I : Ideal O) (hI : I ∈ tupleColumns S) : (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    exact hN v hv
  have he := idealAddedZero_energy (tupleColumns S) (tupleColumns_supported S hS)
    (tupleCoefficient S β) (B * (D ^ r * Y ^ (ε / 2))) Y T (by positivity) hY0.le hT hc hn
  have hy : (Y ^ (ε / 2)) ^ 2 * Y ^ (4 / 3 : ℝ) = Y ^ (4 / 3 + ε : ℝ) := by
    rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 16384 * (B * (D ^ r * Y ^ (ε / 2))) ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := he
    _ = (16384 * (D ^ r) ^ 2) * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
      rw [← hy]
      ring

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

lemma idealRectangle_norm_le (W₁ W₂ : ℝ → ℂ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) :
    ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖ ≤ 2 * B₁ * B₂ := by
  have hprod (x y : ℝ) : ‖W₁ x * W₂ y‖ ≤ B₁ * B₂ := by
    rw [norm_mul]
    exact mul_le_mul (hW₁ x) (hW₂ y) (norm_nonneg _) hB₁
  unfold idealRectangle
  exact (norm_sub_le _ _).trans ((add_le_add
    (hprod ((Ideal.absNorm I : ℝ) / X₁) ((Ideal.absNorm J : ℝ) / X₂))
    (hprod ((Ideal.absNorm I : ℝ) / Y₁) ((Ideal.absNorm J : ℝ) / Y₂))).trans_eq (by ring))

theorem originalCoefficient_norm_le (N : ℕ) (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ)
    (hBslot : ∀ j, 0 ≤ Bslot j) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Fin (N + 2) → Ideal O) (hv : tupleProduct v ≠ 0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  have hslots : ‖∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)‖ ≤ ∏ j, Bslot j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hWslot j _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hweight := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  have hrect := idealRectangle_norm_le W₁ W₂ B₁ B₂ hB₁ hB₂ hW₁ hW₂ X₁ X₂ Y₁ Y₂
    (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩)
  by_cases hs : s ∣ tupleProduct v
  · simp only [originalCoefficient, hs, ite_true, mul_one, norm_mul]
    have hsw := mul_le_mul hslots hweight (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
    simp only [mul_one] at hsw
    exact mul_le_mul hsw hrect (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
  · simp only [originalCoefficient, hs, ite_false, mul_zero, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)

lemma originalCoefficient_eq_zero_of_not_dvd (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Fin (N + 2) → Ideal O) (hs : ¬s ∣ tupleProduct v) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalCoefficient, hs, ite_false, mul_zero]

theorem original_added_zero_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O), c ≠ 0 →
      ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
      (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ),
      (∀ j, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j I, ‖ν j I‖ ≤ 1) → (∀ j x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Fin (N + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v)) (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
        (tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ s)) T‖ ^ 2 ≤
        C * ((∏ j, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := tuple_added_zero_energy (N + 2) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  apply he S hS _ _ Y T (mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)) hY hT _ hN
  intro v hv
  exact originalCoefficient_norm_le N c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s
    Bslot B₁ B₂ hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ v (hS v hv).1

theorem idealAddedZero_eq_gaussPolynomial (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) :
    idealAddedZero S hS c =
      gaussPolynomial (Finset.univ : Finset S)
        (fun I => primaryGenerator I.val)
        (fun I => (supported_span_primaryGenerator_iff I.val).mpr (hS I.val I.property))
        (fun I => c I.val) 0 := rfl

lemma idealGaussRow_zero_divisor_sixth (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) (s : Ideal O) (hs : Squarefree s) (hd : s ∣ I) :
    s ^ 6 ∣ I := by
  have hrem := idealGaussRow_zero_sixthRemainder I hI hz
  have he : sixthQuotient I ^ 6 = I := by
    simpa only [hrem, one_mul] using sixth_normal_form I hI.1
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

theorem idealAddedZero_nonzero_mask_norm (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Y : ℝ)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y)
    (hz : idealAddedZero S hS c ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hg : idealGaussRow I.val (hS I.val I.property) 0 ≠ 0 := by
    intro he
    exact hI (by rw [he, mul_zero])
  have hd : s ∣ I.val := by
    by_contra hn
    exact hI (by rw [hmask I.val I.property hn, zero_mul])
  have hpow := idealGaussRow_zero_divisor_sixth I.val (hS I.val I.property) hg s hs hd
  have hn := (norm_le_of_dvd (hS I.val I.property).1 hpow).trans (hN I.val I.property)
  simpa only [map_pow, Nat.cast_pow] using hn

theorem original_tupleCoefficient_mask (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (S : Finset (Fin (N + 2) → Ideal O)) (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ b₁ b₂ s) I = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply originalCoefficient_eq_zero_of_not_dvd
  rwa [(Finset.mem_filter.mp hv).2]

theorem added_zero_exponent (a s θ : ℝ) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6) :
    a / 3 + 4 * θ / 3 ≤ a - s + 2 * θ := by linarith

theorem added_zero_scale_identity (Z a θ : ℝ) (hZ : 0 < Z) :
    (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) = Z ^ (a / 3 + 4 * θ / 3) := by
  rw [← Real.rpow_neg hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
  congr 1
  ring

theorem idealAddedZero_source_energy (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (B Z a s θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 ≤ Z) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s + 2 * θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := idealAddedZero_energy S hS c B (Z ^ (a + θ)) (Z ^ a)
    hB (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hc hN
  calc
    _ ≤ 16384 * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) := he
    _ = 16384 * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3) := by
      rw [mul_assoc, added_zero_scale_identity Z a θ hZ0]
    _ ≤ 16384 * B ^ 2 * Z ^ (a - s + 2 * θ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (added_zero_exponent a s θ ha hs))
        (by positivity)

theorem idealAddedZero_nonzero_mask_dyad (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Z a s₀ θ : ℝ) (hZ : 1 < Z)
    (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ))
    (hz : idealAddedZero S hS c ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  obtain ⟨I, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hY : 1 ≤ Z ^ (a + θ) :=
    (norm_one_le (hS I.val I.property).1).trans (hN I.val I.property)
  have ha : 0 ≤ a + θ := (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hY)
  have hm := idealAddedZero_nonzero_mask_norm S hS c s hs hmask (Z ^ (a + θ)) hN hz
  have hp : Z ^ (s₀ * (6 : ℕ)) ≤ Z ^ (a + θ) := by
    rw [Real.rpow_mul_natCast hZ0.le]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hNs 6).trans hm
  have hsp := (Real.rpow_le_rpow_left_iff hZ).mp hp
  constructor <;> norm_num at hsp ⊢ <;> linarith

theorem idealAddedZero_source_energy_of_mask (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (B Z a s₀ θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s₀ + 2 * θ) := by
  by_cases hz : idealAddedZero S hS c = 0
  · simp only [normalizedIdealAddedZero, hz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨ha, hss⟩ := idealAddedZero_nonzero_mask_dyad S hS c s hs hmask Z a s₀ θ hZ hNs hN hz
    exact idealAddedZero_source_energy S hS c B Z a s₀ θ hB hZ.le ha hss hc hN

theorem actual_tuple_gauss_eq_columns {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) (β : (Fin r → Ideal O) → ℂ) :
    gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 =
    idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) := by
  let g (I : Ideal O) : ℂ := if hI : Supported I then idealGaussRow I hI 0 else 0
  have hl : gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 = ∑ v ∈ S, β v * g (tupleProduct v) := by
    rw [← Finset.sum_coe_sort S (fun v => β v * g (tupleProduct v))]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [g, dite_eq_left (hS v.val v.property), idealGaussRow]
  have hr : idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I * g I := by
    rw [← Finset.sum_coe_sort (tupleColumns S) (fun I => tupleCoefficient S β I * g I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [g, dite_eq_left (tupleColumns_supported S hS I.val I.property)]
  rw [hl, hr]
  symm
  simp only [tupleCoefficient, Finset.sum_mul]
  calc
    (∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g I) =
        ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ S, β v * g (tupleProduct v) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩) _

end SevenEighths.CenteredMomentAddedZero

end

end OAI
