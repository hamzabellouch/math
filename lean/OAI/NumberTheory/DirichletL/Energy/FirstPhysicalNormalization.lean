import OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy
import OAI.NumberTheory.DirichletL.Moments.FirstWindowBudgets

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceEnergy CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource

lemma window_pair_le (J₁ J₂ : ℕ) (t L R H : ℝ) (hH : 0 ≤ H)
    (hL : L ≤ H) (hR : R ≤ H) :
    windowBudget J₁ t L * windowBudget J₂ t R ≤
      H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hs : Real.sqrt L * Real.sqrt R ≤ H := by
    calc
      _ ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = H := Real.mul_self_sqrt hH
  have hp := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
      exact mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos t).le _)
        (profileMoment_nonneg _)) (profileMoment_nonneg _))
  convert hp using 1 <;> simp only [windowBudget, pow_add] <;> ring

theorem pairedBudget_le_cap (J₁ J₂ : ℕ) (t H : ℝ) (EL ER : Fin 4 → ℝ)
    (hH : 0 ≤ H) (hL : ∀ i, EL i ≤ H) (hR : ∀ j, ER j ≤ H) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh : pairedBudget J₁ J₂ t EL ER ≤
      ∑ _i : Fin 4, ∑ _j : Fin 4,
        H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      window_pair_le J₁ J₂ t (EL i) (ER j) H hH (hL i) (hR j)))
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

theorem pairedBudget_le_powers (J₁ J₂ : ℕ) (t Z F Mdecl M₀ ell : ℝ)
    (lossL lossR EL ER : Fin 4 → ℝ) (hZ : 1 ≤ Z) (hF : 0 ≤ F)
    (hL : ∀ i, EL i ≤ F * Z ^ (Mdecl - M₀ + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^ (Mdecl - M₀ + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * F * Z ^ (Mdecl - M₀ + ell) * heightEnvelope t ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  have hcap := pairedBudget_le_cap J₁ J₂ t (F * Z ^ (Mdecl - M₀ + ell)) EL ER
    (mul_nonneg hF (Real.rpow_nonneg (by linarith) _))
    (fun i => (hL i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellL i])) hF))
    (fun j => (hR j).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellR j])) hF))
  simpa only [mul_assoc] using hcap

theorem physical_power_identity (Z K q Mdecl ell : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hq : 0 < q) :
    K * q * Z ^ (Mdecl - (Real.logb Z K + Real.logb Z q) + ell) =
      Z ^ (Mdecl + ell) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hKq : K * q = Z ^ (Real.logb Z K + Real.logb Z q) := by
    rw [Real.rpow_add hz, Real.rpow_logb hz hZ.ne' hK, Real.rpow_logb hz hZ.ne' hq]
  rw [hKq, ← Real.rpow_add hz]
  congr 1
  ring

lemma character_power_identity (η : Character) (Z K Mdecl ell : ℝ)
    (hZ : 1 < Z) (hK : 0 < K) :
    K * (η.modulus.absNorm : ℝ) *
      Z ^ (Mdecl - (Real.logb Z K + Real.logb Z (η.modulus.absNorm : ℝ)) + ell) =
      Z ^ (Mdecl + ell) := by
  apply physical_power_identity Z K _ Mdecl ell hZ hK
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

lemma heightEnvelope_le (t : ℝ) :
    heightEnvelope t ≤ (1 + 2 * Real.pi) ^ 2 * (1 + ‖t‖) := by
  unfold heightEnvelope
  nlinarith [norm_nonneg t, Real.pi_pos, mul_nonneg (norm_nonneg t) Real.pi_pos.le]

lemma heightEnvelope_pow_le (J : ℕ) (t : ℝ) :
    heightEnvelope t ^ J ≤ (1 + 2 * Real.pi) ^ (2 * J) * (1 + ‖t‖) ^ J := by
  have hh := pow_le_pow_left₀ (heightEnvelope_pos t).le (heightEnvelope_le t) J
  simpa only [mul_pow, ← pow_mul] using hh

def normalizationConstant (lowerProduct : ℝ) : ℝ :=
  16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost

lemma normalizationConstant_pos (lowerProduct : ℝ) (hlower : 0 < lowerProduct) :
    0 < normalizationConstant lowerProduct := by
  unfold normalizationConstant
  exact mul_pos (mul_pos (by norm_num) (div_pos (Real.exp_pos _) hlower))
    fixedPresentationCost_pos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_le (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hbudget := pairedBudget_le_powers J₁ J₂ s.t Z F Mdecl
    (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) ell
    lossL lossR EL ER hZ.le hF hL hR hellL hellR
  have hsource := sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
  have hden := div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hlower hsupport
  have hmass : 0 ≤ (s.η.modulus.absNorm : ℝ) := Nat.cast_nonneg _
  have hpresent := fixedPresentationCost_pos.le
  have hsource' : sourceFactor s a₁ a₂ K ≤
      (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost * K *
        (s.η.modulus.absNorm : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden hpresent) hK.le) hmass
  have hbound := (mul_le_mul_of_nonneg_left hbudget hsource).trans
    (mul_le_mul_of_nonneg_right hsource'
      (show 0 ≤ 16 * F * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell) *
          heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
        have hp₁ := profileMoment_nonneg J₁
        have hp₂ := profileMoment_nonneg J₂
        have hh := (heightEnvelope_pos s.t).le
        have hz := zero_lt_one.trans hZ
        positivity))
  apply hbound.trans_eq
  dsimp [normalizationConstant]
  have hid := character_power_identity s.η Z K Mdecl ell hZ hK
  calc
    _ = (16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost) * F *
        (K * (s.η.modulus.absNorm : ℝ) * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell)) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by ring
    _ = _ := by rw [hid]

def polynomialConstant (lowerProduct : ℝ) (J₁ J₂ : ℕ) : ℝ :=
  normalizationConstant lowerProduct * (1 + 2 * Real.pi) ^ (2 * (J₁ + J₂))

lemma polynomialConstant_pos (lowerProduct : ℝ) (J₁ J₂ : ℕ)
    (hlower : 0 < lowerProduct) : 0 < polynomialConstant lowerProduct J₁ J₂ := by
  exact mul_pos (normalizationConstant_pos lowerProduct hlower) (pow_pos (by positivity) _)

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_polynomial (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
        (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh := sourceFactor_pairedBudget_le lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR hellL hellR
  have hm₁ := profileMoment_nonneg J₁
  have hm₂ := profileMoment_nonneg J₂
  have hconst := (normalizationConstant_pos lowerProduct hlower).le
  have hz := zero_lt_one.trans hZ
  apply hh.trans
  calc
    _ ≤ normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        ((1 + 2 * Real.pi) ^ (2 * (J₁ + J₂)) * (1 + ‖s.t‖) ^ (J₁ + J₂)) *
        profileMoment J₁ * profileMoment J₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (heightEnvelope_pow_le (J₁ + J₂) s.t)
          (by positivity)) hm₁) hm₂
    _ = _ := by unfold polynomialConstant; ring

theorem uniform_source_normalization (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ),
    0 < a₁ → 0 < a₂ → 0 < K → 1 < Z → 0 ≤ F →
    lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
    (∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
    (∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
    (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      C * F * Z ^ (Mdecl + ell) * (1 + ‖s.t‖) ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  refine ⟨polynomialConstant lowerProduct J₁ J₂,
    polynomialConstant_pos lowerProduct J₁ J₂ hlower, ?_⟩
  intro ι _ _ s a₁ a₂ K Z F Mdecl ell lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR
  exact sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceMass CenteredMomentFirstNonexceptionalWeightSum
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_physical_mass_of_columnBounds (W : 𝓢(ℝ, ℂ)) (J₁ J₂ : ℕ)
    (hi : ι → ℝ) (b₁ b₂ B ξ ε lowerProduct : ℝ)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ) (hε : 0 < ε) (hlower : 0 < lowerProduct) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ s : Input ι, ∀ R seed : Ideal HeckeFamily.O,
      Squarefree seed → seed ≠ 0 → (∀ i, |s.hi i| ≤ hi i) → |s.b₁| ≤ b₁ → |s.b₂| ≤ b₂ →
      ∀ a₁ a₂ K : ℝ, 0 < a₁ → 0 < a₂ → 0 < K →
      lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
      (∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x, s.W₂ x ≠ 0 → a₂ ≤ x) →
      CenteredMomentExceptionalAmplitudePair.volume s.toData ≤ Z ^ B → K⁻¹ ≤ Z ^ B →
      ∀ (F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ), 0 ≤ F →
      (∀ i, 0 ≤ EL i) → (∀ j, 0 ≤ ER j) →
      (∀ i, EL i ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
      (∀ j, ER j ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
      (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
      (∀ p : Labels s R seed, ∀ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀ n : SourceBlocks s R seed K Z ξ p E,
        originalBlock s R seed W K Z ξ p E n ≠ 0 →
          ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val)) →
      physicalMass s R seed CenteredMomentSecondHeightFamily.fixedBadMask 1 W K Z ξ /
          CenteredMomentExceptionalAmplitudePair.volume s.toData ≤
        C * F * Z ^ (Mdecl + ell + ε) / (seed.absNorm : ℝ) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  obtain ⟨Cb, hCb, hbound⟩ := actual_physical_mass W J₁ J₂ hi b₁ b₂ B ξ ε hB hξ hε
  refine ⟨Cb * polynomialConstant lowerProduct J₁ J₂,
    mul_pos hCb (polynomialConstant_pos lowerProduct J₁ J₂ hlower), ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with Z hbound hZ
  intro s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hsupport hs₁ hs₂ hV hKi
    F Mdecl ell lossL lossR EL ER hF hEL hER hL hR heL heR hcols
  have hphysical := hbound s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK
    hs₁ hs₂ hV hKi EL ER hEL hER hcols
  have hnormal := sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z
    F Mdecl ell J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR heL heR
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) := by positivity
  calc
    _ ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) * sourceFactor s a₁ a₂ K *
        pairedBudget J₁ J₂ s.t EL ER := hphysical
    _ = (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER) := by ring
    _ ≤ (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂) :=
      mul_le_mul_of_nonneg_left hnormal hp
    _ = _ := by
      rw [show Z ^ (Mdecl + ell + ε) = Z ^ (Mdecl + ell) * Z ^ ε from
        Real.rpow_add hz (Mdecl + ell) ε]
      ring

end SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization

end

end OAI
