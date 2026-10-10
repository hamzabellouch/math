import OAI.NumberTheory.DirichletL.Descent.Widths
import OAI.NumberTheory.DirichletL.Descent.Basic

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma norm_one_le (I : Ideal O) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem physical_residual_width (I Q : Ideal O) (hI : I ≠ 0)
    (Z M O₀ H Ck CO CH : ℝ) (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hres : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)) :
    H ≤ M - O₀ + Real.log (CH * Ck * CO) / Real.log Z := by
  have hz0 : 0 < Z := by linarith
  have hp := (div_le_iff₀ hCO).mp hpow
  have hr := (div_le_iff₀ hCH).mp hres
  have hs : Z ^ (H + O₀) ≤ (CH * Ck * CO) * Z ^ M := by
    calc
      _ = Z ^ H * Z ^ O₀ := Real.rpow_add hz0 _ _
      _ ≤ ((Ideal.absNorm (rowResidualPart I Q) : ℝ) * CH) *
          ((Ideal.absNorm (rowPowerfulPart I) : ℝ) * CO) :=
        mul_le_mul hr hp (Real.rpow_nonneg hz0.le _) (by positivity)
      _ = (CH * CO) * ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowResidualPart I Q) : ℝ)) := by ring
      _ ≤ (CH * CO) * (Ideal.absNorm I : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using actual_residual_norm_width I Q hI) (by positivity)
      _ ≤ (CH * CO) * (Ck * Z ^ M) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have hl := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz0 _) hs
  rw [Real.logb_rpow hz0 (ne_of_gt hZ), Real.logb_mul (by positivity) (by positivity),
    Real.logb_rpow hz0 (ne_of_gt hZ)] at hl
  unfold Real.logb at hl
  linarith

theorem constant_log_error (C η : ℝ) (_hC : 0 < C) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → Real.log C / Real.log Z ≤ η := by
  refine ⟨max 2 (Real.exp (Real.log C / η)), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Z hZ
  have hz : 1 < Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have he : Real.exp (Real.log C / η) ≤ Z := (le_max_right _ _).trans hZ
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have hh := (div_le_iff₀ hη).mp hl
  nlinarith

def activeCharge (j : ℕ) (e : Fin 3) : ℤ :=
  if j = 4 then (if e = 2 then -2 else 1) else if j = 0 then 1 else 2

theorem activeCharge_le_two (j : ℕ) (e : Fin 3) : activeCharge j e ≤ 2 := by
  unfold activeCharge
  split_ifs <;> norm_num

theorem activeCharge_le_one (j : ℕ) (e : Fin 3) (hj : j = 0 ∨ j = 4) :
    activeCharge j e ≤ 1 := by
  rcases hj with rfl | rfl
  · simp [activeCharge]
  · simp only [activeCharge, ite_true]
    split_ifs <;> norm_num

theorem reflectionLocalCost_eq_charge (q : ℝ) (_hq : 0 < q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e = q ^ (activeCharge j e : ℝ) := by
  unfold reflectionLocalCost activeCharge
  split_ifs <;> norm_num [Real.rpow_neg, Real.rpow_two]

theorem surviving_local_piece (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (j : ℕ) (e : Fin 3) (n b : O)
    (hne : reflectedLocalPiece P hg j e n b ≠ 0) :
    (j ≠ 4 → e = 0) ∧ (j = 4 → e = 1 → n ∈ P) ∧
      (j = 4 → e = 2 → n ∉ P ∧ b ∈ P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    by_contra he
    exact hne (by simp [reflectedLocalPiece, hj, he])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])
  · intro hj he
    by_contra hn
    exact hne (by simp [reflectedLocalPiece, exceptionalPiece, hj, he, hn])

def normWidth (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

theorem reflectionConductorCost_pos {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    0 < reflectionConductorCost P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost
  positivity

theorem logb_reflectionConductorCost {ι : Type*} [Fintype ι]
    (Z : ℝ) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0) (j : ι → ℕ) (e : ι → Fin 3) :
    Real.logb Z (reflectionConductorCost P j e) = reflectionWidth Z P j e := by
  have hp := actual_ideal_norm_pos (∏ i, P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hP i))
  have hd (v : Fin 3) := actual_ideal_norm_pos (reflectionExtractedDivisor P j e v)
    (reflectionExtractedDivisor_ne_zero P hP j e v)
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold reflectionConductorCost reflectionWidth normWidth
  rw [Real.logb_div (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (hd 1).ne' (hd 0).ne', Real.logb_pow, Real.logb_pow]
  norm_num
  ring

theorem reflection_charge_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z : ℝ) (hZ : 1 < Z) :
    2 * normWidth Z (rowResidualPart I (B * F * R)) +
      reflectionWidth Z P (fun i => completedLocalExponent I F (P i)) e ≤
      normWidth Z B + 2 * normWidth Z I - normWidth Z (rowPowerfulPart I) +
        normWidth Z F + normWidth Z R := by
  have hi := actual_ideal_norm_pos I hI
  have hf := actual_ideal_norm_pos F hF
  have hb := actual_ideal_norm_pos B hB
  have hr := actual_ideal_norm_pos R hR
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hx := actual_ideal_norm_pos (rowResidualPart I (B * F * R))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) (B * F * R))
  have hc := reflectionConductorCost_pos P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e
  have hh := Real.logb_le_logb_of_le hZ (mul_pos (sq_pos_of_pos hx) hc)
    (actual_common_width_charge_label_puncture I F R B hI hF hR hB P hcop hpool hres e)
  rw [Real.logb_mul (by positivity) hc.ne', Real.logb_pow,
    logb_reflectionConductorCost Z P (fun i => NeZero.ne (P i)),
    Real.logb_mul (by positivity) hr.ne', Real.logb_mul (by positivity) hf.ne',
    Real.logb_mul hb.ne' (by positivity), Real.logb_div (by positivity) hp.ne',
    Real.logb_pow] at hh
  unfold normWidth
  norm_num at hh ⊢
  linarith

theorem normWidth_upper (I : Ideal O) (hI : I ≠ 0) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : (Ideal.absNorm I : ℝ) ≤ C * Z ^ E) :
    normWidth Z I ≤ E + Real.logb Z C := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos I hI) h
  rw [Real.logb_mul hC.ne' (by positivity), Real.logb_rpow hz0 (ne_of_gt hZ)] at hh
  unfold normWidth
  linarith

theorem normWidth_lower (I : Ideal O) (Z C E : ℝ)
    (hZ : 1 < Z) (hC : 0 < C) (h : Z ^ E / C ≤ (Ideal.absNorm I : ℝ)) :
    E - Real.logb Z C ≤ normWidth Z I := by
  have hz0 : 0 < Z := by linarith
  have hh := Real.logb_le_logb_of_le hZ (div_pos (Real.rpow_pos_of_pos hz0 E) hC) h
  rwa [Real.logb_div (by positivity) hC.ne', Real.logb_rpow hz0 (ne_of_gt hZ)] at hh

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal O) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

theorem logb_widthConstant (Z : ℝ) (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH) (hf : 0 < Cf) :
    Real.logb Z (widthConstant B Ck CO CH Cf) =
      2 * Real.logb Z CH + normWidth Z B + 2 * Real.logb Z Ck +
        Real.logb Z CO + Real.logb Z Cf := by
  have hb := actual_ideal_norm_pos B hB
  unfold widthConstant normWidth
  rw [Real.logb_mul (by positivity) hf.ne', Real.logb_mul (by positivity) ho.ne',
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) hb.ne',
    Real.logb_pow, Real.logb_pow]
  norm_num

theorem terminal_common_width {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0) -
      normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  have hb := reflection_charge_width I F B R hI hF hB hR P hcop hpool hres e Z hZ
  have h₁ := normWidth_upper I hI Z Ck M hZ hCk hk
  have h₂ := normWidth_lower (rowPowerfulPart I) Z CO O₀ hZ hCO hpow
  have h₃ := normWidth_lower (rowResidualPart I (B * F * R)) Z CH H hZ hCH hrow
  have h₄ := normWidth_upper F hF Z Cf V hZ hCf hf
  change _ ≤ 2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
    Real.logb Z (widthConstant B Ck CO CH Cf)
  rw [logb_widthConstant Z B hB Ck CO CH Cf hCk hCO hCH hCf]
  unfold terminalDualWidth reflectionWidth at *
  linarith

theorem normWidth_nonneg (Z : ℝ) (hZ : 1 < Z) (I : Ideal O) (hI : I ≠ 0) :
    0 ≤ normWidth Z I := Real.logb_nonneg hZ (norm_one_le I hI)

theorem rpow_reflectionWidth {ι : Type*} [Fintype ι]
    (Z : ℝ) (hZ : 1 < Z) (P : ι → Ideal O) (hP : ∀ i, P i ≠ 0)
    (j : ι → ℕ) (e : ι → Fin 3) :
    Z ^ reflectionWidth Z P j e = reflectionConductorCost P j e := by
  rw [← logb_reflectionConductorCost Z P hP j e]
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ) (reflectionConductorCost_pos P hP j e)

theorem width_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η := by
  have hb := actual_ideal_norm_pos B hB
  obtain ⟨a, ha, h₁⟩ := constant_log_error (CH * Ck * CO) η (by positivity) hη
  obtain ⟨b, hb', h₂⟩ := constant_log_error (widthConstant B Ck CO CH Cf) η
    (by unfold widthConstant; positivity) hη
  exact ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ =>
    ⟨h₁ Z ((le_max_left _ _).trans hZ), h₂ Z ((le_max_right _ _).trans hZ)⟩⟩

theorem canonical_active_pool (I Q Q₀ : Ideal O) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (P : FreeReflection.reflectionActivePool I Q Q₀ e) :
    P.val ∣ I * Q ∧ ¬ P.val ∣ rowResidualPart I Q ∧
      ConcretePrimeRowBridge.goodLambda ∉ P.val ∧
        ringChar (O ⧸ P.val) ≠ 2 ∧ ¬ Q₀ ≤ P.val := by
  let p : FreeReflection.pool I Q Q₀ :=
    ⟨P.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e P.property⟩
  exact ⟨FreeReflection.pool_divides I Q Q₀ hI hQ p,
    FreeReflection.pool_nonresidual I Q Q₀ p, FreeReflection.pool_good I Q Q₀ p,
    FreeReflection.pool_odd I Q Q₀ p, FreeReflection.pool_free I Q Q₀ p⟩

theorem surviving_inactive_exponent (I F Q Q₀ : Ideal O)
    (e : FreeReflection.pool I Q Q₀ → Fin 6)
    (hne : FreeReflection.reflectionSixInactiveWeight I F Q Q₀ e ≠ 0)
    (P : FreeReflection.pool I Q Q₀) (hP : ¬ reflectionSixActive (e P)) :
    completedLocalExponent I F P.val = 0 := by
  have he : reflectionSixValid e := by
    by_contra he
    exact hne (by simp [FreeReflection.reflectionSixInactiveWeight, he])
  have hp : FreeReflection.reflectionInactiveStratumWeight I F Q Q₀ (reflectionSixSupport e) ≠ 0 := by
    simpa only [FreeReflection.reflectionSixInactiveWeight, ite_eq_left he] using hne
  rw [FreeReflection.reflectionInactiveStratumWeight_formula] at hp
  have hm : P ∈ (Finset.univ : Finset (FreeReflection.pool I Q Q₀)) \ reflectionSixSupport e := by
    simp [reflectionSixSupport, hP]
  have ht := (Finset.prod_ne_zero_iff.mp hp) P hm
  by_contra hj
  exact ht (by simp [hj])

theorem surviving_reflected_branch {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (I F : Ideal O) (e : ι → Fin 3) (n b : O)
    (hne : reflectedBranch P hg (fun i => completedLocalExponent I F (P i)) e n b ≠ 0) :
    ∀ i, (completedLocalExponent I F (P i) ≠ 4 → e i = 0) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 1 → n ∈ P i) ∧
      (completedLocalExponent I F (P i) = 4 → e i = 2 → n ∉ P i ∧ b ∈ P i) := by
  intro i
  apply surviving_local_piece (P i) (hg i) _ (e i) n b
  exact (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)

theorem canonical_terminal_common_width
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z M O₀ H V za Nstar Ck CO CH Cf : ℝ) (hZ : 1 < Z)
    (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V) :
    let P := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val
    let j := fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e =>
      completedLocalExponent I F p.val
    let l := FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e
    terminalDualWidth Z H za Nstar P j l -
      normWidth Z (reflectionExtractedDivisor P j l 0) -
      normWidth Z (reflectionExtractedDivisor P j l 2) ≤
        2 * M - O₀ + normWidth Z R + V - Nstar + 2 * za +
          Real.log (widthConstant B Ck CO CH Cf) / Real.log Z := by
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact terminal_common_width I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

theorem hybridSaving_nonneg {v za : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ za) :
    0 ≤ hybridSaving v za := by unfold hybridSaving; positivity

theorem hybridSaving_half {v za : ℝ} (hv : 0 ≤ v)
    (hu : hybridSaving v za ≠ za) : v / 2 ≤ hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v + za) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v + za) / 3) with hz | hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      linarith

theorem terminal_width_from_invariant
    {F₀ N V M Q z₀ c O₀ za Nstar hhat d η Td S₀ B₀ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hF : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hwidth : Td - S₀ - B₀ ≤ 2 * M - O₀ + Q + V - Nstar + 2 * za + η) :
    Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η := by
  have hi := hinv.1
  linarith

theorem reflected_row_bound {O₀ H S₀ B₀ za v ell el Td M η : ℝ}
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hrow : v + ell ≤ H) (hH : H ≤ M - O₀ + η) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ M + za + 5 * η / 3 := by
  have hu := hybridSaving_nonneg hv hz
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_left hrow]
  linarith

theorem reflected_column_full_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hl : 0 ≤ ell) (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za = za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) + 5 * η / 3 + τ := by
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol, hu]
  linarith

theorem reflected_column_partial_bound {O₀ H S₀ B₀ za v ell el Td η τ : ℝ}
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hcol : H ≤ v + ell)
    (hu : hybridSaving v za ≠ za) (hret : v + 3 * ell + el ≤ Td + τ) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      O₀ / 2 + (Td - S₀ - B₀) / 2 + za + 7 * η / 6 + τ / 2 := by
  have hu' := hybridSaving_half hv hu
  have hm := le_max_left 0 (Td - v - 3 * ell - el)
  unfold reflectedExponent
  rw [max_eq_right hcol]
  linarith

theorem reflected_terminal_cases
    {F₀ M Q z₀ c O₀ H S₀ B₀ za v ell el Td d η τ : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η) :
    (v + ell ≤ H → reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - c + 5 * η / 3) ∧
    (H ≤ v + ell → hybridSaving v za = za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ F₀ - 2 * c + 5 * d + 17 * η / 3 + τ) ∧
    (H ≤ v + ell → hybridSaving v za ≠ za →
      reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        F₀ - M / 4 - 3 * c / 4 + 5 * d / 2 + 19 * η / 6 + τ / 2) := by
  obtain ⟨hi₁, hi₂⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro hrow
    have hb := reflected_row_bound hO hS hB hz hv hl he hrow hH (Td := Td)
    linarith
  · intro hcol hu
    have hb := reflected_column_full_bound hl he hcol hu hret (O₀ := O₀) (S₀ := S₀) (B₀ := B₀)
    linarith
  · intro hcol hu
    have hb := reflected_column_partial_bound hS hB hv hl he hcol hu hret (O₀ := O₀)
    linarith

theorem reflected_terminal_saving
    {F₀ M Q z₀ c cstar O₀ H S₀ B₀ za v ell el Td d η τ π : ℝ}
    (hinv : CanonicalMargins F₀ M Q z₀ c) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hO : 0 ≤ O₀) (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hz : 0 ≤ za) (hzcap : za ≤ z₀) (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (he : -η ≤ el) (hret : v + 3 * ell + el ≤ Td + τ)
    (hH : H ≤ M - O₀ + η)
    (hT : Td - S₀ - B₀ ≤ M - O₀ + 2 * za - z₀ - c + 5 * d + 4 * η)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H S₀ B₀ za v ell el Td + π ≤ F₀ - cstar / 4 := by
  obtain ⟨hr, hf, hp⟩ := reflected_terminal_cases hinv hQ hO hS hB hz hzcap hv hl he hret hH hT
  rcases le_total (v + ell) H with h | h
  · have := hr h
    linarith
  · by_cases hu : hybridSaving v za = za
    · have := hf h hu
      linarith
    · have := hp h hu
      linarith

def ramifiedWidth (Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z 3

theorem rpow_ramifiedWidth (Z : ℝ) (hZ : 1 < Z) (m : ℕ) :
    Z ^ ramifiedWidth Z m = (3 : ℝ) ^ ((m : ℝ) - 4) := by
  unfold ramifiedWidth
  rw [mul_comm, Real.rpow_mul (by linarith : 0 ≤ Z),
    Real.rpow_logb (by linarith : 0 < Z) (ne_of_gt hZ) (by norm_num : (0 : ℝ) < 3)]

theorem fractionalThetaPoint_norm_width (Z : ℝ) (hZ : 1 < Z)
    (u : Oˣ) (m : ℕ) (n b : O) :
    ‖fractionalThetaPoint u m n b‖ ^ 2 =
      Z ^ ramifiedWidth Z m * ‖ConcreteTraceCRT.eisEmbedding n‖ ^ 2 *
        (‖ConcreteTraceCRT.eisEmbedding b‖ ^ 2) ^ 3 := by
  rw [rpow_ramifiedWidth Z hZ]
  exact fractionalThetaPoint_norm_sq u m n b

theorem ramified_width_threshold (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨Z₀, hZ₀, hlog⟩ := constant_log_error ((3 : ℝ) ^ (4 : ℕ)) η (by norm_num) hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ m
  have hz := hZ₀.trans_le hZ
  have hl := hlog Z hZ
  change Real.logb Z ((3 : ℝ) ^ (4 : ℕ)) ≤ η at hl
  rw [Real.logb_pow] at hl
  have hn : 0 ≤ Real.logb Z 3 := Real.logb_nonneg hz (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold ramifiedWidth
  norm_num at hl
  nlinarith

theorem terminal_error_threshold (B : Ideal O) (hB : B ≠ 0)
    (Ck CO CH Cf η : ℝ) (hk : 0 < Ck) (ho : 0 < CO) (hh : 0 < CH)
    (hf : 0 < Cf) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ m : ℕ, -η ≤ ramifiedWidth Z m := by
  obtain ⟨a, ha, h₁⟩ := width_error_threshold B hB Ck CO CH Cf η hk ho hh hf hη
  obtain ⟨b, hb, h₂⟩ := ramified_width_threshold η hη
  refine ⟨max a b, ha.trans_le (le_max_left _ _), fun Z hZ => ?_⟩
  exact ⟨(h₁ Z ((le_max_left _ _).trans hZ)).1,
    (h₁ Z ((le_max_left _ _).trans hZ)).2, h₂ Z ((le_max_right _ _).trans hZ)⟩

theorem actual_terminal_saving {ι : Type*} [Fintype ι]
    (I F B R : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (B * F * R))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (B * F * R)) (e : ι → Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    reflectedExponent O₀ H
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
      (normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
      za v ell el (terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e) + π ≤
        F₀ - cstar / 4 := by
  have hH := physical_residual_width I (B * F * R) hI Z M O₀ H Ck CO CH hZ hCk hCO hCH hk hpow hrow
  have hT := terminal_common_width I F B R hI hF hB hR P hcop hpool hres e
    Z M O₀ H V za Nstar Ck CO CH Cf hZ hCk hCO hCH hCf hk hpow hrow hf
  have hT' := terminal_width_from_invariant (O₀ := O₀) (za := za) (η := η)
    (Td := terminalDualWidth Z H za Nstar P (fun i => completedLocalExponent I F (P i)) e)
    (S₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0))
    (B₀ := normWidth Z (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2))
    hinv hF₀ hscale hV hh (hT.trans (by linarith))
  exact reflected_terminal_saving hinv (normWidth_nonneg Z hZ R hR) hM hO
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (normWidth_nonneg Z hZ _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    hz hzcap hv hl he hret (by linarith) hT' hc hmargin hd hη hτ hπ

theorem residual_admissible_of_fixed_bad (I F B R : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B) :
    Admissible (rowResidualPart I (B * F * R)) := by
  apply rowResidualPart_admissible
  intro P hP
  exact (hbad P hP).trans ((dvd_mul_right B F).trans (dvd_mul_right (B * F) R))

def canonicalDualWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6)
    (Z H za Nstar : ℝ) : ℝ :=
  terminalDualWidth Z H za Nstar
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e)

def canonicalExtractedWidth (I F B R Q₀ : Ideal O)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (Z : ℝ) (a : Fin 3) : ℝ :=
  normWidth Z (reflectionExtractedDivisor
    (fun p : FreeReflection.reflectionActivePool I (B * F * R) Q₀ e => p.val)
    (fun p => completedLocalExponent I F p.val)
    (FreeReflection.reflectionActiveLabel I (B * F * R) Q₀ e) a)

theorem canonical_terminal_saving
    (I F B R Q₀ : Ideal O) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ B)
    (e : FreeReflection.pool I (B * F * R) Q₀ → Fin 6) (m : ℕ)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (herr : Real.log (CH * Ck * CO) / Real.log Z ≤ η ∧
      Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η ∧
      ∀ a : ℕ, -η ≤ ramifiedWidth Z a)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell)
    (hret : v + 3 * ell + ramifiedWidth Z m ≤ canonicalDualWidth I F B R Q₀ e Z H za Nstar + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    Admissible (rowResidualPart I (B * F * R)) ∧
    reflectedExponent O₀ H (canonicalExtractedWidth I F B R Q₀ e Z 0)
      (canonicalExtractedWidth I F B R Q₀ e Z 2) za v ell (ramifiedWidth Z m)
      (canonicalDualWidth I F B R Q₀ e Z H za Nstar) + π ≤ F₀ - cstar / 4 := by
  refine ⟨residual_admissible_of_fixed_bad I F B R hbad, ?_⟩
  let Q := B * F * R
  have hQ : Q ≠ 0 := mul_ne_zero (mul_ne_zero hB hF) hR
  let A := FreeReflection.reflectionActivePool I Q Q₀ e
  let : ∀ p : A, p.val.IsMaximal := fun p => FreeReflection.pool_maximal I Q Q₀
    ⟨p.val, FreeReflection.reflectionActivePool_subset I Q Q₀ e p.property⟩
  have hcop : Pairwise (fun p q : A => IsCoprime p.val q.val) := by
    intro p q hpq
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
  exact actual_terminal_saving I F B R hI hF hB hR (fun p : A => p.val) hcop
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).1)
    (fun p => (canonical_active_pool I Q Q₀ hI hQ e p).2.1)
    (FreeReflection.reflectionActiveLabel I Q Q₀ e)
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell (ramifiedWidth Z m) d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf herr.1 herr.2.1 hinv hF₀ hscale hV hh hM hO hz hzcap
    hv hl (herr.2.2 m) hret hc hmargin hd hη hτ hπ

end SevenEighths.InverseTerminalWidths

end

end OAI
