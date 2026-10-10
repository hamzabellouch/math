import OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma exponential_cubic_bound (x Y : ℝ) (hx : 0 < x) (hY : 0 < Y) :
    x * Real.exp (-x/Y) ≤ 6*Y^3/x^2 := by
  have he := Real.pow_div_factorial_le_exp (x/Y) (show 0 ≤ x/Y by positivity) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x/Y))).le
  have hex : Real.exp (x/Y)*Real.exp (-(x/Y))=1 := by rw [←Real.exp_add]; simp
  rw [hex] at hh
  have hb : (x/Y)^3*Real.exp (-(x/Y)) ≤ 6 := by nlinarith
  calc
    _ = (Y^3/x^2)*((x/Y)^3*Real.exp (-(x/Y))) := by
      rw [neg_div]
      field_simp
    _ ≤ (Y^3/x^2)*6 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma divisor_count (I : Ideal O) (hI : I ≠ 0) :
    ((idealDivisors I).card : ℝ) ≤ 128*(Ideal.absNorm I : ℝ) := by
  apply DescentFiberCost.finite_ideal_count_real
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  · intro J hJ
    exact ne_zero_of_dvd_ne_zero hI ((mem_idealDivisors hI).mp hJ)
  · intro J hJ
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm ((mem_idealDivisors hI).mp hJ))

theorem cutoffCoefficient_bound (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D : ℝ) (I : Ideal O) :
    ‖cutoffCoefficient V D I‖ ≤ 128*B*(Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [cutoffCoefficient,hI]
  rw [cutoffCoefficient,ite_eq_right hI]
  let e := mulFiberDivisorEquiv I hI
  have he : (∑' p : MulFiber I, (moebius p.val.1 : ℂ)*V ((Ideal.absNorm p.val.1 : ℝ)/D)) =
      ∑' J : {J : Ideal O // J ∈ idealDivisors I},
        (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D) :=
    e.tsum_eq (fun J => (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D))
  rw [he,tsum_fintype]
  calc
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I},
        ‖(moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D)‖ := norm_sum_le _ _
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I}, B := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one _)).trans (hV _)
    _ = ((idealDivisors I).card : ℝ)*B := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (divisor_count I hI) hB]

lemma norm_weight_two (I : Ideal O) (hI : I ≠ 0) :
    ‖CubicEisenstein.fullIdealWeight 2 I‖ = 1/(Ideal.absNorm I : ℝ)^2 := by
  rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,Complex.cpow_neg,Complex.cpow_ofNat,
    norm_inv,norm_pow,Complex.norm_natCast]
  simp [one_div]

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,ite_eq_right hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,CubicEisenstein.fullIdealWeight]
  have hN : (0 : ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

def terminalRemainder (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

lemma exponentialTerm_half (χ : Character) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : Character) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

def terminalTerm (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : Character) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

theorem terminal_sum_finite (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ I ∈ ConcretePrimeRowBridge.idealsUpTo ⌈2*U⌉₊, terminalTerm χ V T D Y U s I := by
  apply tsum_eq_sum
  intro I hI
  by_cases hI0 : I = 0
  · simp [terminalTerm,exponentialTerm,cutoffCoefficient,hI0]
  have hN : (⌈2*U⌉₊ : ℝ) < Ideal.absNorm I := by
    have hn : ¬Ideal.absNorm I ≤ ⌈2*U⌉₊ := by
      intro hh
      apply hI
      exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0),hh⟩
    exact_mod_cast lt_of_not_ge hn
  have ht : T ((Ideal.absNorm I : ℝ)/U)=0 := by
    apply hTzero
    apply (le_div_iff₀ hU).mpr
    linarith [Nat.le_ceil (2*U)]
  simp only [terminalTerm,ht,mul_zero]

end SevenEighths.HeckeDetectorTail

end

end OAI
