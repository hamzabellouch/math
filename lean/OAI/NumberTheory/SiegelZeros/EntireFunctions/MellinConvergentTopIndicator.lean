import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped BigOperators Topology

open Filter Set MeasureTheory
open scoped Topology

namespace WeightedTorusJets

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma mellinConvergent_top_indicator (P : WeakFEPair E) (s : ℂ) :
    MellinConvergent ((Ioi 1).indicator (fun t ↦ P.f t - P.f₀)) s := by
  have hi : MellinConvergent P.f_modif s :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  change IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • P.f_modif t) (Ioi 0) at hi
  unfold MellinConvergent
  convert hi.indicator (t := Ioi 1) measurableSet_Ioi using 1
  ext t
  by_cases ht : 1 < t
  · simp [WeakFEPair.f_modif, ht, notMem_Ioo_of_ge ht.le]
  · simp [ht]

lemma f_modif_eq_top_add_inv (P : WeakFEPair E) {t : ℝ} (ht : 0 < t) :
    P.f_modif t = (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) t +
      P.ε • ((t : ℂ) ^ (-P.k : ℂ) •
        (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) t⁻¹) := by
  rcases lt_trichotomy t 1 with h | rfl | h
  · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h
    have heq := P.hf_modif_FE t⁻¹ (inv_pos.mpr ht)
    rw [one_div, inv_inv] at heq
    rw [Set.indicator_of_notMem (show t ∉ Ioi 1 from not_lt.mpr h.le), zero_add,
      Set.indicator_of_mem (show t⁻¹ ∈ Ioi 1 from hinv), heq]
    simp only [WeakFEPair.g_modif, Pi.add_apply,
      Set.indicator_of_mem (show t⁻¹ ∈ Ioi 1 from hinv),
      Set.indicator_of_notMem (notMem_Ioo_of_ge hinv.le),
      add_zero, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, Complex.ofReal_cpow ht.le,
      Complex.ofReal_neg, mul_smul]
  · simp [WeakFEPair.f_modif]
  · have hinv : ¬1 < t⁻¹ := not_lt.mpr ((inv_le_one₀ ht).mpr h.le)
    simp [WeakFEPair.f_modif, h, notMem_Ioo_of_ge h.le, hinv]

lemma mellin_top_indicator_eq (f : ℝ → E) (s : ℂ) :
    mellin ((Ioi 1).indicator f) s =
      ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • f t := by
  simp only [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

lemma Lambda_zero_eq_top_integrals (P : WeakFEPair E) (s : ℂ) :
    P.Λ₀ s = (∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • (P.f t - P.f₀)) +
      P.ε • (∫ t : ℝ in Ioi 1, (t : ℂ) ^ ((P.k : ℂ) - s - 1) • (P.g t - P.g₀)) := by
  let F := (Ioi 1).indicator (fun t ↦ P.f t - P.f₀)
  let G := (Ioi 1).indicator (fun t ↦ P.g t - P.g₀)
  have hF : MellinConvergent F s := mellinConvergent_top_indicator P s
  have hG : MellinConvergent G (P.k - s) := mellinConvergent_top_indicator P.symm _
  have hInv : MellinConvergent (fun t ↦ G t⁻¹) (s - P.k) := by
    have hdiv : (s - (P.k : ℂ)) / ((-1 : ℝ) : ℂ) = (P.k : ℂ) - s := by
      simp only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one, neg_sub]
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (f := G) (s := s - P.k)
        (a := -1) (by norm_num)).mpr (hdiv.symm ▸ hG)
  have hSecond : MellinConvergent
      (fun t : ℝ ↦ P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s := by
    apply MellinConvergent.const_smul
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using hInv
  calc
    P.Λ₀ s = mellin (fun t : ℝ ↦ F t + P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact congrArg (fun v : E ↦ (t : ℂ) ^ (s - 1) • v) (f_modif_eq_top_add_inv P ht)
    _ = mellin F s + mellin (fun t : ℝ ↦ P.ε • ((t : ℂ) ^ (-P.k : ℂ) • G t⁻¹)) s :=
      (hasMellin_add hF hSecond).2
    _ = mellin F s + P.ε • mellin G (P.k - s) := by
      rw [mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
      congr 3
      ring
    _ = _ := by rw [mellin_top_indicator_eq, mellin_top_indicator_eq]

lemma norm_top_integral_le (f : ℝ → E) (s : ℂ) :
    ‖∫ t : ℝ in Ioi 1, (t : ℂ) ^ (s - 1) • f t‖ ≤
      ∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖f t‖ := by
  apply le_trans (norm_integral_le_integral_norm _)
  apply le_of_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht),
    Complex.sub_re, Complex.one_re]

theorem norm_Lambda_zero_le_top_integrals (P : WeakFEPair E) (s : ℂ) :
    ‖P.Λ₀ s‖ ≤ (∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖P.f t - P.f₀‖) +
      ‖P.ε‖ * (∫ t : ℝ in Ioi 1, t ^ (P.k - s.re - 1) * ‖P.g t - P.g₀‖) := by
  rw [Lambda_zero_eq_top_integrals]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  apply add_le_add (norm_top_integral_le _ s)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa using (norm_top_integral_le (fun t ↦ P.g t - P.g₀) (P.k - s))

end

section

open _root_.Real Set MeasureTheory

theorem exponential_moment_integrable {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) :
    IntegrableOn (fun t : ℝ => t ^ R * exp (-p * t)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := R) (p := 1)
    (by linarith) zero_lt_one hp
  simp only [rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi (by norm_num))

theorem exponential_moment_pointwise {p R t : ℝ}
    (hp : 0 < p) (hR : 0 ≤ R) (ht : 1 ≤ t) :
    t ^ R * exp (-p * t) ≤
      exp ((R + 1) * log (2 * (R + 1) / p)) * exp (-(p / 2) * t) := by
  have hr : 0 < R + 1 := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ha : 0 < 2 * (R + 1) / p := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht0 ha)
  rw [Real.log_div ht0.ne' ha.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hr.le
  have heq : (R + 1) * (t / (2 * (R + 1) / p) - 1) = p * t / 2 - (R + 1) := by
    field_simp
  rw [heq] at hmul
  have htlog := Real.log_nonneg ht
  rw [Real.rpow_def_of_pos ht0, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exponential_moment_le {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) :
    (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) ≤
      exp ((R + 1) * log (2 * (R + 1) / p)) * (2 / p) := by
  have hp2 : -(p / 2) < 0 := by linarith
  have hi := (integrableOn_exp_mul_Ioi hp2 1).const_mul
    (exp ((R + 1) * log (2 * (R + 1) / p)))
  calc
    _ ≤ ∫ t : ℝ in Ioi 1,
        exp ((R + 1) * log (2 * (R + 1) / p)) * exp (-(p / 2) * t) :=
      setIntegral_mono_on (exponential_moment_integrable hp hR) hi measurableSet_Ioi
        (fun t ht => exponential_moment_pointwise hp hR ht.le)
    _ = exp ((R + 1) * log (2 * (R + 1) / p)) *
        (exp (-(p / 2)) * (2 / p)) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hp2]
      congr 1
      simp only [mul_one]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      calc
        _ ≤ 1 * (2 / p) := mul_le_mul_of_nonneg_right
          (Real.exp_le_one_iff.mpr hp2.le) (by positivity)
        _ = _ := one_mul _

theorem mul_log_le_three_halves {u : ℝ} (hu : 1 ≤ u) :
    u * log u ≤ 2 * u ^ (3 / 2 : ℝ) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlog := Real.log_le_rpow_div hu0.le (by norm_num : 0 < (1 / 2 : ℝ))
  have hmul := mul_le_mul_of_nonneg_left hlog hu0.le
  have heq : u * u ^ (1 / 2 : ℝ) = u ^ (3 / 2 : ℝ) := by
    calc
      _ = u ^ ((1 : ℝ) + 1 / 2) := by rw [Real.rpow_add hu0, Real.rpow_one]
      _ = _ := by norm_num
  nlinarith

theorem exponential_moment_growth {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) ≤
        exp (C * (1 + R) ^ (3 / 2 : ℝ)) := by
  refine ⟨2 * |log (2 / p)| + 2, by positivity, fun R hR => ?_⟩
  have hr : 0 < R + 1 := by positivity
  have hp2 : 0 < 2 / p := by positivity
  have hpow : R + 1 ≤ (R + 1) ^ (3 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ R + 1)
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hpow1 : 1 ≤ (R + 1) ^ (3 / 2 : ℝ) := by
    exact one_le_rpow (by linarith) (by norm_num)
  have hlog := mul_log_le_three_halves (by linarith : 1 ≤ R + 1)
  have hA := le_abs_self (log (2 / p))
  have hAu := mul_le_mul_of_nonneg_left hA hr.le
  have hA1 := mul_le_mul_of_nonneg_left hpow1 (abs_nonneg (log (2 / p)))
  have hApow := mul_le_mul_of_nonneg_left hpow (abs_nonneg (log (2 / p)))
  calc
    _ ≤ exp ((R + 1) * log (2 * (R + 1) / p)) * (2 / p) :=
      exponential_moment_le hp hR
    _ = exp ((R + 1) * log (2 * (R + 1) / p) + log (2 / p)) := by
      rw [Real.exp_add, Real.exp_log hp2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [show 2 * (R + 1) / p = (2 / p) * (R + 1) by ring,
        Real.log_mul hp2.ne' hr.ne', show 1 + R = R + 1 by ring]
      nlinarith

theorem log_one_add_le_log_two_add {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : b ≤ exp x) : log (1 + b) ≤ log 2 + x := by
  calc
    _ ≤ log (2 * exp x) := Real.log_le_log (by positivity)
      (by linarith [Real.one_le_exp_iff.mpr hx])
    _ = _ := by rw [Real.log_mul (by norm_num) (exp_pos _).ne', Real.log_exp]

theorem log_norm_growth_of_norm_growth {F : ℂ → ℂ}
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F s‖ ≤ exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ,
      log (1 + ‖F s‖) ≤ D * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨C + log 2, by positivity, fun s => ?_⟩
  have hpow1 : 1 ≤ (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
    one_le_rpow (le_add_of_nonneg_right (norm_nonneg _)) (by norm_num)
  have hlog2 : 0 ≤ log 2 := by positivity
  have hlog := log_one_add_le_log_two_add (norm_nonneg _) (by positivity) (hF s)
  have hmul := mul_le_mul_of_nonneg_left hpow1 hlog2
  nlinarith

end

open Filter Set MeasureTheory _root_.Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
lemma weighted_norm_integral_le_moment (f : ℝ → E) {p C a R : ℝ}
    (hp : 0 < p) (hR : 0 ≤ R) (ha : a ≤ R)
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * exp (-p * t)) :
    (∫ t : ℝ in Ioi 1, t ^ a * ‖f t‖) ≤
      C * (∫ t : ℝ in Ioi 1, t ^ R * exp (-p * t)) := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg (zero_lt_one.trans ht).le _) (norm_nonneg _)
  · exact (exponential_moment_integrable hp hR).const_mul C
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      _ ≤ t ^ R * (C * exp (-p * t)) :=
        mul_le_mul (rpow_le_rpow_of_exponent_le ht.le ha) (hf t ht.le)
          (norm_nonneg _) (rpow_nonneg (zero_lt_one.trans ht).le _)
      _ = _ := by ring

theorem norm_Lambda_zero_growth_of_exp_bounds (P : WeakFEPair E)
    (hf : ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 1 ≤ t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
      ‖P.Λ₀ s‖ ≤ exp (B * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨pf, hpf, Cf, hCf, hf⟩ := hf
  obtain ⟨pg, hpg, Cg, hCg, hg⟩ := hg
  obtain ⟨Ef, hEf, hEf_bound⟩ := exponential_moment_growth hpf
  obtain ⟨Eg, hEg, hEg_bound⟩ := exponential_moment_growth hpg
  let D := Ef + Eg
  let K := (2 + |P.k|) ^ (3 / 2 : ℝ)
  let A := Cf + ‖P.ε‖ * Cg
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A + D * K, by positivity, ?_⟩
  intro s
  let R := 1 + |P.k| + ‖s‖
  let r := (1 + ‖s‖) ^ (3 / 2 : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := one_le_rpow (by simp) (by norm_num)
  have hfexp : s.re - 1 ≤ R := by
    have := Complex.re_le_norm s
    dsimp [R]
    linarith [abs_nonneg P.k]
  have hgexp : P.k - s.re - 1 ≤ R := by
    have := (neg_le_abs s.re).trans (Complex.abs_re_le_norm s)
    dsimp [R]
    linarith [le_abs_self P.k]
  have hweight : (1 + R) ^ (3 / 2 : ℝ) ≤ K * r := by
    calc
      _ ≤ ((2 + |P.k|) * (1 + ‖s‖)) ^ (3 / 2 : ℝ) := by
        apply rpow_le_rpow (by positivity) _ (by norm_num)
        dsimp [R]
        nlinarith [abs_nonneg P.k, norm_nonneg s]
      _ = _ := by rw [mul_rpow (by positivity) (by positivity)]
  have hEfm : Ef * (1 + R) ^ (3 / 2 : ℝ) ≤ D * K * r := by
    have h1 := mul_le_mul_of_nonneg_left hweight hEf.le
    have h2 := mul_le_mul_of_nonneg_right (show Ef ≤ D by dsimp [D]; linarith)
      (mul_nonneg hK.le hr)
    nlinarith
  have hEgm : Eg * (1 + R) ^ (3 / 2 : ℝ) ≤ D * K * r := by
    have h1 := mul_le_mul_of_nonneg_left hweight hEg.le
    have h2 := mul_le_mul_of_nonneg_right (show Eg ≤ D by dsimp [D]; linarith)
      (mul_nonneg hK.le hr)
    nlinarith
  have hfint : (∫ t : ℝ in Ioi 1, t ^ (s.re - 1) * ‖P.f t - P.f₀‖) ≤
      Cf * exp (D * K * r) := by
    apply (weighted_norm_integral_le_moment _ hpf hR hfexp hf).trans
    exact mul_le_mul_of_nonneg_left
      ((hEf_bound R hR).trans (exp_le_exp.mpr hEfm)) hCf.le
  have hgint : (∫ t : ℝ in Ioi 1, t ^ (P.k - s.re - 1) * ‖P.g t - P.g₀‖) ≤
      Cg * exp (D * K * r) := by
    apply (weighted_norm_integral_le_moment _ hpg hR hgexp hg).trans
    exact mul_le_mul_of_nonneg_left
      ((hEg_bound R hR).trans (exp_le_exp.mpr hEgm)) hCg.le
  have hAexp : A ≤ exp (A * r) := by
    have h1 := mul_le_mul_of_nonneg_left hr1 hA.le
    exact (by linarith : A ≤ A * r + 1).trans (add_one_le_exp _)
  calc
    ‖P.Λ₀ s‖ ≤ Cf * exp (D * K * r) + ‖P.ε‖ * (Cg * exp (D * K * r)) :=
      (norm_Lambda_zero_le_top_integrals P s).trans
        (add_le_add hfint (mul_le_mul_of_nonneg_left hgint (norm_nonneg _)))
    _ = A * exp (D * K * r) := by dsimp [A]; ring
    _ ≤ exp (A * r) * exp (D * K * r) :=
      mul_le_mul_of_nonneg_right hAexp (exp_nonneg _)
    _ = _ := by rw [← exp_add]; congr 1; dsimp [r]; ring

end WeightedTorusJets

open Filter Set Asymptotics

namespace WeightedTorusJets

theorem exists_global_exp_bound {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {p : ℝ} (hf : ContinuousOn f (Ici 1))
    (hdecay : f =O[atTop] (fun t : ℝ => Real.exp (-p * t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨A, _, hA⟩ := hdecay.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.mp hA.bound
  have hcompact : ContinuousOn (fun t => ‖f t‖ / Real.exp (-p * t))
      (Icc 1 (max 1 T)) := by
    apply (hf.mono fun _ ht => ht.1).norm.div
    · fun_prop
    · exact fun _ _ => Real.exp_ne_zero _
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcompact
  refine ⟨max 1 (max A B), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  by_cases hlarge : T ≤ t
  · calc
      ‖f t‖ ≤ A * Real.exp (-p * t) := by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hT t hlarge
      _ ≤ max 1 (max A B) * Real.exp (-p * t) :=
        mul_le_mul_of_nonneg_right ((le_max_left A B).trans (le_max_right _ _))
          (Real.exp_pos _).le
  · have hsmall := hB t ⟨ht, (le_of_not_ge hlarge).trans (le_max_right _ _)⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
      at hsmall
    calc
      ‖f t‖ ≤ B * Real.exp (-p * t) := (div_le_iff₀ (Real.exp_pos _)).mp hsmall
      _ ≤ max 1 (max A B) * Real.exp (-p * t) :=
        mul_le_mul_of_nonneg_right ((le_max_right A B).trans (le_max_right _ _))
          (Real.exp_pos _).le

theorem exists_evenKernel_sub_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.evenKernel a t - (if a = 0 then 1 else 0)‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact ((HurwitzZeta.continuousOn_evenKernel a).sub continuousOn_const).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_cosKernel_sub_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.cosKernel a t - 1‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_cosKernel_sub a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact ((HurwitzZeta.continuousOn_cosKernel a).sub continuousOn_const).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_oddKernel_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.oddKernel a t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_oddKernel a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact (HurwitzZeta.continuousOn_oddKernel a).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_sinKernel_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖HurwitzZeta.sinKernel a t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hdecay⟩ := HurwitzZeta.isBigO_atTop_sinKernel a
  refine ⟨p, hp, exists_global_exp_bound ?_ hdecay⟩
  exact (HurwitzZeta.continuousOn_sinKernel a).mono
    fun t ht => (show (0 : ℝ) < t from lt_of_lt_of_le zero_lt_one ht)

theorem exists_hurwitzEvenFEPair_f_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzEvenFEPair a).f t - (HurwitzZeta.hurwitzEvenFEPair a).f₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_evenKernel_sub_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  by_cases ha : a = 0 <;>
    simpa [HurwitzZeta.hurwitzEvenFEPair, ha, ← Complex.ofReal_one,
      ← Complex.ofReal_sub] using hbound t ht

theorem exists_hurwitzEvenFEPair_g_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzEvenFEPair a).g t - (HurwitzZeta.hurwitzEvenFEPair a).g₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_cosKernel_sub_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzEvenFEPair, ← Complex.ofReal_one,
    ← Complex.ofReal_sub] using hbound t ht

theorem exists_hurwitzOddFEPair_f_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzOddFEPair a).f t - (HurwitzZeta.hurwitzOddFEPair a).f₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_oddKernel_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzOddFEPair] using hbound t ht

theorem exists_hurwitzOddFEPair_g_exp_bound (a : UnitAddCircle) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖(HurwitzZeta.hurwitzOddFEPair a).g t - (HurwitzZeta.hurwitzOddFEPair a).g₀‖ ≤
        C * Real.exp (-p * t) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := exists_sinKernel_exp_bound a
  refine ⟨p, hp, C, hC, fun t ht => ?_⟩
  simpa [HurwitzZeta.hurwitzOddFEPair] using hbound t ht

theorem norm_growth_half_shift {F : ℂ → ℂ}
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)))
    {b : ℂ} (hb : ‖b‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖F ((s + b) / 2) / 2‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨4 * C, by positivity, fun s => ?_⟩
  have harg : 1 + ‖(s + b) / 2‖ ≤ 2 * (1 + ‖s‖) := by
    rw [norm_div, Complex.norm_ofNat]
    have := norm_add_le s b
    nlinarith [norm_nonneg s]
  have hpow : (1 + ‖(s + b) / 2‖) ^ (3 / 2 : ℝ) ≤
      4 * (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (1 + ‖s‖)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) harg (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
  calc
    _ ≤ ‖F ((s + b) / 2)‖ := by
      rw [norm_div, Complex.norm_ofNat]
      exact div_le_self (norm_nonneg _) (by norm_num)
    _ ≤ Real.exp (C * (1 + ‖(s + b) / 2‖) ^ (3 / 2 : ℝ)) := hF _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]

theorem norm_completedHurwitzZetaEven_zero_growth_of_Lambda_zero_growth
    (a : UnitAddCircle)
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖(HurwitzZeta.hurwitzEvenFEPair a).Λ₀ s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  simpa [HurwitzZeta.completedHurwitzZetaEven₀] using
    norm_growth_half_shift hF (b := 0) (by simp)

theorem norm_completedHurwitzZetaOdd_growth_of_Lambda_zero_growth
    (a : UnitAddCircle)
    (hF : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖(HurwitzZeta.hurwitzOddFEPair a).Λ₀ s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  have hΛ : (HurwitzZeta.hurwitzOddFEPair a).Λ =
      (HurwitzZeta.hurwitzOddFEPair a).Λ₀ := by
    ext s
    simp [WeakFEPair.Λ, HurwitzZeta.hurwitzOddFEPair]
  simpa only [HurwitzZeta.completedHurwitzZetaOdd, hΛ] using
    norm_growth_half_shift hF (b := 1) (by simp)

theorem exists_completedHurwitzZetaEven_zero_growth (a : UnitAddCircle) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  norm_completedHurwitzZetaEven_zero_growth_of_Lambda_zero_growth a
    (norm_Lambda_zero_growth_of_exp_bounds (HurwitzZeta.hurwitzEvenFEPair a)
      (exists_hurwitzEvenFEPair_f_exp_bound a) (exists_hurwitzEvenFEPair_g_exp_bound a))

theorem exists_completedHurwitzZetaOdd_growth (a : UnitAddCircle) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  norm_completedHurwitzZetaOdd_growth_of_Lambda_zero_growth a
    (norm_Lambda_zero_growth_of_exp_bounds (HurwitzZeta.hurwitzOddFEPair a)
      (exists_hurwitzOddFEPair_f_exp_bound a) (exists_hurwitzOddFEPair_g_exp_bound a))

end WeightedTorusJets

end SiegelZeros

end OAI
