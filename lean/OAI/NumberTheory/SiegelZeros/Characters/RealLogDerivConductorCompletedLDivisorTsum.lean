import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.ConductorCompletedL

namespace OAI

namespace SiegelZeros
open scoped _root_.SiegelZeros

open scoped BigOperators Topology
namespace WeightedTorusJets

section
open Filter Set MeasureTheory
open scoped Topology
open Filter Set Asymptotics

section

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard RealCharacterAnalysis

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "DivisorIndices" => divisorZeroIndex₀ (conductorCompletedL χ) Set.univ

theorem real_logDeriv_conductorCompletedL_eq_divisor_tsum
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hquad : χ.IsQuadratic) (B : ℂ)
    (hbase : Summable (fun j : DivisorIndices => (1 / divisorZeroIndex₀Val j).re))
    (hexp : ∀ z : ℂ, conductorCompletedL χ z ≠ 0 →
      HasSum (fun j : DivisorIndices =>
        1 / (z - divisorZeroIndex₀Val j) + 1 / divisorZeroIndex₀Val j)
        (logDeriv (conductorCompletedL χ) z - B))
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' j : DivisorIndices, (1 / ((s : ℂ) - divisorZeroIndex₀Val j)).re := by
  have hf := differentiable_conductorCompletedL χ hχ1
  have h0 := conductorCompletedL_ne_zero_at_zero χ hχ hχ1
  have hnz (x : ℝ) (hx : x = -1 ∨ 1 < x) : conductorCompletedL χ (x : ℂ) ≠ 0 := by
    intro hzero
    have hstrip := completedL_zero_re_mem_Ioo χ hχ hχ1
      ((conductorCompletedL_zero_iff χ (x : ℂ)).mp hzero)
    simp only [Set.mem_Ioo, Complex.ofReal_re] at hstrip
    rcases hx with rfl | hx
    · linarith
    · linarith
  rw [tsum_divisorIndex_eq_analytic hf h0 (fun z => (1 / ((s : ℂ) - z)).re)]
  apply real_logDeriv_conductorCompletedL_eq_tsum hχ hχ1 hquad B.re
    ((summable_divisorIndex_iff_analytic hf h0 (fun z => (1 / z).re)).mp hbase) _ hs
  intro x hx
  apply ((divisorIndexEquivAnalytic hf h0).hasSum_iff
    (f := fun j => (1 / ((x : ℂ) - j.1) + 1 / j.1).re)).mp
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val, Complex.sub_re] using
    Complex.hasSum_re (hexp (x : ℂ) (hnz x hx))

end

section

theorem abs_reciprocal_sub_re_le_normSq {ρ : ℂ} {s : ℝ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (hs : 1 < s) :
    |(1 / ((s : ℂ) - ρ)).re| ≤
      (s * (1 + 1 / (s - 1) ^ 2)) / Complex.normSq ρ := by
  have hs₀ : 0 < s := zero_lt_one.trans hs
  have hsquare : 0 < (s - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hρne : ρ ≠ 0 := by
    intro h
    simp [h] at hρ₀
  have hnorm : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρne
  have hdenlower : (s - 1) ^ 2 ≤ Complex.normSq ((s : ℂ) - ρ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith [sq_nonneg ρ.im, mul_self_le_mul_self
      (show 0 ≤ s - 1 by linarith) (show s - 1 ≤ s - ρ.re by linarith)]
  have hden : 0 < Complex.normSq ((s : ℂ) - ρ) := hsquare.trans_le hdenlower
  have hnormadd : Complex.normSq ρ ≤ 1 + Complex.normSq ((s : ℂ) - ρ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith [sq_nonneg (s - ρ.re), mul_self_le_mul_self hρ₀.le hρ₁.le]
  have hone : 1 ≤ Complex.normSq ((s : ℂ) - ρ) / (s - 1) ^ 2 := by
    exact (le_div_iff₀ hsquare).mpr (by simpa using hdenlower)
  have hbound : Complex.normSq ρ ≤
      (1 + 1 / (s - 1) ^ 2) * Complex.normSq ((s : ℂ) - ρ) := by
    calc
      Complex.normSq ρ ≤ 1 + Complex.normSq ((s : ℂ) - ρ) := hnormadd
      _ ≤ Complex.normSq ((s : ℂ) - ρ) / (s - 1) ^ 2 +
          Complex.normSq ((s : ℂ) - ρ) := by linarith
      _ = _ := by ring
  have hnum : 0 ≤ s - ρ.re := by linarith
  simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
  rw [abs_of_nonneg (div_nonneg hnum hden.le)]
  apply (div_le_div_iff₀ hden hnorm).mpr
  calc
    (s - ρ.re) * Complex.normSq ρ ≤ s * Complex.normSq ρ :=
      mul_le_mul_of_nonneg_right (sub_le_self s hρ₀.le) hnorm.le
    _ ≤ s * ((1 + 1 / (s - 1) ^ 2) * Complex.normSq ((s : ℂ) - ρ)) :=
      mul_le_mul_of_nonneg_left hbound hs₀.le
    _ = _ := by ring

theorem abs_reciprocal_re_le_normSq {ρ : ℂ}
    (hρ₀ : 0 ≤ ρ.re) (hρ₁ : ρ.re ≤ 1) :
    |(1 / ρ).re| ≤ 1 / Complex.normSq ρ := by
  simp only [one_div, Complex.inv_re]
  rw [abs_of_nonneg (div_nonneg hρ₀ (Complex.normSq_nonneg ρ))]
  simpa only [one_div] using div_le_div_of_nonneg_right hρ₁ (Complex.normSq_nonneg ρ)

theorem summable_abs_reciprocal_sub_re {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hsum : Summable (fun i => ‖ρ i‖⁻¹ ^ (2 : ℕ)))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun i => |(1 / ((s : ℂ) - ρ i)).re|) := by
  have hnormSq : Summable (fun i => 1 / Complex.normSq (ρ i)) := by
    simpa only [Complex.normSq_eq_norm_sq, one_div, inv_pow] using hsum
  apply (hnormSq.mul_left (s * (1 + 1 / (s - 1) ^ 2))).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_abs, mul_one_div] using
    abs_reciprocal_sub_re_le_normSq (hstrip i).1 (hstrip i).2 hs

theorem summable_abs_reciprocal_re {ι : Type*} (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hsum : Summable (fun i => ‖ρ i‖⁻¹ ^ (2 : ℕ))) :
    Summable (fun i => |(1 / ρ i).re|) := by
  have hnormSq : Summable (fun i => 1 / Complex.normSq (ρ i)) := by
    simpa only [Complex.normSq_eq_norm_sq, one_div, inv_pow] using hsum
  apply hnormSq.of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs, abs_abs] using
    abs_reciprocal_re_le_normSq (hstrip i).1 (hstrip i).2

open _root_.SiegelZeros.Complex.Hadamard

theorem divisorZeroIndex_val_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (p : divisorZeroIndex₀ f Set.univ) : f (divisorZeroIndex₀Val p) = 0 := by
  by_contra hz
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := (hf.analyticAt (divisorZeroIndex₀Val p)).analyticOrderAt_eq_zero.mpr hz
  have hsupport := divisorZeroIndex₀Val_mem_divisor_support p
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ _), hzero] at hsupport
  simp at hsupport

theorem conductorCompletedL_divisorIndex_re_mem_Ioo {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ) :
    0 < (divisorZeroIndex₀Val p).re ∧ (divisorZeroIndex₀Val p).re < 1 := by
  have hzero := divisorZeroIndex_val_zero (differentiable_conductorCompletedL χ hχ₁) p
  exact completedL_zero_re_mem_Ioo χ hχ hχ₁
    ((conductorCompletedL_zero_iff χ _).mp hzero)

theorem conductorCompletedL_abs_reciprocal_summable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1)
    (hsum : Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re|) ∧
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / divisorZeroIndex₀Val p).re|) := by
  have hstrip := conductorCompletedL_divisorIndex_re_mem_Ioo χ hχ hχ₁
  exact ⟨summable_abs_reciprocal_sub_re _ hstrip hsum hs,
    summable_abs_reciprocal_re _ (fun p => ⟨(hstrip p).1.le, (hstrip p).2.le⟩) hsum⟩

theorem exists_divisorZeroIndex_val_eq_of_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfne : f ≠ 0) {z : ℂ} (hz₀ : z ≠ 0) (hz : f z = 0) :
    ∃ p : divisorZeroIndex₀ f Set.univ, divisorZeroIndex₀Val p = z := by
  have horder : analyticOrderAt f z ≠ 0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz
  have htop : analyticOrderAt f z ≠ ⊤ := by
    exact fun h => hfne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hf.analyticAt).mp h)
  have hpos : 0 < analyticOrderNatAt f z := by
    rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
    exact ⟨horder, htop⟩
  refine ⟨⟨⟨z, ⟨0, ?_⟩⟩, hz₀⟩, rfl⟩
  rw [RealCharacterAnalysis.toNat_divisor_eq_analyticOrderNatAt hf]
  exact hpos

theorem real_zero_le_divisor_reciprocal_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ₁ : χ ≠ 1)
    (hsum : Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)))
    {β s : ℝ} (hβ₀ : 0 < β)
    (hβ : DirichletCharacter.LFunction χ (β : ℂ) = 0) (hs : 1 < s) :
    1 / (s - β) ≤
      ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
        (1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re := by
  have hf := differentiable_conductorCompletedL χ hχ₁
  have hfne : conductorCompletedL χ ≠ 0 := by
    intro hzero
    have hzero₁ : conductorCompletedL χ 1 = 0 := congrFun hzero 1
    exact completedL_ne_zero_of_one_le_re χ hχ₁ (s := 1) (by simp)
      ((conductorCompletedL_zero_iff χ 1).mp hzero₁)
  have hzeroβ : conductorCompletedL χ (β : ℂ) = 0 := by
    rw [conductorCompletedL_zero_iff,
      completedL_eq_mul_gammaFactor χ (by simpa using hβ₀), hβ, zero_mul]
  obtain ⟨p, hp⟩ := exists_divisorZeroIndex_val_eq_of_zero hf hfne
    (Complex.ofReal_ne_zero.mpr hβ₀.ne') hzeroβ
  have hsummable := (conductorCompletedL_abs_reciprocal_summable χ hχ hχ₁ hsum hs).1.of_abs
  have hle := hsummable.le_tsum p (fun j _ => by
    have hj := conductorCompletedL_divisorIndex_re_mem_Ioo χ hχ hχ₁ j
    simp only [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (by linarith) (Complex.normSq_nonneg _))
  simpa only [hp, ← Complex.ofReal_sub, one_div, ← Complex.ofReal_inv,
    Complex.ofReal_re] using hle

end

open _root_.SiegelZeros.Complex DirichletCharacter _root_.SiegelZeros.Complex.Hadamard

theorem conductorCompletedL_zero_sum_absolutely_summable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ =>
      |(1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re|) :=
  (conductorCompletedL_abs_reciprocal_summable χ hχ hχ1
    (conductorCompletedL_zeroIndex_summable_inv_sq χ hχ hχ1) hs).1

theorem real_logDeriv_conductorCompletedL_eq_divisor_tsum_source {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hquad : χ.IsQuadratic) {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
        (1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re := by
  obtain ⟨B, hB⟩ := conductorCompletedL_logDeriv_hasSum χ hχ hχ1
  apply real_logDeriv_conductorCompletedL_eq_divisor_tsum hχ hχ1 hquad B _ hB hs
  exact (summable_abs_reciprocal_re divisorZeroIndex₀Val
    (fun p => let h := conductorCompletedL_zeroIndex_re_mem_Ioo χ hχ hχ1 p
      ⟨h.1.le, h.2.le⟩)
    (conductorCompletedL_zeroIndex_summable_inv_sq χ hχ hχ1)).of_abs

theorem real_zero_le_conductorCompletedL_logDeriv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hquad : χ.IsQuadratic) {β s : ℝ} (hβ0 : 0 < β)
    (hβ : LFunction χ (β : ℂ) = 0) (hs : 1 < s) :
    1 / (s - β) ≤ (logDeriv (conductorCompletedL χ) (s : ℂ)).re := by
  rw [real_logDeriv_conductorCompletedL_eq_divisor_tsum_source χ hχ hχ1 hquad hs]
  exact real_zero_le_divisor_reciprocal_tsum χ hχ hχ1
    (conductorCompletedL_zeroIndex_summable_inv_sq χ hχ hχ1) hβ0 hβ hs

end

section

open Filter Set
open scoped Topology

lemma analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hzpos : 0 < z.re := hz
    linarith
  exact hd.analyticAt ((Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs)

theorem exists_bound_Gamma_logDeriv_parity :
    ∃ C : ℝ, 0 < C ∧ ∀ s ε : ℝ, 1 < s → s ≤ 2 → (ε = 0 ∨ ε = 1) →
      ‖logDeriv Complex.Gamma (((s + ε) / 2 : ℝ) : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ ↦ logDeriv Complex.Gamma (t : ℂ))
      (Icc (1 / 2) (3 / 2)) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have ha := analyticAt_Gamma_of_re_pos (s := (t : ℂ)) (by simpa using htpos)
    exact ((ha.deriv.continuousAt.div ha.continuousAt
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using htpos))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s ε hs hs2 hε
  apply (hC ((s + ε) / 2) ?_).trans (le_max_left _ _)
  rcases hε with rfl | rfl <;> constructor <;> linarith

end

section

open scoped Classical

theorem character_parity_parameter {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (1 - χ (-1)) / 2 = if χ.Even then (0 : ℂ) else 1 := by
  rcases χ.even_or_odd with h | h
  · simp [h, show χ (-1) = 1 from h]
  · simp [h.not_even, show χ (-1) = -1 from h]

theorem character_parity_parameter_real {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (1 - (χ (-1)).re) / 2 = if χ.Even then (0 : ℝ) else 1 := by
  rcases χ.even_or_odd with h | h
  · simp [h, show χ (-1) = 1 from h]
  · simp [h.not_even, show χ (-1) = -1 from h]

theorem character_gamma_argument_mem_Icc {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) :
    (s + (1 - (χ (-1)).re) / 2) / 2 ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  rw [character_parity_parameter_real]
  split_ifs <;> constructor <;> linarith

end

section

theorem logDeriv_GammaR_add {s a : ℂ} (hs : 0 < (s + a).re) :
    logDeriv (fun z : ℂ => Complex.Gammaℝ (z + a)) s =
      -Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma ((s + a) / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-(s + a) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hpi)
  have hgpos : 0 < ((s + a) / 2).re := by
    simpa only [Complex.div_ofNat_re] using half_pos hs
  have hg := (analyticAt_Gamma_of_re_pos hgpos).differentiableAt
  have hgn : Complex.Gamma ((s + a) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hgpos
  have hpow : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2))
      ((Real.pi : ℂ) ^ (-(s + a) / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    simpa only [id_eq, Pi.neg_apply] using
      (((hasDerivAt_id s).add_const a).neg.div_const (2 : ℂ)).const_cpow (Or.inl hpi)
  have harg : HasDerivAt (fun z : ℂ => (z + a) / 2) (1 / 2) s :=
    ((hasDerivAt_id s).add_const a).div_const (2 : ℂ)
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2) *
    Complex.Gamma ((z + a) / 2)) s = _
  rw [logDeriv_fun_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2))
    (g := fun z : ℂ => Complex.Gamma ((z + a) / 2)) s hp hgn hpow.differentiableAt
      (hg.comp s harg.differentiableAt)]
  rw [logDeriv_apply, hpow.deriv]
  rw [logDeriv_fun_comp (f := Complex.Gamma) (g := fun z : ℂ => (z + a) / 2)
    hg harg.differentiableAt, harg.deriv]
  field_simp

theorem gammaFactor_logDeriv_real_parity {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℝ} (hs : 0 < s) :
    logDeriv χ.gammaFactor (s : ℂ) =
      -Complex.log (Real.pi : ℂ) / 2 +
        logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ) / 2 := by
  classical
  rw [character_parity_parameter_real]
  by_cases hχ : χ.Even
  · have hf : χ.gammaFactor = Complex.Gammaℝ := funext hχ.gammaFactor_def
    rw [hf]
    simpa only [hχ, ite_true, add_zero, Complex.ofReal_div, Complex.ofReal_ofNat] using
      logDeriv_GammaR_add (s := (s : ℂ)) (a := 0) (by simpa using hs)
  · have hf : χ.gammaFactor = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z
      simp [DirichletCharacter.gammaFactor, hχ]
    rw [hf]
    simpa only [hχ, ite_false, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_ofNat] using
      logDeriv_GammaR_add (s := (s : ℂ)) (a := 1) (by simp; linarith)

theorem conductor_gamma_correction_real {q : ℕ} (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) {s : ℝ} (hs : 0 < s) :
    (Complex.log (q : ℂ) / 2 + logDeriv χ.gammaFactor (s : ℂ)).re =
      Real.log ((q : ℝ) / Real.pi) / 2 +
        (logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ)).re / 2 := by
  rw [gammaFactor_logDeriv_real_parity χ hs]
  rw [Complex.add_re, Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_re,
    Complex.div_ofNat_re, Complex.neg_re, ← Complex.ofReal_natCast,
    Complex.log_ofReal_re, Complex.log_ofReal_re]
  rw [Real.log_div (Nat.cast_ne_zero.mpr hq) Real.pi_ne_zero]
  ring

theorem exists_bound_gammaFactor_logDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∀ s : ℝ, 1 < s → s ≤ 2 → ‖logDeriv χ.gammaFactor (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_Gamma_logDeriv_parity
  refine ⟨‖Complex.log (Real.pi : ℂ)‖ / 2 + C / 2, by positivity, ?_⟩
  intro q χ s hs hs2
  have heps : (1 - (χ (-1)).re) / 2 = 0 ∨ (1 - (χ (-1)).re) / 2 = 1 := by
    rw [character_parity_parameter_real]
    split_ifs <;> simp
  have hg := hbound s ((1 - (χ (-1)).re) / 2) hs hs2 heps
  rw [gammaFactor_logDeriv_real_parity χ (by linarith)]
  calc
    _ ≤ ‖-Complex.log (Real.pi : ℂ) / 2‖ +
        ‖logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ) / 2‖ :=
      norm_add_le _ _
    _ = ‖Complex.log (Real.pi : ℂ)‖ / 2 +
        ‖logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ)‖ / 2 := by
      simp only [norm_div, norm_neg, Complex.norm_ofNat]
    _ ≤ _ := by linarith

theorem exists_upper_bound_conductor_gammaFactor_logDeriv :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ), 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      ∀ s : ℝ, 1 < s → s ≤ 2 →
      (Complex.log (q : ℂ) / 2 + logDeriv χ.gammaFactor (s : ℂ)).re ≤
        K * Real.log q := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_gammaFactor_logDeriv
  refine ⟨C + 1, by linarith, ?_⟩
  intro q hq χ s hs hs2
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hg : (logDeriv χ.gammaFactor (s : ℂ)).re ≤ C :=
    (Complex.re_le_norm _).trans (hbound q χ s hs hs2)
  rw [Complex.add_re, Complex.div_ofNat_re, ← Complex.ofReal_natCast,
    Complex.log_ofReal_re]
  nlinarith

open Filter Set
open scoped Topology

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hne
  · simp
  · intro hz
    have h := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hne, hz, mul_zero] at h
    exact h rfl

lemma logDeriv_riemannZeta₁ {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta₁ s = 1 / (s - 1) + logDeriv riemannZeta s := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs
  have hz := riemannZeta₁_ne_zero_of_one_le_re hs.le
  rw [logDeriv_apply, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne, riemannZeta_eq_inv_sub_mul hne]
  field_simp
  ring

theorem exists_bound_zeta_logDeriv :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖-logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)‖ ≤ C := by
  have hc : ContinuousOn (fun s : ℝ ↦ logDeriv riemannZeta₁ (s : ℂ)) (Icc 1 2) := by
    intro s hs
    have ha := differentiable_riemannZeta₁.analyticAt (s : ℂ)
    exact ((ha.deriv.continuousAt.div ha.continuousAt
      (riemannZeta₁_ne_zero_of_one_le_re (by simpa using hs.1))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs hs2
  have heq : -logDeriv riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1) =
      -logDeriv riemannZeta₁ (s : ℂ) := by
    rw [logDeriv_riemannZeta₁ (by simpa using hs)]
    ring
  rw [heq, norm_neg]
  exact (hC s ⟨hs.le, hs2⟩).trans (le_max_left _ _)

theorem exists_upper_bound_zeta_logDeriv_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-logDeriv riemannZeta (s : ℂ)).re ≤ 1 / (s - 1) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_zeta_logDeriv
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have h := (Complex.re_le_norm _).trans (hbound s hs hs2)
  have heq : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [Complex.sub_re, heq] at h
  linarith

end

theorem conductorCompletedL_logDeriv_decomposition {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (conductorCompletedL χ) s = logDeriv (DirichletCharacter.LFunction χ) s +
      (Complex.log (q : ℂ) / 2 + logDeriv χ.gammaFactor s) := by
  classical
  have hs0 : 0 < s.re := by linarith
  have hgn := gammaFactor_ne_zero_of_re_pos χ hs0
  have hinv : Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
    rcases χ.even_or_odd with heven | hodd
    · convert Complex.differentiable_Gammaℝ_inv using 1
      funext z
      rw [heven.gammaFactor_def]
    · convert Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1) using 1
      funext z
      rw [hodd.gammaFactor_def]
      rfl
  have hgamma : DifferentiableAt ℂ χ.gammaFactor s := by
    convert (hinv s).inv (inv_ne_zero hgn) using 1
    funext z
    exact (inv_inv (χ.gammaFactor z)).symm
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun z => DirichletCharacter.LFunction χ z * χ.gammaFactor z := by
    have hU : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs0
    filter_upwards [hU] with z hz using completedL_eq_mul_gammaFactor χ hz
  have hl := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [conductorCompletedL_logDeriv χ hχ
    (completedL_ne_zero_of_one_le_re χ hχ hs.le), hl]
  rw [logDeriv_fun_mul s
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs.le) hgn
    (DirichletCharacter.differentiable_LFunction hχ s) hgamma]
  ring

theorem logDeriv_upper_of_completedL_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ s β : ℝ, 1 < s → s ≤ 2 →
      1 / (s - β) ≤ (logDeriv (conductorCompletedL χ) (s : ℂ)).re →
      (-logDeriv riemannZeta (s : ℂ) -
        logDeriv (DirichletCharacter.LFunction χ) (s : ℂ)).re ≤
        K * Real.log q + 1 / (s - 1) - 1 / (s - β) := by
  obtain ⟨Kg, hKg, hgamma⟩ := exists_upper_bound_conductor_gammaFactor_logDeriv
  obtain ⟨Cz, hCz, hzeta⟩ := exists_upper_bound_zeta_logDeriv_re
  refine ⟨Kg + Cz, by linarith, ?_⟩
  intro q _ hq χ hχ s β hs hs2 hzero
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 < Real.log q :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hdecomp := congrArg Complex.re
    (conductorCompletedL_logDeriv_decomposition χ hχ (s := (s : ℂ)) (by simpa using hs))
  rw [Complex.add_re] at hdecomp
  have hg := hgamma q hq χ s hs hs2
  have hz := hzeta s hs hs2
  rw [Complex.sub_re]
  nlinarith

end WeightedTorusJets

end SiegelZeros

end OAI
