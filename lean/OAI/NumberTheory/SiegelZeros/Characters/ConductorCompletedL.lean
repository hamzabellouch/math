import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.MellinConvergentTopIndicator

namespace OAI

namespace SiegelZeros
open scoped _root_.SiegelZeros

open scoped BigOperators Topology
open Filter Set MeasureTheory
open scoped Topology
open Filter Set Asymptotics
namespace WeightedTorusJets

section

open _root_.Complex DirichletCharacter

variable {q : ℕ} [NeZero q]

noncomputable def conductorCompletedL (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * completedLFunction χ s

omit [NeZero q] in
theorem gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

theorem completedL_eq_mul_gammaFactor (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) :
    completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)]
  exact (div_mul_cancel₀ _ (gammaFactor_ne_zero_of_re_pos χ hs)).symm

theorem completedL_ne_zero_of_one_le_re (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : completedLFunction χ s ≠ 0 := by
  have hs0 : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
  rw [completedL_eq_mul_gammaFactor χ hs0]
  exact mul_ne_zero (LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs)
    (gammaFactor_ne_zero_of_re_pos χ hs0)

theorem conductorCompletedL_zero_iff (χ : DirichletCharacter ℂ q) (s : ℂ) :
    conductorCompletedL χ s = 0 ↔ completedLFunction χ s = 0 := by
  simp [conductorCompletedL, Nat.cast_ne_zero.mpr (NeZero.ne q)]

theorem differentiable_conductorCompletedL (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (conductorCompletedL χ) := by
  apply Differentiable.mul
  · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  · exact differentiable_completedLFunction hχ

theorem conductorCompletedL_one_sub (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    conductorCompletedL χ (1 - s) = rootNumber χ * conductorCompletedL χ⁻¹ s := by
  rw [conductorCompletedL, hχ.completedLFunction_one_sub, conductorCompletedL]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  calc
    (q : ℂ) ^ ((1 - s) / 2) *
        ((q : ℂ) ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s) =
      ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
        (rootNumber χ * completedLFunction χ⁻¹ s) := by ring
    _ = (q : ℂ) ^ (s / 2) * (rootNumber χ * completedLFunction χ⁻¹ s) := by
      rw [← Complex.cpow_add _ _ hq]
      congr 2
      ring
    _ = rootNumber χ * ((q : ℂ) ^ (s / 2) * completedLFunction χ⁻¹ s) := by ring

theorem completedL_zero_re_mem_Ioo (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {ρ : ℂ}
    (hρ : completedLFunction χ ρ = 0) : ρ.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hinv : χ⁻¹.IsPrimitive := by
    simpa only [DirichletCharacter.IsPrimitive, conductor_inv] using hχ
  have hinv1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  constructor
  · by_contra! hn
    have hz : completedLFunction χ⁻¹ (1 - ρ) = 0 := by
      rw [hinv.completedLFunction_one_sub, inv_inv, hρ, mul_zero]
    exact completedL_ne_zero_of_one_le_re χ⁻¹ hinv1 (by simp only [sub_re, one_re]; linarith) hz
  · by_contra! hn
    exact completedL_ne_zero_of_one_le_re χ hχ1 hn hρ

theorem conductorCompletedL_logDeriv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : completedLFunction χ s ≠ 0) :
    logDeriv (conductorCompletedL χ) s =
      Complex.log (q : ℂ) / 2 + logDeriv (completedLFunction χ) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hq)
  have hd : HasDerivAt (fun z : ℂ => (q : ℂ) ^ (z / 2))
      ((q : ℂ) ^ (s / 2) * Complex.log (q : ℂ) * (1 / 2)) s := by
    simpa only [id_eq] using
      ((hasDerivAt_id s).div_const (2 : ℂ)).const_cpow (.inl hq)
  have hl : logDeriv (fun z : ℂ => (q : ℂ) ^ (z / 2)) s =
      Complex.log (q : ℂ) / 2 := by
    rw [logDeriv_apply, hd.deriv]
    field_simp
  exact (logDeriv_fun_mul s hpow hs hd.differentiableAt
    (differentiable_completedLFunction hχ s)).trans (congrArg (· + _) hl)

theorem completedL_eq_poleFree (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    completedLFunction χ s = ZMod.completedLFunction₀ χ s := by
  have hq : q ≠ 1 := hχ ∘ level_one' _
  simp [completedLFunction, ZMod.completedLFunction_eq, χ.map_zero' hq,
    χ.sum_eq_zero_of_ne_one hχ]

theorem conductorCompletedL_eq_hurwitzSum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    conductorCompletedL χ s = (q : ℂ) ^ (-s / 2) *
      ((∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) +
       ∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by
  rw [conductorCompletedL, completedL_eq_poleFree χ hχ, ZMod.completedLFunction₀]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  calc
    _ = ((q : ℂ) ^ (s / 2) * (q : ℂ) ^ (-s)) *
      ((∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s) +
       ∑ j : ZMod q, χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hq]
      congr 2
      ring

theorem norm_conductor_power_le (s : ℂ) :
    ‖(q : ℂ) ^ (-s / 2)‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  change ‖((q : ℝ) : ℂ) ^ (-s / 2)‖ ≤ _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  simp only [Complex.div_ofNat_re, neg_re]
  have hreal : -s.re ≤ ‖s‖ := (neg_le_abs s.re).trans (Complex.abs_re_le_norm s)
  have := mul_le_mul_of_nonneg_left hreal (Real.log_nonneg hq1)
  nlinarith

theorem norm_conductorCompletedL_le_hurwitzSum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    ‖conductorCompletedL χ s‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) *
      ((∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖) +
       ∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖) := by
  have hsum : ∀ f : ZMod q → ℂ, ‖∑ j, χ j * f j‖ ≤ ∑ j, ‖f j‖ := by
    intro f
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one j)
  rw [conductorCompletedL_eq_hurwitzSum χ hχ s, norm_mul]
  apply mul_le_mul (norm_conductor_power_le s)
    ((norm_add_le _ _).trans (add_le_add (hsum _) (hsum _))) (norm_nonneg _)
    (Real.exp_nonneg _)

omit [NeZero q] in
theorem finite_uniform_exp_bound {ι : Type*} [Finite ι] (f : ι → ℂ → ℂ)
    (r : ℂ → ℝ) (hr : ∀ z, 0 ≤ r z)
    (hf : ∀ i, ∃ C > 0, ∀ z, ‖f i z‖ ≤ Real.exp (C * r z)) :
    ∃ C > 0, ∀ i z, ‖f i z‖ ≤ Real.exp (C * r z) := by
  choose c _ hc using hf
  obtain ⟨B, hB⟩ := (Set.finite_range c).bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun i z => ?_⟩
  exact (hc i z).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    ((hB (Set.mem_range_self i)).trans (le_max_left _ _)) (hr z)))

theorem conductorCompletedL_growth_of_hurwitz (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1)
    (he : ∀ j : ZMod q, ∃ C > 0, ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)))
    (ho : ∀ j : ZMod q, ∃ C > 0, ∀ s : ℂ,
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ))) :
    ∃ C > 0, ∀ s : ℂ, ‖conductorCompletedL χ s‖ ≤
      Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  classical
  let r : ℂ → ℝ := fun s => (1 + ‖s‖) ^ (3 / 2 : ℝ)
  have hr : ∀ s, 0 ≤ r s := fun s => Real.rpow_nonneg (by positivity) _
  obtain ⟨E, hE, he⟩ := finite_uniform_exp_bound _ r hr he
  obtain ⟨O, hO, ho⟩ := finite_uniform_exp_bound _ r hr ho
  let B := max E O
  have hB : 0 < B := lt_of_lt_of_le hE (le_max_left _ _)
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  refine ⟨Real.log (q : ℝ) / 2 + B + 2 * q, by positivity, fun s => ?_⟩
  have hr1 : 1 ≤ r s := Real.one_le_rpow (by simp) (by norm_num)
  have hrs : ‖s‖ ≤ r s := (by linarith : ‖s‖ ≤ 1 + ‖s‖).trans
    (Real.self_le_rpow_of_one_le (by simp) (by norm_num))
  have he' : ∀ j : ZMod q,
      ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤
        Real.exp (B * r s) := fun j => (he j s).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (hr s)))
  have ho' : ∀ j : ZMod q,
      ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤
        Real.exp (B * r s) := fun j => (ho j s).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (hr s)))
  have hsum :
      ((∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖) +
       ∑ j : ZMod q, ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖) ≤
      (2 * q) * Real.exp (B * r s) := by
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (ZMod q))) => he' j)
    have h2 := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (ZMod q))) => ho' j)
    simpa [Finset.sum_const, ZMod.card, nsmul_eq_mul, two_mul, add_mul] using add_le_add h1 h2
  have hcard : (2 * q : ℝ) ≤ Real.exp ((2 * q : ℝ) * r s) := by
    have h1 : (2 * q : ℝ) ≤ (2 * q : ℝ) * r s :=
      le_mul_of_one_le_right (by positivity) hr1
    exact h1.trans ((by linarith : (2 * q : ℝ) * r s ≤ (2 * q : ℝ) * r s + 1).trans
      (Real.add_one_le_exp _))
  calc
    ‖conductorCompletedL χ s‖ ≤ Real.exp (Real.log (q : ℝ) * ‖s‖ / 2) *
        ((2 * q) * Real.exp (B * r s)) :=
      (norm_conductorCompletedL_le_hurwitzSum χ hχ s).trans
        (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
    _ ≤ Real.exp ((Real.log (q : ℝ) / 2) * r s) *
        (Real.exp ((2 * q : ℝ) * r s) * Real.exp (B * r s)) := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hrs hlog]
      · exact mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      · positivity
      · positivity
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [r]; ring

theorem conductorCompletedL_analyticOrderAt_eq (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (conductorCompletedL χ) s = analyticOrderAt (completedLFunction χ) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have ha : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : ℂ)).const_cpow (.inl hq)).analyticAt s
  change analyticOrderAt ((fun z : ℂ => (q : ℂ) ^ (z / 2)) * completedLFunction χ) s = _
  rw [analyticOrderAt_mul ha ((differentiable_completedLFunction hχ).analyticAt s),
    ha.analyticOrderAt_eq_zero.mpr (Complex.cpow_ne_zero_iff.mpr (.inl hq)), zero_add]

theorem conductorCompletedL_ne_zero_at_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) : conductorCompletedL χ 0 ≠ 0 := by
  intro hzero
  have hstrip := completedL_zero_re_mem_Ioo χ hχ hχ1
    ((conductorCompletedL_zero_iff χ 0).mp hzero)
  norm_num at hstrip

theorem conductorCompletedL_analyticOrderNatAt_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    analyticOrderNatAt (conductorCompletedL χ) 0 = 0 := by
  rw [analyticOrderNatAt,
    analyticOrderAt_eq_zero.mpr (.inr (conductorCompletedL_ne_zero_at_zero χ hχ hχ1))]
  rfl

end

section

theorem conductorCompletedL_norm_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C > 0, ∀ s : ℂ, ‖conductorCompletedL χ s‖ ≤
      Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
  conductorCompletedL_growth_of_hurwitz χ hχ
    (fun j => exists_completedHurwitzZetaEven_zero_growth (ZMod.toAddCircle j))
    (fun j => exists_completedHurwitzZetaOdd_growth (ZMod.toAddCircle j))

theorem conductorCompletedL_log_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C > 0, ∀ s : ℂ, Real.log (1 + ‖conductorCompletedL χ s‖) ≤
      C * (1 + ‖s‖) ^ (3 / 2 : ℝ) :=
  log_norm_growth_of_norm_growth (conductorCompletedL_norm_growth χ hχ)

open _root_.SiegelZeros.Complex.Hadamard

variable {q : ℕ} [NeZero q]

theorem conductorCompletedL_zeroIndex_vanishes (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ)) :
    conductorCompletedL χ (divisorZeroIndex₀Val p) = 0 := by
  by_contra hnonzero
  have ha : AnalyticOnNhd ℂ (conductorCompletedL χ) Set.univ :=
    fun z _ => (differentiable_conductorCompletedL χ hχ).analyticAt z
  have hdiv : MeromorphicOn.divisor (conductorCompletedL χ) Set.univ
      (divisorZeroIndex₀Val p) = 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ _),
      (ha _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hnonzero]
    simp
  exact divisorZeroIndex₀Val_mem_divisor_support p hdiv

theorem conductorCompletedL_zeroIndex_re_mem_Ioo (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ)) :
    (divisorZeroIndex₀Val p).re ∈ Set.Ioo (0 : ℝ) 1 :=
  completedL_zero_re_mem_Ioo χ hp hχ
    ((conductorCompletedL_zero_iff χ _).mp (conductorCompletedL_zeroIndex_vanishes χ hχ p))

theorem conductorCompletedL_zeroIndex_summable_inv_sq (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀Val p‖⁻¹ ^ (2 : ℕ)) := by
  have hfloor : Nat.floor (3 / 2 : ℝ) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).mpr
    norm_num
  simpa [hfloor] using summable_norm_inv_pow_divisorZeroIndex₀_of_growth
    (f := conductorCompletedL χ) (ρ := (3 / 2 : ℝ)) (by norm_num)
    (differentiable_conductorCompletedL χ hχ)
    ⟨0, conductorCompletedL_ne_zero_at_zero χ hp hχ⟩
    (conductorCompletedL_log_growth χ hχ)

theorem conductorCompletedL_hadamard_factorization (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ s : ℂ,
      conductorCompletedL χ s = Complex.exp (P.eval s) *
        divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) s := by
  obtain ⟨P, hP, hfac⟩ := hadamard_factorization_of_growth
    (f := conductorCompletedL χ) (ρ := (3 / 2 : ℝ)) (by norm_num)
    (differentiable_conductorCompletedL χ hχ)
    ⟨0, conductorCompletedL_ne_zero_at_zero χ hp hχ⟩
    (conductorCompletedL_log_growth χ hχ)
  have hfloor : Nat.floor (3 / 2 : ℝ) = 1 := by
    apply (Nat.floor_eq_iff (by norm_num)).mpr
    norm_num
  refine ⟨P, by simpa [hfloor] using hP, fun s => ?_⟩
  simpa [hfloor, conductorCompletedL_analyticOrderNatAt_zero χ hp hχ] using hfac s

theorem conductorCompletedL_logDeriv_hasSum (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hχ : χ ≠ 1) :
    ∃ B : ℂ, ∀ s : ℂ, conductorCompletedL χ s ≠ 0 →
      HasSum (fun p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ) =>
        1 / (s - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p)
        (logDeriv (conductorCompletedL χ) s - B) := by
  obtain ⟨P, hP, hfac⟩ := conductorCompletedL_hadamard_factorization χ hp hχ
  have hsum := conductorCompletedL_zeroIndex_summable_inv_sq χ hp hχ
  refine ⟨P.coeff 1, fun s hs => ?_⟩
  have hsindex : ∀ p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ),
      s ≠ divisorZeroIndex₀Val p := by
    intro p hsp
    exact hs (hsp ▸ conductorCompletedL_zeroIndex_vanishes χ hχ p)
  have hprod : divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) s ≠ 0 :=
    divisorCanonicalProduct_ne_zero_of_forall_ne 1 (conductorCompletedL χ) hsum hsindex
  have hpd : P.derivative.eval s = P.coeff 1 := by
    have heq := congrArg Polynomial.derivative (Polynomial.eq_X_add_C_of_degree_le_one hP)
    simpa using congrArg (Polynomial.eval s) heq
  have hdexp : HasDerivAt (fun z : ℂ => Complex.exp (P.eval z))
      (Complex.exp (P.eval s) * P.derivative.eval s) s := by
    simpa only [Function.comp_def] using
      ((Complex.hasDerivAt_exp (P.eval s)).comp s (P.hasDerivAt s))
  have hexp : logDeriv (fun z : ℂ => Complex.exp (P.eval z)) s = P.coeff 1 := by
    rw [logDeriv_apply, hdexp.deriv,
      hpd]
    field_simp
  have hlog : logDeriv (conductorCompletedL χ) s = P.coeff 1 +
      ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) (Set.univ : Set ℂ),
        (1 / (s - divisorZeroIndex₀Val p) + 1 / divisorZeroIndex₀Val p) := by
    calc
      _ = logDeriv (fun z => Complex.exp (P.eval z) *
          divisorCanonicalProduct 1 (conductorCompletedL χ) (Set.univ : Set ℂ) z) s :=
        congrArg (fun f : ℂ → ℂ => logDeriv f s) (funext hfac)
      _ = _ := by
        rw [logDeriv_fun_mul (f := fun z : ℂ => Complex.exp (P.eval z)) s
          (Complex.exp_ne_zero (P.eval s)) hprod hdexp.differentiableAt
          (differentiableAt_divisorCanonicalProduct_univ 1 (conductorCompletedL χ) hsum s),
          hexp, logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne hsum hsindex]
  rw [hlog, add_sub_cancel_left]
  exact (summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq hsum hsindex).hasSum

end

theorem reflected_reciprocal_tsum {ι : Type*} (ρ : ι → ℂ) (e : ι ≃ ι)
    (he : ∀ i, ρ (e i) = 1 - ρ i) :
    ∑' i, (1 / ((-1 : ℂ) - ρ i)).re = -∑' i, (1 / ((2 : ℂ) - ρ i)).re := by
  calc
    ∑' i, (1 / ((-1 : ℂ) - ρ i)).re =
        ∑' i, (1 / ((-1 : ℂ) - ρ (e i))).re := (e.tsum_eq _).symm
    _ = ∑' i, -(1 / ((2 : ℂ) - ρ i)).re := by
      apply tsum_congr
      intro i
      rw [he i, show (-1 : ℂ) - (1 - ρ i) = -((2 : ℂ) - ρ i) by ring,
        div_neg, Complex.neg_re]
    _ = -∑' i, (1 / ((2 : ℂ) - ρ i)).re := tsum_neg

open _root_.Complex DirichletCharacter

theorem primitive_rootNumber_ne_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    rootNumber χ ≠ 0 := by
  intro hroot
  have hzero : completedLFunction χ 2 = 0 := by
    have h := hχ.completedLFunction_one_sub (-1)
    norm_num [hroot] at h
    exact h
  exact completedL_ne_zero_of_one_le_re χ hχ1 (by norm_num) hzero

theorem logDeriv_conductorCompletedL_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    logDeriv (conductorCompletedL χ) (1 - s) =
      -logDeriv (conductorCompletedL χ⁻¹) s := by
  have hfun : (fun z => conductorCompletedL χ (1 - z)) =
      (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) :=
    funext (conductorCompletedL_one_sub χ hχ)
  have h := congrArg (fun f => logDeriv f s) hfun
  rw [logDeriv_fun_comp (differentiable_conductorCompletedL χ hχ1 (1 - s))
    (by fun_prop), logDeriv_const_mul s _ (primitive_rootNumber_ne_zero hχ hχ1)] at h
  simpa using congrArg Neg.neg h

theorem analyticOrderAt_conductorCompletedL_one_sub {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (conductorCompletedL χ) (1 - s) =
      analyticOrderAt (conductorCompletedL χ⁻¹) s := by
  have hfun : (fun z => conductorCompletedL χ (1 - z)) =
      (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) :=
    funext (conductorCompletedL_one_sub χ hχ)
  have hcomp : analyticOrderAt (fun z => conductorCompletedL χ (1 - z)) s =
      analyticOrderAt (conductorCompletedL χ) (1 - s) := by
    simpa only [Function.comp_def] using
      (analyticOrderAt_comp_of_deriv_ne_zero (f := conductorCompletedL χ) (z₀ := s)
        (g := fun z : ℂ => 1 - z) (by fun_prop) (by simp))
  have hconst : analyticOrderAt (fun _ : ℂ => rootNumber χ) s = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr (primitive_rootNumber_ne_zero hχ hχ1)
  calc
    analyticOrderAt (conductorCompletedL χ) (1 - s) =
        analyticOrderAt (fun z => rootNumber χ * conductorCompletedL χ⁻¹ z) s :=
      hcomp.symm.trans (congrArg (fun f => analyticOrderAt f s) hfun)
    _ = analyticOrderAt (fun _ : ℂ => rootNumber χ) s +
        analyticOrderAt (conductorCompletedL χ⁻¹) s := by
      exact analyticOrderAt_mul analyticAt_const
        ((differentiable_conductorCompletedL χ⁻¹ (inv_ne_one.mpr hχ1)).analyticAt s)
    _ = analyticOrderAt (conductorCompletedL χ⁻¹) s := by rw [hconst, zero_add]

theorem completed_reciprocal_tsum_reflection {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hquad : χ.IsQuadratic) :
    (∑' j : Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z),
      (1 / ((-1 : ℂ) - j.1)).re) =
      -∑' j : Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z),
        (1 / ((2 : ℂ) - j.1)).re := by
  let e : (Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)) ≃
      (Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)) :=
    Equiv.sigmaCongr (Equiv.subLeft (1 : ℂ)) fun z => finCongr (by
      unfold analyticOrderNatAt
      apply congrArg ENat.toNat
      simpa only [hquad.inv, Equiv.subLeft_apply] using
        (analyticOrderAt_conductorCompletedL_one_sub hχ hχ1 z).symm)
  exact reflected_reciprocal_tsum Sigma.fst e (fun _ => rfl)

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

local notation "ZeroIndices" => Σ z : ℂ, Fin (analyticOrderNatAt (conductorCompletedL χ) z)

theorem real_logDeriv_conductorCompletedL_eq_tsum
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) (hquad : χ.IsQuadratic) (B : ℝ)
    (hbase : Summable (fun j : ZeroIndices => (1 / j.1).re))
    (hexp : ∀ x : ℝ, x = -1 ∨ 1 < x →
      HasSum (fun j : ZeroIndices => (1 / ((x : ℂ) - j.1) + 1 / j.1).re)
        ((logDeriv (conductorCompletedL χ) (x : ℂ)).re - B))
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (conductorCompletedL χ) (s : ℂ)).re =
      ∑' j : ZeroIndices, (1 / ((s : ℂ) - j.1)).re := by
  let C : ℝ := ∑' j : ZeroIndices, (1 / j.1).re
  have hsplit (x : ℝ) (hx : x = -1 ∨ 1 < x) :
      (∑' j : ZeroIndices, (1 / ((x : ℂ) - j.1)).re) =
        (logDeriv (conductorCompletedL χ) (x : ℂ)).re - B - C := by
    apply HasSum.tsum_eq
    convert (hexp x hx).sub hbase.hasSum using 1
    ext j
    simp only [Complex.add_re, add_sub_cancel_right]
  have hreflection : (logDeriv (conductorCompletedL χ) (-1)).re =
      -(logDeriv (conductorCompletedL χ) 2).re := by
    have h := logDeriv_conductorCompletedL_one_sub hχ hχ1 2
    rw [hquad.inv] at h
    have harg : (1 - (2 : ℂ)) = -1 := by ring
    simpa only [harg, Complex.neg_re] using congrArg Complex.re h
  have hcancel : B + C = 0 := by
    have htwo := hsplit 2 (.inr (by norm_num))
    have hneg := hsplit (-1) (.inl rfl)
    have hzero := completed_reciprocal_tsum_reflection hχ hχ1 hquad
    norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one] at htwo hneg
    linarith
  rw [hsplit s (.inr hs)]
  linarith

end WeightedTorusJets

namespace RealCharacterAnalysis

open _root_.Complex _root_.SiegelZeros.Complex.Hadamard

theorem toNat_divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (z : ℂ) :
    Int.toNat (MeromorphicOn.divisor f Set.univ z) = analyticOrderNatAt f z := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ z)]
  unfold analyticOrderNatAt
  cases h : analyticOrderAt f z <;> simp

noncomputable def divisorIndexEquivAnalytic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    divisorZeroIndex₀ f Set.univ ≃ Σ z : ℂ, Fin (analyticOrderNatAt f z) := by
  have horder : analyticOrderNatAt f 0 = 0 := by
    rw [analyticOrderNatAt, (hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
    rfl
  have horigin : ∀ p : divisorZeroIndex f Set.univ, p.1 ≠ 0 := by
    rintro ⟨z, i⟩ hz
    dsimp at hz
    subst z
    have hi : Fin 0 := by
      simpa only [toNat_divisor_eq_analyticOrderNatAt hf, horder] using i
    exact Fin.elim0 hi
  exact (Equiv.subtypeUnivEquiv horigin).trans
    (Equiv.sigmaCongrRight fun z => finCongr (toNat_divisor_eq_analyticOrderNatAt hf z))

theorem divisorIndexEquivAnalytic_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (p : divisorZeroIndex₀ f Set.univ) :
    (divisorIndexEquivAnalytic hf h0 p).1 = divisorZeroIndex₀Val p := rfl

theorem tsum_divisorIndex_eq_analytic {E : Type*} [NormedAddCommGroup E] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (F : ℂ → E) :
    (∑' p : divisorZeroIndex₀ f Set.univ, F (divisorZeroIndex₀Val p)) =
      ∑' p : Σ z : ℂ, Fin (analyticOrderNatAt f z), F p.1 := by
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val] using
    (divisorIndexEquivAnalytic hf h0).tsum_eq (fun p => F p.1)

theorem summable_divisorIndex_iff_analytic {E : Type*} [NormedAddCommGroup E] {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (F : ℂ → E) :
    Summable (fun p : divisorZeroIndex₀ f Set.univ => F (divisorZeroIndex₀Val p)) ↔
      Summable (fun p : Σ z : ℂ, Fin (analyticOrderNatAt f z) => F p.1) := by
  simpa only [Function.comp_def, divisorIndexEquivAnalytic_val] using
    (divisorIndexEquivAnalytic hf h0).summable_iff (f := fun p => F p.1)

end RealCharacterAnalysis

end SiegelZeros

end OAI
