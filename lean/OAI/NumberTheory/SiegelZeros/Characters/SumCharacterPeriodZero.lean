import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.DirichletRealZeroBound

namespace OAI

namespace SiegelZeros

section
section IntroDependency0

section GrowthDependency0

namespace WeightedTorusJets

open _root_.Finset MeasureTheory
open scoped Fin.NatCast

theorem sum_character_period_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  have heq : ∀ a : Fin q, (ZMod.finEquiv q).toEquiv a = (a : ℕ) := by
    intro a
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      change a = ((a : ℕ) : Fin (q + 1))
      exact (Fin.cast_val_eq_self a).symm
  have hsum := Equiv.sum_comp (ZMod.finEquiv q).toEquiv (fun a => χ a)
  simpa only [heq, MulChar.sum_eq_zero_of_ne_one hχ] using hsum

theorem norm_sum_character_range_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ < q := by
  classical
  have hperiod : Function.Periodic (fun n => ∑ k ∈ range n, χ (k : ZMod q)) q := by
    intro n
    change (∑ k ∈ range (n + q), χ (k : ZMod q)) = ∑ k ∈ range n, χ (k : ZMod q)
    rw [Nat.add_comm n q, Finset.sum_range_add, sum_character_period_eq_zero χ hχ]
    simp
  rw [← hperiod.map_mod_nat n]
  have hbound : ‖∑ k ∈ range (n % q), χ (k : ZMod q)‖ ≤ (n % q : ℕ) := by
    calc
      _ ≤ ∑ k ∈ range (n % q), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (n % q), (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (n % q : ℕ) := by simp
  exact hbound.trans_lt (by exact_mod_cast Nat.mod_lt n (NeZero.pos q))

theorem norm_sum_character_Icc_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ < q := by
  have hzero : χ 0 = 0 := χ.map_zero' (hχ ∘ χ.level_one')
  have hbound := norm_sum_character_range_lt χ hχ (n + 1)
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos n), Nat.cast_zero, hzero, zero_add,
    Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc] at hbound
  exact hbound

theorem isBigO_sum_character_Icc_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))
      (fun _ => (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨q, Filter.Eventually.of_forall fun n => ?_⟩
  simpa using (norm_sum_character_Icc_lt χ hχ n).le

theorem mellin_partial_sum_neg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-s) =
      ∫ t : ℝ in Set.Ioi 1,
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Set.Ici_subset_Ioi.mpr zero_lt_one) ?_]
  · rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul, neg_add, sub_eq_add_neg]
    exact mul_comm _ _
  · intro t ht
    have ht1 : t < 1 := lt_of_not_ge ht.2
    simp [Nat.floor_eq_zero.mpr ht1]

theorem differentiableAt_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) s := by
  have hmeas : Measurable (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, χ (k : ZMod q))).comp
      Nat.measurable_floor
  have hmem : MemLp (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) ⊤ :=
    memLp_top_of_bound hmeas.aestronglyMeasurable q
      (Filter.Eventually.of_forall fun t => (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le)
  have htop : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (fun t => t ^ (-(0 : ℝ))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨q, Filter.Eventually.of_forall fun t => ?_⟩
    simpa using (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le
  have hbot : Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))
      (fun t => t ^ (-(-s.re - 1))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [Nat.floor_eq_zero.mpr ht]
  have hm : DifferentiableAt ℂ
      (mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q))) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      ((hmem.locallyIntegrable le_top).locallyIntegrableOn _) htop
      (by simpa using neg_neg_of_pos hs) hbot
    simp only [Complex.neg_re]
    linarith
  have hfun : (fun z : ℂ => z * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))) =
      (fun z : ℂ => z * mellin (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) (-z)) := by
    funext z
    rw [mellin_partial_sum_neg]
  rw [hfun]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

theorem LFunction_eq_partial_sum_integral {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  apply LSeries_eq_mul_integral (r := 0) _ le_rfl (zero_lt_one.trans hs)
  · exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  · simpa using isBigO_sum_character_Icc_one χ hχ

end WeightedTorusJets

namespace WeightedTorusJets

open _root_.Finset MeasureTheory
open scoped Topology

theorem LFunction_eq_partial_sum_integral_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = s * ∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1)) := by
  let U : Set ℂ := {z | 0 < z.re}
  let F := DirichletCharacter.LFunction χ
  let G : ℂ → ℂ := fun z => z * ∫ t : ℝ in Set.Ioi 1,
    (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(z + 1))
  have hUo : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hUc : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have hF : AnalyticOnNhd ℂ F U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact (differentiableAt_partial_sum_integral χ hχ hz).differentiableWithinAt
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hFG : F =ᶠ[𝓝 (2 : ℂ)] G := by
    filter_upwards [hV] with z hz
    exact LFunction_eq_partial_sum_integral χ hχ hz
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUc (by norm_num [U]) hFG hs

end WeightedTorusJets

end GrowthDependency0

section GrowthDependency1

open MeasureTheory Set

namespace WeightedTorusJets

 theorem integrableOn_min_mul_rpow {q r : ℝ} (hq : 0 ≤ q) (hr : r < -1) :
    IntegrableOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ => min x q * x ^ r) (Ioi 1) :=
    (continuous_id.min continuous_const).continuousOn.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))))
  apply ((integrableOn_Ioi_rpow_of_lt hr zero_lt_one).const_mul q).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min hx0 hq) (Real.rpow_nonneg hx0 _))]
  exact mul_le_mul_of_nonneg_right (min_le_right x q) (Real.rpow_nonneg hx0 _)

 theorem integral_min_mul_rpow_exact {q η : ℝ} (hq : 1 ≤ q) (hη : 0 < η) (hη1 : η < 1) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2)) =
      (q ^ η - 1) / η + q ^ η / (1 - η) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr : η - 2 < -1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0.le hr
  have hfirst : (∫ x : ℝ in 1..q, min x q * x ^ (η - 2)) = (q ^ η - 1) / η := by
    calc
      _ = ∫ x : ℝ in 1..q, x ^ (η - 1) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hq] at hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
        dsimp only
        rw [min_eq_left hx.2]
        calc
          _ = x ^ (1 + (η - 2)) := by rw [Real.rpow_add hx0, Real.rpow_one]
          _ = _ := by congr 1; ring
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith : -1 < η - 1))]
        simp only [show η - 1 + 1 = η by ring, Real.one_rpow]
  have htail : (∫ x : ℝ in Ioi q, min x q * x ^ (η - 2)) = q ^ η / (1 - η) := by
    calc
      _ = ∫ x : ℝ in Ioi q, q * x ^ (η - 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [min_eq_right hx.le]
      _ = q * (-q ^ (η - 2 + 1) / (η - 2 + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hr hq0]
      _ = _ := by
        have hp : q * q ^ (η - 1) = q ^ η := by
          calc
            _ = q ^ (1 + (η - 1)) := by rw [Real.rpow_add hq0, Real.rpow_one]
            _ = _ := by congr 1; ring
        rw [show η - 2 + 1 = η - 1 by ring]
        have hηn : η - 1 ≠ 0 := by linarith
        have hηn' : 1 - η ≠ 0 := by linarith
        field_simp
        nlinarith [hp]
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hq))
  rw [hfirst, htail] at hsplit
  exact hsplit.symm

 theorem integral_min_mul_rpow_le {q η σ : ℝ} (hq : 1 ≤ q) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) (hσ : 1 - η ≤ σ) :
    (∫ x : ℝ in Ioi 1, min x q * x ^ (-σ - 1)) ≤ q ^ η * (1 / η + 2) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hσ0 : 0 < σ := by linarith
  have hη1 : η < 1 := by linarith
  have hint := integrableOn_min_mul_rpow hq0 (by linarith : -σ - 1 < -1)
  have henv := integrableOn_min_mul_rpow hq0 (by linarith : η - 2 < -1)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, min x q * x ^ (η - 2) := by
      apply integral_mono_ae hint henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
        (le_min (le_trans zero_le_one hx.le) hq0)
    _ = (q ^ η - 1) / η + q ^ η / (1 - η) := integral_min_mul_rpow_exact hq hη hη1
    _ ≤ q ^ η * (1 / η + 2) := by
      have hp : 0 ≤ q ^ η := Real.rpow_nonneg hq0 _
      have hfirst : (q ^ η - 1) / η ≤ q ^ η / η :=
        div_le_div_of_nonneg_right (by linarith) hη.le
      have htail : q ^ η / (1 - η) ≤ 2 * q ^ η := by
        apply (div_le_iff₀ (by linarith : 0 < 1 - η)).mpr
        nlinarith
      calc
        _ ≤ q ^ η / η + 2 * q ^ η := add_le_add hfirst htail
        _ = _ := by ring

end WeightedTorusJets

end GrowthDependency1

namespace WeightedTorusJets

open _root_.Finset MeasureTheory

theorem norm_sum_character_Icc_le_min {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤ min t (q : ℝ) := by
  apply le_min
  · calc
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)‖ ≤
          ∑ k ∈ Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (⌊t⌋₊ : ℝ) := by simp
      _ ≤ t := Nat.floor_le ht
  · exact (norm_sum_character_Icc_lt χ hχ ⌊t⌋₊).le

theorem norm_LFunction_le_rpow_near_one {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    {q : ℕ} [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hre : 1 - η ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (2 / η + 4) * (q : ℝ) ^ η := by
  have hs : 0 < s.re := by linarith
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hint := integrableOn_min_mul_rpow (Nat.cast_nonneg q)
    (by linarith : -s.re - 1 < -1)
  have hI : ‖∫ t : ℝ in Set.Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, χ (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Set.Ioi 1, min t (q : ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have he : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (norm_sum_character_Icc_le_min χ hχ ht0.le)
      (Real.rpow_nonneg ht0.le _)
  have hbound := hI.trans (integral_min_mul_rpow_le hq1 hη hηhalf hre)
  rw [LFunction_eq_partial_sum_integral_of_re_pos χ hχ hs, norm_mul]
  calc
    ‖s‖ * _ ≤ 2 * ((q : ℝ) ^ η * (1 / η + 2)) :=
      mul_le_mul hnorm hbound (norm_nonneg _) (by norm_num)
    _ = (2 / η + 4) * (q : ℝ) ^ η := by ring

theorem LFunction_uniform_closedBall_bound (η : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ s ∈ Metric.closedBall (1 : ℂ) η,
          ‖DirichletCharacter.LFunction χ s‖ ≤ A * (q : ℝ) ^ η := by
  refine ⟨2 / η + 4, by positivity, ?_⟩
  intro q _ hq χ hχ s hs
  have hnorm : ‖s - 1‖ ≤ η := by simpa [Metric.mem_closedBall, dist_eq_norm] using hs
  have hreal : |s.re - 1| ≤ η := by
    simpa using (Complex.abs_re_le_norm (s - 1)).trans hnorm
  have hre : 1 - η ≤ s.re := by
    have := (abs_le.mp hreal).1
    linarith
  have hnorm2 : ‖s‖ ≤ 2 := by
    have ht := norm_le_norm_sub_add s (1 : ℂ)
    simp only [norm_one] at ht
    linarith
  exact norm_LFunction_le_rpow_near_one hη hηhalf hq χ hχ hre hnorm2

end WeightedTorusJets

end IntroDependency0

section IntroDependency2

open _root_.Complex Filter ArithmeticFunction MeasureTheory Set
open scoped Topology ComplexOrder LSeries.notation

namespace WeightedTorusJets

theorem one_le_zeta_mul_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    1 ≤ riemannZeta (x : ℂ) * DirichletCharacter.LFunction χ (x : ℂ) := by
  have hs : 1 < (x : ℂ).re := hx
  have hpos : 1 ≤ LSeries χ.zetaMul (x : ℂ) := by
    have h := (χ.LSeriesSummable_zetaMul hs).le_tsum 1
      (fun n _ => LSeries.term_nonneg (χ.zetaMul_nonneg hχ.sq_eq_one n) x)
    simpa [LSeries, LSeries.term_def, χ.isMultiplicative_zetaMul.map_one] using h
  have heq : LSeries χ.zetaMul (x : ℂ) =
      riemannZeta (x : ℂ) * DirichletCharacter.LFunction χ (x : ℂ) := by
    rw [DirichletCharacter.zetaMul, ← coe_mul, LSeries_convolution']
    · rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
      congr 1
      · simpa only [← natCoe_apply] using LSeries_zeta_eq_riemannZeta hs
      · exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply (x : ℂ)).symm
    · exact LSeriesSummable_zeta_iff.mpr hs
    · exact (LSeriesSummable_congr _ fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
        (ZMod.LSeriesSummable_of_one_lt_re χ hs)
  rwa [heq] at hpos

theorem riemannZeta_re_eq_tsum_rpow {x : ℝ} (hx : 1 < x) :
    (riemannZeta (x : ℂ)).re = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-x) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hx)]
  have heq (n : ℕ) : (1 : ℂ) / (n + 1) ^ (x : ℂ) =
      (((n + 1 : ℕ) : ℝ) ^ (-x) : ℝ) := by
    rw [Real.rpow_neg (by positivity), Complex.ofReal_inv,
      Complex.ofReal_cpow (by positivity)]
    simp
  simp_rw [heq]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

theorem riemannZeta_re_le_one_add_inv {x : ℝ} (hx : 1 < x) :
    (riemannZeta (x : ℂ)).re ≤ 1 + 1 / (x - 1) := by
  rw [riemannZeta_re_eq_tsum_rpow hx]
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-x)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs' : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-x)) :=
    (summable_nat_add_iff 1).mpr hs
  have hanti : AntitoneOn (fun y : ℝ => y ^ (-x)) (Ici 1) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : -x ≤ 0)).mono
      (by intro y hy; exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt (by linarith : -x < -1) (by norm_num))
    (by intro y hy; have hy' : 1 < y := by simpa using hy
        exact Real.rpow_nonneg (by linarith) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -x < -1) (by norm_num)] at htail
  norm_num only [Nat.cast_one] at htail
  have heq : -(1 : ℝ) ^ (-x + 1) / (-x + 1) = 1 / (x - 1) := by
    rw [Real.one_rpow, show -x + 1 = -(x - 1) by ring]
    exact neg_div_neg_eq 1 (x - 1)
  rw [heq] at htail
  rw [hs'.tsum_eq_zero_add]
  simpa using add_le_add_left htail 1

theorem one_div_zeta_re_le_LFunction_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    1 / (riemannZeta (x : ℂ)).re ≤ (DirichletCharacter.LFunction χ (x : ℂ)).re := by
  have hz := Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)
  have hprod := (Complex.le_def.mp (one_le_zeta_mul_LFunction χ hχ hx)).1
  rw [Complex.mul_re, ← hz.2, zero_mul, sub_zero, Complex.one_re] at hprod
  exact (div_le_iff₀ hz.1).mpr (by simpa [mul_comm] using hprod)

theorem half_mul_le_LFunction_one_add_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {t : ℝ} (ht : 0 < t)
    (ht1 : t ≤ 1) : t / 2 ≤ (DirichletCharacter.LFunction χ ((1 + t : ℝ) : ℂ)).re := by
  have hx : 1 < 1 + t := by linarith
  have hz := (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hx)).1
  have hupper : (riemannZeta ((1 + t : ℝ) : ℂ)).re ≤ 2 / t := by
    calc
      _ ≤ 1 + 1 / t := by simpa using riemannZeta_re_le_one_add_inv hx
      _ ≤ 2 / t := by
        apply (le_div_iff₀ ht).mpr
        rw [add_mul, one_mul, one_div_mul_cancel ht.ne']
        linarith
  calc
    t / 2 = 1 / (2 / t) := by rw [one_div_div]
    _ ≤ 1 / (riemannZeta ((1 + t : ℝ) : ℂ)).re :=
      one_div_le_one_div_of_le hz hupper
    _ ≤ (DirichletCharacter.LFunction χ ((1 + t : ℝ) : ℂ)).re :=
      one_div_zeta_re_le_LFunction_re χ hχ hx

end WeightedTorusJets

end IntroDependency2

section IntroDependency1

open _root_.Complex Filter
open scoped Topology ComplexConjugate

namespace RealCharacterAnalysis

end RealCharacterAnalysis

open _root_.Complex Filter ArithmeticFunction
open scoped Topology ComplexOrder LSeries.notation

namespace RealCharacterAnalysis

theorem lFunction_positive_of_one_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    0 < DirichletCharacter.LFunction χ (x : ℂ) := by
  have hpos : 0 < riemannZeta (x : ℂ) * DirichletCharacter.LFunction χ (x : ℂ) :=
    lt_of_lt_of_le zero_lt_one (WeightedTorusJets.one_le_zeta_mul_LFunction χ hχ hx)
  have hzeta := riemannZeta_pos_of_one_lt hx
  have hdiv := div_pos hpos hzeta
  simpa only [mul_div_cancel_left₀ _ (ne_of_gt hzeta)] using hdiv

theorem lFunction_positive_at_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hne : χ ≠ 1) :
    0 < DirichletCharacter.LFunction χ 1 := by
  have hc : ContinuousAt (fun x : ℝ => DirichletCharacter.LFunction χ (x : ℂ)) 1 :=
    (DirichletCharacter.differentiable_LFunction hne).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hn : 0 ≤ DirichletCharacter.LFunction χ 1 := by
    apply ge_of_tendsto (hc.tendsto.mono_left
      (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (lFunction_positive_of_one_lt χ hχ hx).le
  exact lt_of_le_of_ne hn (DirichletCharacter.LFunction_apply_one_ne_zero hne).symm

end RealCharacterAnalysis

namespace WeightedTorusJets

theorem real_character_LFunction_eq_real_part {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    DirichletCharacter.LFunction χ (s : ℂ) =
      ((DirichletCharacter.LFunction χ (s : ℂ)).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using RealCharacterAnalysis.lFunction_real χ hne hreal s

theorem real_character_LFunction_one_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    0 < (DirichletCharacter.LFunction χ 1).re := by
  exact (Complex.pos_iff.mp (RealCharacterAnalysis.lFunction_positive_at_one χ
    ((RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal) hne)).1

theorem real_character_LFunction_re_zero_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (s : ℝ) :
    (DirichletCharacter.LFunction χ (s : ℂ)).re = 0 ↔
      DirichletCharacter.LFunction χ (s : ℂ) = 0 := by
  constructor
  · intro h
    rw [real_character_LFunction_eq_real_part χ hne hreal s, h, Complex.ofReal_zero]
  · intro h
    simp [h]

end WeightedTorusJets

end IntroDependency1

section IntroDependency3

open Metric

namespace WeightedTorusJets

theorem norm_second_deriv_le_of_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c x : ℂ} {R M : ℝ}
    (hR : 0 < R) (hx : dist x c ≤ R / 2)
    (hM : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) :
    ‖deriv (deriv f) x‖ ≤ 8 * M / R ^ 2 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := f) (c := x) (R := R / 2) 2 (half_pos hR) hf.diffContOnCl
    (fun z hz => hM z (by
      rw [mem_closedBall]
      have hz' : dist z x = R / 2 := mem_sphere.mp hz
      calc
        dist z c ≤ dist z x + dist x c := dist_triangle z x c
        _ ≤ R := by linarith))
  have h' : ‖deriv (deriv f) x‖ ≤ 2 * M / (R / 2) ^ 2 := by
    simpa [iteratedDeriv_succ] using h
  convert h' using 1
  ring

theorem real_deriv_eq_re_complex_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    deriv (fun x : ℝ => (f x).re) = fun x : ℝ => (deriv f x).re := by
  funext x
  exact (hf x).hasDerivAt.real_of_complex.deriv

theorem differentiable_real_restriction {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℝ (fun x : ℝ => (f x).re) := by
  intro x
  exact (hf x).hasDerivAt.real_of_complex.differentiableAt

theorem differentiable_deriv_real_restriction {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℝ (deriv (fun x : ℝ => (f x).re)) := by
  rw [real_deriv_eq_re_complex_deriv hf]
  exact differentiable_real_restriction hf.deriv

theorem real_second_deriv_eq_re_complex_second_deriv
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    deriv (deriv (fun x : ℝ => (f x).re)) =
      fun x : ℝ => (deriv (deriv f) x).re := by
  rw [real_deriv_eq_re_complex_deriv hf]
  exact real_deriv_eq_re_complex_deriv hf.deriv

theorem abs_real_second_deriv_le_of_closedBall
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R M x : ℝ}
    (hR : 0 < R) (hx : |x - 1| ≤ R / 2)
    (hM : ∀ z ∈ closedBall (1 : ℂ) R, ‖f z‖ ≤ M) :
    |deriv (deriv (fun t : ℝ => (f t).re)) x| ≤ 8 * M / R ^ 2 := by
  rw [real_second_deriv_eq_re_complex_second_deriv hf]
  refine (Complex.abs_re_le_norm _).trans
    (norm_second_deriv_le_of_closedBall hf hR ?_ hM)
  simpa only [← Complex.ofReal_one, Complex.isometry_ofReal.dist_eq, Real.dist_eq] using hx

end WeightedTorusJets

end IntroDependency3

section IntroDependency4

namespace WeightedTorusJets

theorem siegel_parameter_selection (ε C c₀ : ℝ) (hε : 0 < ε)
    (hC : 0 < C) (hc₀ : 0 < c₀) :
    let η := min ε (1 / 2)
    let κ := min (η / 2) (min (1 / (8 * C)) (c₀ * η / 2))
    0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 ∧ 0 < κ ∧ 0 < κ / 8 ∧
      ∀ q : ℝ, 3 ≤ q →
        let t := κ * q ^ (-η)
        0 < t ∧ t ≤ η / 2 ∧ t ≤ 1 / 2 ∧ 0 ≤ C * q ^ η ∧
          (C * q ^ η) * t ≤ 1 / 8 ∧ t * Real.log q ≤ c₀ / 2 ∧
          (κ / 8) * q ^ (-ε) ≤ t / 8 := by
  let η := min ε (1 / 2)
  let κ := min (η / 2) (min (1 / (8 * C)) (c₀ * η / 2))
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκη : κ ≤ η / 2 := min_le_left _ _
  have hκC : κ ≤ 1 / (8 * C) := (min_le_right _ _).trans (min_le_left _ _)
  have hκc : κ ≤ c₀ * η / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hCκ : C * κ ≤ 1 / 8 := by
    have h := (le_div_iff₀ (show 0 < 8 * C by positivity)).mp hκC
    nlinarith
  refine ⟨hη, hηε, hηhalf, hκ, by positivity, ?_⟩
  intro q hq
  have hqpos : 0 < q := by linarith
  have hqone : 1 ≤ q := by linarith
  have hp : 0 < q ^ η := Real.rpow_pos_of_pos hqpos η
  have hn : 0 < q ^ (-η) := Real.rpow_pos_of_pos hqpos (-η)
  have hn1 : q ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hqone (by linarith)
  let t := κ * q ^ (-η)
  have ht : 0 < t := mul_pos hκ hn
  have htκ : t ≤ κ := by simpa [t] using mul_le_mul_of_nonneg_left hn1 hκ.le
  have htη : t ≤ η / 2 := htκ.trans hκη
  refine ⟨ht, htη, by linarith, by positivity, ?_, ?_, ?_⟩
  · calc
      (C * q ^ η) * t = C * κ * (q ^ η * q ^ (-η)) := by dsimp [t]; ring
      _ = C * κ := by rw [← Real.rpow_add hqpos, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ 1 / 8 := hCκ
  · calc
      t * Real.log q ≤ t * (q ^ η / η) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hqpos.le hη) ht.le
      _ = κ / η := by
        dsimp [t]
        rw [Real.rpow_neg hqpos.le]
        field_simp
      _ ≤ c₀ / 2 := (div_le_iff₀ hη).mpr (by nlinarith [hκc])
  · have hr : q ^ (-ε) ≤ q ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
    calc
      (κ / 8) * q ^ (-ε) ≤ (κ / 8) * q ^ (-η) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = t / 8 := by dsimp [t]; ring

end WeightedTorusJets

end IntroDependency4

section IntroDependency5

namespace WeightedTorusJets

open Set

theorem value_one_lower_bound_of_real_zero_gap (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    {r B c ℓ : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hB : 0 ≤ B)
    (hc : 0 < c) (hℓ : 0 < ℓ)
    (hbound : ∀ x ∈ Icc (1 - r) (1 + r), |deriv (deriv f) x| ≤ B)
    (hBr : B * r ≤ 1 / 8) (hrℓ : r * ℓ ≤ c / 2)
    (hpositive : 0 < f 1) (hright : r / 2 ≤ f (1 + r))
    (hgap : ∀ β ∈ Ioo (0 : ℝ) 1, f β = 0 → c ≤ (1 - β) * ℓ) :
    r / 8 ≤ f 1 := by
  by_contra! hsmall
  obtain ⟨u, hu, hequ⟩ := exists_deriv_eq_slope f (show 1 < 1 + r by linarith)
    hf.continuous.continuousOn hf.differentiableOn
  obtain ⟨v, hv, heqv⟩ := exists_deriv_eq_slope f (show 1 - r < 1 by linarith)
    hf.continuous.continuousOn hf.differentiableOn
  have hvu : v < u := hv.2.trans hu.1
  have hdiff : deriv f u - deriv f v ≤ B * (u - v) :=
    (convex_Icc (1 - r) (1 + r)).image_sub_le_mul_sub_of_deriv_le
      hf'.continuous.continuousOn hf'.differentiableOn
      (fun x hx => (le_abs_self _).trans (hbound x (interior_subset hx)))
      v ⟨hv.1.le, (hvu.trans hu.2).le⟩ u ⟨(hv.1.trans hvu).le, hu.2.le⟩ hvu.le
  have hlength : u - v ≤ 2 * r := by linarith [hu.2, hv.1]
  have hdiff' : deriv f u - deriv f v ≤ B * (2 * r) :=
    hdiff.trans (mul_le_mul_of_nonneg_left hlength hB)
  have hplus : deriv f u * r = f (1 + r) - f 1 :=
    (eq_div_iff hr.ne').mp (by simpa only [add_sub_cancel_left] using hequ)
  have hden : (1 : ℝ) - (1 - r) = r := by ring
  rw [hden] at heqv
  have hminus : deriv f v * r = f 1 - f (1 - r) := (eq_div_iff hr.ne').mp heqv
  have hprod := mul_le_mul_of_nonneg_right hdiff' hr.le
  have hprodB := mul_le_mul_of_nonneg_right hBr hr.le
  have hleft : f (1 - r) < 0 := by nlinarith
  obtain ⟨β, hβ, hzero⟩ := intermediate_value_Ioo (show 1 - r ≤ 1 by linarith)
    hf.continuous.continuousOn ⟨hleft, hpositive⟩
  have hβpos : 0 < β := by linarith [hβ.1]
  have hcontr := hgap β ⟨hβpos, hβ.2⟩ hzero
  have hshort : (1 - β) * ℓ < r * ℓ :=
    mul_lt_mul_of_pos_right (by linarith [hβ.1]) hℓ
  linarith

end WeightedTorusJets

end IntroDependency5

section IntroDependency6
namespace WeightedTorusJets

theorem siegel_LFunction_one_lower_bound_of_zero_gap (hmain :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            c ≤ (1 - β) * Real.log (q : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          c * (q : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction χ 1).re := by
  obtain ⟨c₀, hc₀, hgap⟩ := hmain
  intro ε hε
  let η := min ε (1 / 2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  obtain ⟨A, hA, hnorm⟩ := LFunction_uniform_closedBall_bound η hη hηhalf
  let C := 8 * A / η ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let κ := min (η / 2) (min (1 / (8 * C)) (c₀ * η / 2))
  obtain ⟨_, _, _, _, hκ, hparameters⟩ := siegel_parameter_selection ε C c₀ hε hC hc₀
  refine ⟨κ / 8, hκ, ?_⟩
  intro q _ hq χ hprim hne hreal
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hr, hrη, hrhalf, hB, hBr, hrlog, hcompare⟩ := hparameters (q : ℝ) hqreal
  let r := κ * (q : ℝ) ^ (-η)
  let f := fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).re
  have hf := DirichletCharacter.differentiable_LFunction hne
  have hbound : ∀ x ∈ Set.Icc (1 - r) (1 + r),
      |deriv (deriv f) x| ≤ C * (q : ℝ) ^ η := by
    intro x hx
    have hx' : |x - 1| ≤ η / 2 := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
    calc
      |deriv (deriv f) x| ≤ 8 * (A * (q : ℝ) ^ η) / η ^ 2 :=
        abs_real_second_deriv_le_of_closedBall hf hη hx' (hnorm q hq χ hne)
      _ = C * (q : ℝ) ^ η := by dsimp [C]; ring
  have hlower : r / 8 ≤ f 1 := by
    apply value_one_lower_bound_of_real_zero_gap f
      (differentiable_real_restriction hf) (differentiable_deriv_real_restriction hf)
      hr hrhalf hB hc₀ (Real.log_pos (by linarith : (1 : ℝ) < q)) hbound hBr hrlog
    · simpa [f] using real_character_LFunction_one_re_pos χ hne hreal
    · exact half_mul_le_LFunction_one_add_re χ
        ((RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal) hr (by linarith)
    · intro β hβ hzero
      exact hgap q hq χ hprim hne hreal β
        ⟨hβ.1, hβ.2, (real_character_LFunction_re_zero_iff χ hne hreal β).mp hzero⟩
  exact hcompare.trans hlower

end WeightedTorusJets

end IntroDependency6

namespace WeightedTorusJets

theorem siegel_LFunction_one_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          c * (q : ℝ) ^ (-ε) ≤ (DirichletCharacter.LFunction χ 1).re :=
  siegel_LFunction_one_lower_bound_of_zero_gap dirichlet_real_zero_bound

end WeightedTorusJets

end

end SiegelZeros

end OAI
