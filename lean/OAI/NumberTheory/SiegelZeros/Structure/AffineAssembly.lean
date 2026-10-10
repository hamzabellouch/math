import Mathlib.Analysis.SpecificLimits.Normed
import OAI.NumberTheory.SiegelZeros.Estimates.AffineAsymptotics
import OAI.NumberTheory.SiegelZeros.Estimates.LowerBoundTransfer
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.CanonicalQuotient

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W01

open Complex Filter
open scoped Topology

theorem affine_of_factorization_circle_data {f P g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hfact : ∀ z : ℂ, f z = Complex.exp (g z) * P z)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (R r L : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hrlo : ∀ n, R n ≤ r n)
    (hrhi : ∀ n, r n ≤ 2 * R n) (hRtop : Tendsto R atTop atTop)
    (hL : ∀ n, 0 ≤ L n)
    (hLlim : Tendsto (fun n => L n / (R n) ^ 2) atTop (𝓝 0))
    (hP : ∀ n, ∀ z : ℂ, ‖z‖ = r n → P z ≠ 0)
    (hmin : ∀ n, ∀ z : ℂ, ‖z‖ = r n → -L n ≤ Real.log ‖P z‖) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = a + b * z := by
  let Q : ℕ → ℝ := fun n => 12 * C * ((1 + R n) * (Real.log (2 + R n)) ^ 2) + L n + 1
  have hr : ∀ n, 0 < r n := fun n => (hR n).trans_le (hrlo n)
  have hprof : ∀ n, 0 ≤ (1 + R n) * (Real.log (2 + R n)) ^ 2 := by
    intro n
    have := hR n
    positivity
  have hQ : ∀ n, 0 < Q n := by
    intro n
    dsimp [Q]
    have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hC) (hprof n)
    linarith [hL n]
  have hrTop : Tendsto r atTop atTop := tendsto_atTop_mono hrlo hRtop
  have hbound : ∀ n, ∀ z : ℂ, ‖z‖ = r n → (g z).re ≤ Q n := by
    intro n z hz
    have hfz : ‖f z‖ ≤ Real.exp (C * (1 + r n) * Real.log (2 + r n)) := by simpa only [hz] using hf z
    have hreal := re_logFactor_le_of_product_lower (hfact z) (hP n z hz) hfz (hmin n z hz)
    have hab := mul_le_mul_of_nonneg_left
      (doubled_radius_growth_le_logSquare (hR n).le (hr n).le (hrhi n)) hC
    dsimp [Q]
    nlinarith
  have hi : Tendsto (fun n => 1 / (R n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, one_div, inv_pow, zero_pow two_ne_zero] using
      (tendsto_inv_atTop_zero.comp hRtop).pow 2
  have hqR : Tendsto (fun n => Q n / (R n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hp := (tendsto_logSquare_profile_div_sq.comp hRtop).const_mul (12 * C)
    have hsum := (hp.add hLlim).add hi
    have he : (fun n => 12 * C * ((1 + R n) * Real.log (2 + R n) ^ 2 / R n ^ 2) +
        L n / R n ^ 2 + 1 / R n ^ 2) = (fun n => Q n / R n ^ 2) := by
      funext n
      dsimp [Q]
      ring
    simpa only [Function.comp_apply, mul_zero, add_zero, he] using hsum
  have hqr : Tendsto (fun n => Q n / (r n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun n => div_nonneg (hQ n).le (sq_nonneg _)) _ hqR
    intro n
    apply div_le_div_of_nonneg_left (hQ n).le (sq_pos_of_pos (hR n))
    exact pow_le_pow_left₀ (hR n).le (hrlo n) 2
  exact affine_of_re_circle_bounds hg r Q hr hQ hrTop hbound hqr

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.Workers.W01

open Complex Filter
open scoped Topology

theorem tendsto_dyadic_logSquare_bound (A : ℝ) :
    Tendsto (fun k : ℕ => (A * ((k : ℝ) + 4) ^ 2 * (2 : ℝ) ^ k) / ((2 : ℝ) ^ k) ^ 2)
      atTop (𝓝 0) := by
  have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (r := (1 / 2 : ℝ)) (by norm_num)
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
  have hs : Summable (fun k : ℕ => A * ((k : ℝ) + 4) ^ 2 * (1 / 2 : ℝ) ^ k) := by
    convert ((h2.add (h1.mul_left 8)).add (summable_geometric_two.mul_left 16)).mul_left A using 1
    funext k
    ring
  have he : (fun k : ℕ => A * ((k : ℝ) + 4) ^ 2 * (1 / 2 : ℝ) ^ k) =
      (fun k : ℕ => (A * ((k : ℝ) + 4) ^ 2 * (2 : ℝ) ^ k) / ((2 : ℝ) ^ k) ^ 2) := by
    funext k
    rw [div_pow, one_pow]
    field_simp
  rw [← he]
  exact hs.tendsto_atTop_zero

theorem affine_of_factorization_dyadic_minimum {f P g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hfact : ∀ z : ℂ, f z = Complex.exp (g z) * P z)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hf : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hmin : ∀ᶠ k : ℕ in atTop, ∃ r : ℝ, (2 : ℝ) ^ k ≤ r ∧ r ≤ 2 * (2 : ℝ) ^ k ∧
      ∀ z : ℂ, ‖z‖ = r → P z ≠ 0 ∧
        -(A * ((k : ℝ) + 4) ^ 2 * (2 : ℝ) ^ k) ≤ Real.log ‖P z‖) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = a + b * z := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmin
  choose r hrlo hrhi hcircle using (fun n : ℕ => hN (n + N) (Nat.le_add_left N n))
  apply affine_of_factorization_circle_data hg hfact hC hf
    (fun n => (2 : ℝ) ^ (n + N)) r
    (fun n => A * (((n + N : ℕ) : ℝ) + 4) ^ 2 * (2 : ℝ) ^ (n + N))
    (fun n => by positivity) hrlo hrhi
  · exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp (tendsto_add_atTop_nat N)
  · intro n
    positivity
  · exact (tendsto_dyadic_logSquare_bound A).comp (tendsto_add_atTop_nat N)
  · intro n z hz
    exact (hcircle n z hz).1
  · intro n z hz
    exact (hcircle n z hz).2

end SiegelZerosAwei.Workers.W01

end

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

theorem zeroSubproduct_univ (χ : DirichletCharacter ℂ q) :
    W03.zeroSubproduct χ Set.univ = canonicalProduct χ := by
  funext z
  exact tprod_univ (fun i : ZeroIndex χ => W03.genusOneFactor (zeroValue χ i) z)

theorem differentiable_canonicalProduct (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    Differentiable ℂ (canonicalProduct χ) := by
  rw [← zeroSubproduct_univ]
  exact W03.differentiable_zeroSubproduct χ hχ hprimitive Set.univ

theorem canonicalProduct_ne_zero_of_normalizedCompletion_ne_zero
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) : canonicalProduct χ z ≠ 0 := by
  rw [← zeroSubproduct_univ]
  apply W03.zeroSubproduct_ne_zero χ hχ hprimitive
  intro i _ heq
  apply hz
  rw [heq]
  exact zeroValue_is_zero χ i

theorem analyticOrderAt_canonicalProduct (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) (z : ℂ) :
    analyticOrderAt (canonicalProduct χ) z = analyticOrderAt (normalizedCompletion χ) z := by
  by_cases hz : normalizedCompletion χ z = 0
  · let r : {z : ℂ // normalizedCompletion χ z = 0} := ⟨z, hz⟩
    have hr : r.val ≠ 0 := by
      intro hzero
      have hpos := (normalizedCompletion_zero_mem_strip χ hχ hprimitive r.property).1
      simp only [hzero, Complex.zero_re, lt_self_iff_false] at hpos
    have htail : ∀ w, Multipliable (fun i : {i : ZeroIndex χ // i.1 ≠ r} =>
        W03.genusOneFactor (zeroValue χ i.val) w) :=
      W03.multipliable_zeroSubproduct χ hχ hprimitive {i | i.1 ≠ r}
    have hd : Differentiable ℂ (deletedRootProduct χ r) :=
      W03.differentiable_zeroSubproduct χ hχ hprimitive {i | i.1 ≠ r}
    have hne : deletedRootProduct χ r r.val ≠ 0 :=
      W03.deleted_root_subproduct_ne_zero χ hχ hprimitive r
    exact analyticOrderAt_canonicalProduct_at_root χ hχ r hr htail (hd.analyticAt r.val) hne
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr
      (canonicalProduct_ne_zero_of_normalizedCompletion_ne_zero χ hχ hprimitive hz)),
      analyticOrderAt_eq_zero.mpr (Or.inr hz)]

theorem actual_normalizedQuotient_entire_ne_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    Differentiable ℂ (normalizedQuotient χ (canonicalProduct χ)) ∧
      ∀ z, normalizedQuotient χ (canonicalProduct χ) z ≠ 0 :=
  normalizedQuotient_entire_ne_zero χ hχ (canonicalProduct χ)
    (differentiable_canonicalProduct χ hχ hprimitive)
    (analyticOrderAt_canonicalProduct χ hχ hprimitive)

theorem exists_entire_canonicalFactorization (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, normalizedCompletion χ z = Complex.exp (g z) * canonicalProduct χ z :=
  exists_entire_logarithm_normalizedQuotient χ hχ (canonicalProduct χ)
    (differentiable_canonicalProduct χ hχ hprimitive)
    (analyticOrderAt_canonicalProduct χ hχ hprimitive)

end SiegelZerosAwei.W51

end

section

namespace SiegelZerosAwei.W03

open Filter
open scoped Topology

variable {q : ℕ} [NeZero q]

theorem actual_zero_norm_lower_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : W51.ZeroIndex χ, ε ≤ ‖W51.zeroValue χ i‖ := by
  have h0 : W51.normalizedCompletion χ 0 ≠ 0 := by
    intro hz
    have h := (W51.normalizedCompletion_zero_mem_strip χ hχ hprimitive hz).1
    simp at h
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), W51.normalizedCompletion χ z ≠ 0 :=
    (W51.differentiable_normalizedCompletion χ hχ).continuous.continuousAt.eventually_ne h0
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp he
  refine ⟨ε, hε, fun i => ?_⟩
  by_contra hi
  apply hb (W51.zeroValue χ i) (by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hi)
  exact W51.zeroValue_is_zero χ i

theorem actual_dyadic_count_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
        C * ((k : ℝ) + 1) * (2 : ℝ) ^ k := by
  obtain ⟨C, hC, hg⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_order_one_growth χ hχ
  refine ⟨(6 * C + |Real.log ‖W51.normalizedCompletion χ 0‖|) / Real.log 2,
    by positivity, fun k => ?_⟩
  exact dyadic_count_bound_of_jensen
    (fun R => ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard : ℝ)) hC.le
    (fun R hR => actual_zero_count_le_of_growth χ hχ hprimitive hC.le hg hR) k

theorem actual_far_inverse_square_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ k : ℕ,
      ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
        C * ((k : ℝ) + 1) * (2 : ℝ) ^ k) (k : ℕ) :
    (∑' i : {i : W51.ZeroIndex χ // i ∉ zeroIndexFinset χ hχ (6 * (2 : ℝ) ^ k)},
      1 / ‖W51.zeroValue χ i.val‖ ^ 2) ≤ 4 * C * ((k : ℝ) + 3) / (2 : ℝ) ^ k := by
  classical
  apply Real.tsum_le_of_sum_le (fun i => by positivity)
  intro t
  have hh := WeightedTorusJets.W48.finite_tail_inverse_square_le (W51.zeroValue χ) C hC
    (W51.finite_zeroIndex_norm_le χ hχ) hcount (t.image Subtype.val) k (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      have hn : ¬ ‖W51.zeroValue χ j.val‖ ≤ 6 * (2 : ℝ) ^ k := by
        intro hb
        exact j.property ((mem_zeroIndexFinset χ hχ (6 * (2 : ℝ) ^ k) j.val).mpr hb)
      have hp : 0 < (2 : ℝ) ^ k := by positivity
      linarith [lt_of_not_ge hn])
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at hh
  exact hh

theorem dyadic_minimum_arithmetic {C B k R r n d u t v : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hk : 0 ≤ k) (hR : 0 < R)
    (hr : 0 ≤ r ∧ r ≤ 2 * R) (hn0 : 0 ≤ n) (hu0 : 0 ≤ u) (ht0 : 0 ≤ t)
    (hn : n ≤ 8 * C * (k + 4) * R) (hd : -3 * (k + 1) ≤ d)
    (hu : u ≤ B + 2 * C * (k + 3) * (k + 4))
    (ht : t ≤ 4 * C * (k + 3) / R)
    (hv : n * d - r * u - 6 * r ^ 2 * t ≤ v) :
    -((124 * C + 2 * B + 1) * (k + 4) ^ 2 * R) ≤ v := by
  have hcount : -(24 * C * (k + 4) ^ 2 * R) ≤ n * d := by
    have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ 3 * (k + 1) by positivity)
    have hpoly : (k + 4) * (k + 1) ≤ (k + 4) ^ 2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 24 * C * R by positivity)
    have hl := mul_le_mul_of_nonneg_left hd hn0
    nlinarith
  have hK : 1 ≤ (k + 4) ^ 2 := by nlinarith
  have hB' := mul_le_mul_of_nonneg_left hK hB
  have hpoly : (k + 3) * (k + 4) ≤ (k + 4) ^ 2 := by nlinarith
  have hC' := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 2 * C by positivity)
  have hu' : u ≤ (B + 2 * C) * (k + 4) ^ 2 := by nlinarith
  have hnear : r * u ≤ (2 * B + 4 * C) * (k + 4) ^ 2 * R := by
    have hm := mul_le_mul hr.2 hu' hu0 (show 0 ≤ 2 * R by positivity)
    nlinarith
  have htail : 6 * r ^ 2 * t ≤ 96 * C * (k + 4) ^ 2 * R := by
    have hr2 : r ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ hr.1 hr.2 2
    have hm := mul_le_mul hr2 ht ht0 (show 0 ≤ (2 * R) ^ 2 by positivity)
    have heq : (2 * R) ^ 2 * (4 * C * (k + 3) / R) = 16 * C * (k + 3) * R := by
      field_simp [hR.ne']
      ring
    rw [heq] at hm
    have hpoly' : k + 3 ≤ (k + 4) ^ 2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hpoly' (show 0 ≤ 96 * C * R by positivity)
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg (k + 4)) hR.le]

theorem dyadic_log_separation_lower (k : ℕ) :
    -3 * ((k : ℝ) + 1) ≤
      Real.log (1 / ((2 : ℝ) ^ k) ^ 2) - Real.log (6 * (2 : ℝ) ^ k) := by
  have hL : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log (6 * (2 : ℝ) ^ k) ≤ ((k : ℝ) + 3) * Real.log 2 := by
    calc
      _ ≤ Real.log (8 * (2 : ℝ) ^ k) := Real.log_le_log (by positivity) (by
        have hp : 0 ≤ (2 : ℝ) ^ k := by positivity
        nlinarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
          show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
        push_cast
        ring
  have hrecip : Real.log (1 / ((2 : ℝ) ^ k) ^ 2) = -2 * (k : ℝ) * Real.log 2 := by
    rw [one_div, Real.log_inv, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hrecip]
  have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ 3 * ((k : ℝ) + 1) by positivity)
  nlinarith

theorem actual_canonicalProduct_dyadic_minimum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop, ∃ r : ℝ,
      (2 : ℝ) ^ k ≤ r ∧ r ≤ 2 * (2 : ℝ) ^ k ∧
      ∀ z : ℂ, ‖z‖ = r → W51.canonicalProduct χ z ≠ 0 ∧
        -(A * ((k : ℝ) + 4) ^ 2 * (2 : ℝ) ^ k) ≤
          Real.log ‖W51.canonicalProduct χ z‖ := by
  classical
  obtain ⟨C, hC, hcount⟩ := actual_dyadic_count_bound χ hχ hprimitive
  let B : ℝ := ∑ i ∈ (W51.finite_zeroIndex_norm_le χ hχ 1).toFinset,
    1 / ‖W51.zeroValue χ i‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨124 * C + 2 * B + 1, by positivity, ?_⟩
  have hsep := WeightedTorusJets.W04.eventually_radius_avoiding_of_dyadic_count
    (W51.zeroValue χ) C (W51.finite_zeroIndex_norm_le χ hχ) hcount
  filter_upwards [hsep] with k hk
  obtain ⟨r, hr1, hr2, hrsep⟩ := hk
  refine ⟨r, hr1, hr2, fun z hz => ?_⟩
  let R : ℝ := 2 ^ k
  let S := zeroIndexFinset χ hχ (6 * R)
  have hR : 0 < R := by positivity
  have hSne : ∀ i ∈ S, ‖W51.zeroValue χ i‖ ≤ 6 * R := by
    intro i hi
    exact (mem_zeroIndexFinset χ hχ (6 * R) i).mp hi
  have hSupper : ∀ i ∈ S, ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ (k + 3) := by
    intro i hi
    have hh := hSne i hi
    rw [pow_add]
    norm_num
    change ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ k * 8
    dsimp only [R] at hh
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
  have hcard : (S.card : ℝ) ≤ 8 * C * ((k : ℝ) + 4) * R := by
    have hsset : (S : Set (W51.ZeroIndex χ)) ⊆
        {i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ (k + 3)} := hSupper
    have hn := Set.ncard_le_ncard hsset
      (W51.finite_zeroIndex_norm_le χ hχ ((2 : ℝ) ^ (k + 3)))
    rw [Set.ncard_coe_finset] at hn
    have hh := (show (S.card : ℝ) ≤
        ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ (2 : ℝ) ^ (k + 3)}.ncard : ℝ)
      from by exact_mod_cast hn).trans (hcount (k + 3))
    convert hh using 1
    dsimp only [R]
    push_cast
    rw [pow_add]
    ring
  have hnear := WeightedTorusJets.W48.finite_near_reciprocal_le (W51.zeroValue χ)
    C hC.le (W51.finite_zeroIndex_norm_le χ hχ) hcount S (k + 3) hSupper
  have hnear' : (∑ i ∈ S, 1 / ‖W51.zeroValue χ i‖) ≤
      B + 2 * C * ((k : ℝ) + 3) * ((k : ℝ) + 4) := by
    convert hnear using 1
    dsimp only [B]
    push_cast
    ring
  have htail := actual_far_inverse_square_le χ hχ hC.le hcount k
  have hlower := actual_canonicalProduct_near_far_lower χ hχ hprimitive hR ⟨hr1, hr2⟩
    (d := 1 / R ^ 2) (by positivity) hz (fun i hi => hrsep i (hSne i hi))
  refine ⟨hlower.2, ?_⟩
  apply dyadic_minimum_arithmetic hC.le hB (Nat.cast_nonneg k) hR
    ⟨le_trans hR.le hr1, hr2⟩ (by positivity)
    (Finset.sum_nonneg (fun i _ => by positivity))
    (tsum_nonneg (fun i => by positivity)) hcard (dyadic_log_separation_lower k)
    hnear' htail hlower.1

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.Workers.W01

variable {q : ℕ} [NeZero q]

theorem normalizedCompletion_affine_factorization
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) :
    ∃ a b : ℂ, ∀ z : ℂ,
      SiegelZerosAwei.W51.normalizedCompletion χ z =
        Complex.exp (a + b * z) * SiegelZerosAwei.W51.canonicalProduct χ z := by
  obtain ⟨g, hg, hfact⟩ := SiegelZerosAwei.W51.exists_entire_canonicalFactorization χ hχ hprimitive
  obtain ⟨C, hC, hgrowth⟩ := normalizedCompletion_order_one_growth χ hχ
  obtain ⟨A, hA, hminimum⟩ := SiegelZerosAwei.W03.actual_canonicalProduct_dyadic_minimum χ hχ hprimitive
  obtain ⟨a, b, hab⟩ := affine_of_factorization_dyadic_minimum hg hfact hC.le hA.le hgrowth hminimum
  exact ⟨a, b, fun z => by rw [hfact z, hab z]⟩

end SiegelZerosAwei.Workers.W01

end

end SiegelZeros

end OAI
