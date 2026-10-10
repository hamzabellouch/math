import Mathlib.Algebra.Order.Archimedean.Basic
import OAI.AlgebraicGeometry.PlaneCurves.ExponentSets
import OAI.AlgebraicGeometry.PlaneCurves.TorusConfigurations

namespace OAI

/-!
# Real and integral parameter choices and scaling
-/

section

namespace Nagata.Workers.W05

/-- Equation (rho): the boundary parameter satisfies the quadratic identity. -/
theorem rhoStar_identity (r : ℝ) (hr : 0 ≤ r) :
    2 * (3 * (Real.sqrt r - 3)) + (3 * (Real.sqrt r - 3)) ^ 2 / 9 = r - 9 := by
  have hs := Real.sq_sqrt hr
  nlinarith

/-- The inequalities preceding equation (rho), with positive multiplicity. -/
theorem rho_bounds (r d m : ℝ) (_hm : 0 < m)
    (hlow : 3 < d / m) (hupp : d / m < Real.sqrt r) :
    0 < 3 * (d / m - 3) ∧
      3 * (d / m - 3) < 3 * (Real.sqrt r - 3) ∧
      0 < 3 * (Real.sqrt r - 3) := by
  constructor
  · linarith
  constructor <;> linarith

/-- Equation (lambda), proved using an explicit open interval for lambda. -/
theorem exists_contraction (rho a : ℝ) (hrho : 0 ≤ rho) (hgap : rho < a) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ rho < lam * a - 9 * (1 - lam) := by
  have hden : 0 < a + 9 := by linarith
  have hfracpos : 0 < (rho + 9) / (a + 9) := div_pos (by linarith) hden
  have hfrac : (rho + 9) / (a + 9) < 1 :=
    (div_lt_one hden).2 (by linarith)
  obtain ⟨lam, hlow, hupp⟩ := exists_between hfrac
  refine ⟨lam, lt_trans hfracpos hlow, hupp, ?_⟩
  have hprod := (div_lt_iff₀ hden).1 hlow
  nlinarith

/-- Equation (scaling): a common positive integral multiple supplies the slack. -/
theorem exists_positive_scaling (q lam m : ℝ)
    (hq : 0 < q) (hlam : lam < 1) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ 1 ≤ q * (1 - lam) * ((n : ℝ) * m) := by
  have hc : 0 < q * (1 - lam) * m := mul_pos (mul_pos hq (by linarith)) hm
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (q * (1 - lam) * m))
  have hnreal : 0 < (n : ℝ) := lt_trans (div_pos zero_lt_one hc) hn
  have hprod := (div_lt_iff₀ hc).1 hn
  refine ⟨n, by exact_mod_cast hnreal, ?_⟩
  nlinarith [hprod]

/-- Common scaling leaves d/m, hence rho, unchanged. -/
theorem ratio_scale (d m : ℝ) (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) * d) / ((n : ℝ) * m) = d / m := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact mul_div_mul_left d m hn'

/-- The integer degree h agrees with m rho after viewing the data as reals. -/
theorem degree_eq_mul_rho (d m : ℝ) (hm : 0 < m) :
    3 * (d - 3 * m) = m * (3 * (d / m - 3)) := by
  field_simp [ne_of_gt hm]

/-- Positivity of the number of nonzero displacements. -/
theorem q_pos (r : ℝ) (hr : 10 ≤ r) : 0 < r - 9 := by linarith

end Nagata.Workers.W05

end

section

/-! Integer/floor and coefficient-index counts. These count formal coefficient
indices, not holomorphic sections; equality with section dimensions requires
the separate theta-basis theorem. -/
namespace Nagata.Workers.W05
open Nagata.FiniteExponents

theorem natural_integer_floor (D : ℕ) : ((D / 3 : ℕ) : ℤ) = (D : ℤ) / 3 := by
  exact Int.natCast_ediv D 3

/-- The finite natural coefficient index type enumerates the exact integer range. -/
theorem coefficient_index_iff (D : ℕ) (j : ℤ) :
    0 ≤ j ∧ j ≤ (D : ℤ) / 3 ↔
      ∃ i : Fin (D / 3 + 1), (i.val : ℤ) = j := by
  rw [← natural_integer_floor]
  constructor
  · rintro ⟨hj0, hjD⟩
    have hjnat : j.toNat ≤ D / 3 := by omega
    exact ⟨⟨j.toNat, by omega⟩, Int.toNat_of_nonneg hj0⟩
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    omega

/-- No column in the actual exponent set has a negative polynomial exponent,
and every exponent lies below the same integer floor bound. -/
theorem exponentSet_index_bounds {D M j K : ℤ} {a Δ : ℝ}
    (hM : 0 ≤ M) (hD : 3 * M < D)
    (hp : (j, K) ∈ exponentSet D M a Δ) : 0 ≤ j ∧ j ≤ D / 3 := by
  have hMD : M ≤ D / 3 :=
    (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 3)).mpr (by linarith)
  rcases mem_exponentSet_iff.mp hp with hfirst | hsecond | hzero
  · exact ⟨hfirst.1, hfirst.2.1.trans hMD⟩
  · exact ⟨by linarith [hsecond.1], hsecond.2.1⟩
  · exact ⟨by linarith [hzero.1], hzero.2.1⟩

/-- All source degrees up to the floor cutoff are nonnegative integers. -/
theorem sourceDegree_nonnegative {D j : ℤ} (hj : j ≤ D / 3) :
    0 ≤ sourceDegree D j := by
  have hprod := (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 3)).mp hj
  unfold sourceDegree
  linarith

/-- The first blocks have positive common degree under the source's strict ratio. -/
theorem commonDegree_positive {D M : ℤ} (hD : 3 * M < D) :
    0 < commonDegree D M := by
  unfold commonDegree
  linarith

/-- Exact integer index count for every first coefficient block. -/
theorem first_block_index_count (D M j : ℤ) (a Δ : ℝ)
    (hU : firstLower D M j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    (openIntegerInterval (firstLower D M j a Δ)
      (firstLower D M j a Δ + (commonDegree D M : ℝ))).card =
        (commonDegree D M).toNat := by
  have heq : openIntegerInterval (firstLower D M j a Δ)
      (firstLower D M j a Δ + (commonDegree D M : ℝ)) =
      Nagata.W09.thetaIndices (firstLower D M j a Δ) (commonDegree D M) := by
    ext K
    exact mem_openIntegerInterval.trans (Nagata.W09.mem_thetaIndices_iff hU).symm
  rw [heq]
  exact Nagata.W09.card_thetaIndices _ _

/-- Exact integer index count for every positive-degree second coefficient block. -/
theorem second_block_index_count (D j : ℤ) (a Δ : ℝ)
    (hU : secondLower D j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    (openIntegerInterval (secondLower D j a Δ)
      (secondLower D j a Δ + (sourceDegree D j : ℝ))).card =
        (sourceDegree D j).toNat := by
  have heq : openIntegerInterval (secondLower D j a Δ)
      (secondLower D j a Δ + (sourceDegree D j : ℝ)) =
      Nagata.W09.thetaIndices (secondLower D j a Δ) (sourceDegree D j) := by
    ext K
    exact mem_openIntegerInterval.trans (Nagata.W09.mem_thetaIndices_iff hU).symm
  rw [heq]
  exact Nagata.W09.card_thetaIndices _ _

/-- A zero source degree is exactly the final index and forces divisibility by 3. -/
theorem zero_source_degree_last {D j : ℤ} (hz : sourceDegree D j = 0) :
    j = D / 3 ∧ 3 ∣ D := by
  unfold sourceDegree at hz
  have heq : D = 3 * j := by omega
  refine ⟨?_, ⟨j, heq⟩⟩
  omega

end Nagata.Workers.W05

end

section

/-! Joint numerical existence in §2. All section-space and geometric bridges remain
separate. In particular the theorem makes no claim about universal systems. -/
namespace Nagata.Workers.W05

/-- Simultaneously choose the contraction, integral scaling, nonintegral delta,
and nine marked real exponents required before the elliptic construction. -/
theorem exists_numeric_choices (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / (m : ℝ))
    (hupp : (d : ℝ) / (m : ℝ) < Real.sqrt (r : ℝ)) :
    ∃ (n : ℕ) (lam Δ : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ 0 < lam ∧ lam < 1 ∧
      1 ≤ ((r : ℝ) - 9) * (1 - lam) * ((n * m : ℕ) : ℝ) ∧
      0 < Δ ∧ Δ < 1 / 2 ∧
      (3 * ((d : ℝ) / (m : ℝ) - 3)) +
          Δ * (3 * ((d : ℝ) / (m : ℝ) - 3)) / 9 <
        lam * (3 * (Real.sqrt (r : ℝ) - 3)) - 9 * (1 - lam) ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, (1 / 2 - x i)) = Δ ∧
      (∀ (j : Fin (n * m + 1)) (k : ℤ),
        (3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ))) / 9 *
          (3 * (Real.sqrt (r : ℝ) - 3) - Δ) +
          (((n * m : ℕ) : ℝ) - (j.val : ℝ)) *
            (3 * (Real.sqrt (r : ℝ) - 3)) ≠ k) ∧
      (∀ (j : Fin (n * d / 3 + 1)), n * m < j.val →
        0 < ((n * d : ℕ) : ℝ) - 3 * (j.val : ℝ) → ∀ k : ℤ,
        ((3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ))) -
          9 * ((j.val : ℝ) - ((n * m : ℕ) : ℝ))) / 9 *
            (3 * (Real.sqrt (r : ℝ) - 3) - Δ) ≠ k) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hrR : (10 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨hρ, hρa, _⟩ := rho_bounds (r : ℝ) (d : ℝ) (m : ℝ) hmR hlow hupp
  obtain ⟨lam, hlam0, hlam1, hgap⟩ :=
    exists_contraction _ _ (le_of_lt hρ) hρa
  obtain ⟨n, hn, hscale⟩ :=
    exists_positive_scaling ((r : ℝ) - 9) lam (m : ℝ) (q_pos _ hrR) hlam1 hmR
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < (d : ℝ) - 3 * (m : ℝ) := by
    have hprod := (lt_div_iff₀ hmR).mp hlow
    linarith
  have hscaled : 0 < 3 * (((n * d : ℕ) : ℝ) - 3 * ((n * m : ℕ) : ℝ)) := by
    push_cast
    nlinarith [mul_pos hnR hd]
  obtain ⟨Δ, hΔ, hhalf, hslack, hnonint1, hnonint2⟩ :=
    Nagata.W06.exists_source_nonintegral_delta
      (m := n * m) (u₀ := n * d / 3)
      (d := ((n * d : ℕ) : ℝ))
      (ρstar := 3 * (Real.sqrt (r : ℝ) - 3))
      hscaled rfl hρ hgap
  obtain ⟨x, hxinj, hxbounds, hxsum⟩ := Nagata.W06.exists_marked_parameters hΔ hhalf
  refine ⟨n, lam, Δ, x, hn, hlam0, hlam1, ?_, hΔ, hhalf, hslack,
    hxinj, hxbounds, hxsum, hnonint1, hnonint2⟩
  simpa only [Nat.cast_mul] using hscale

end Nagata.Workers.W05

end

section

namespace Nagata.Workers.W05
open Nagata.FiniteExponents

theorem firstLower_nonintegral_of_fin (D M : ℕ) (a Δ : ℝ)
    (h : ∀ (i : Fin (M + 1)) (k : ℤ),
      (3 * ((D : ℝ) - 3 * M)) / 9 * (a - Δ) +
        ((M : ℝ) - (i.val : ℝ)) * a ≠ k)
    (j : ℤ) (hj0 : 0 ≤ j) (hjM : j ≤ M) :
    firstLower (D : ℤ) (M : ℤ) j a Δ ∉ Set.range (Int.cast : ℤ → ℝ) := by
  let i : Fin (M + 1) := ⟨j.toNat, by omega⟩
  have hi : (i.val : ℝ) = (j : ℝ) := by
    dsimp [i]
    exact_mod_cast Int.toNat_of_nonneg hj0
  rintro ⟨k, hk⟩
  apply h i k
  rw [hi]
  simpa [firstLower, commonDegree] using hk.symm

theorem secondLower_nonintegral_of_fin (D M : ℕ) (a Δ : ℝ)
    (h : ∀ (i : Fin (D / 3 + 1)), M < i.val →
      0 < (D : ℝ) - 3 * (i.val : ℝ) → ∀ k : ℤ,
      ((3 * ((D : ℝ) - 3 * M)) - 9 * ((i.val : ℝ) - (M : ℝ))) / 9 *
        (a - Δ) ≠ k)
    (j : ℤ) (hjM : (M : ℤ) < j) (hjD : j ≤ (D : ℤ) / 3)
    (hjpos : 0 < (D : ℤ) - 3 * j) :
    secondLower (D : ℤ) j a Δ ∉ Set.range (Int.cast : ℤ → ℝ) := by
  have hj0 : 0 ≤ j := by omega
  obtain ⟨i, hi⟩ := (coefficient_index_iff D j).mp ⟨hj0, hjD⟩
  have hiR : (i.val : ℝ) = (j : ℝ) := by exact_mod_cast hi
  have hiM : M < i.val := by omega
  have hipos : 0 < (D : ℝ) - 3 * (i.val : ℝ) := by
    rw [hiR]
    exact_mod_cast hjpos
  rintro ⟨k, hk⟩
  apply h i hiM hipos k
  rw [hiR]
  have hnum : 3 * ((D : ℝ) - 3 * M) - 9 * ((j : ℝ) - M) =
      3 * ((D : ℝ) - 3 * j) := by ring
  rw [hnum]
  simpa [secondLower, sourceDegree] using hk.symm

end Nagata.Workers.W05

end

section

namespace Nagata.Workers.W05
open scoped BigOperators

/-- All fixed scalar choices from equations rho/lambda/scaling/delta/nonintegral/
marked-parameters, with actual scaled natural degrees and multiplicities. -/
theorem exists_scaled_parameters (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r) :
    ∃ (n D M q : ℕ) (rho a h lam Δ eta : ℝ) (x : Fin 9 → ℝ),
      0 < n ∧ D = n * d ∧ M = n * m ∧ q = r - 9 ∧
      0 < D ∧ 0 < M ∧ 0 < q ∧ M ≤ D / 3 ∧
      (D : ℝ) / M = (d : ℝ) / m ∧
      rho = 3 * ((D : ℝ) / M - 3) ∧ a = 3 * (Real.sqrt r - 3) ∧
      h = 3 * ((D : ℝ) - 3 * M) ∧ h = (M : ℝ) * rho ∧
      0 < rho ∧ rho < a ∧ 0 < a ∧ 0 < h ∧
      2 * a + a ^ 2 / 9 = (q : ℝ) ∧
      0 < lam ∧ lam < 1 ∧ rho < lam * a - 9 * (1 - lam) ∧
      1 ≤ (q : ℝ) * (1 - lam) * M ∧
      0 < Δ ∧ Δ < 1 / 2 ∧ rho + Δ * rho / 9 < lam * a - 9 * (1 - lam) ∧
      (∀ (j : Fin (M + 1)) (k : ℤ),
        h / 9 * (a - Δ) + ((M : ℝ) - (j.val : ℝ)) * a ≠ k) ∧
      (∀ (j : Fin (D / 3 + 1)), M < j.val → 0 < (D : ℝ) - 3 * (j.val : ℝ) →
        ∀ k : ℤ, (h - 9 * ((j.val : ℝ) - (M : ℝ))) / 9 * (a - Δ) ≠ k) ∧
      Function.Injective x ∧ (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      (∑ i : Fin 9, (1 / 2 - x i)) = Δ ∧
      (∑ i : Fin 9, x i) = 9 / 2 - Δ ∧
      eta = ((∑ i : Fin 9, x i) + a) / 3 ∧
      3 * eta = (∑ i : Fin 9, x i) + a := by
  obtain ⟨n, lam, Δ, x, hn, hlam0, hlam1, hscale, hΔ, hhalf, hslack,
    hxinj, hxbounds, hxsum, hnonint1, hnonint2⟩ :=
    exists_numeric_choices r d m hr hm hlow hupp
  let D := n * d
  let M := n * m
  let rho : ℝ := 3 * ((d : ℝ) / m - 3)
  let a : ℝ := 3 * (Real.sqrt r - 3)
  let h : ℝ := 3 * ((D : ℝ) - 3 * M)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : 0 < M := Nat.mul_pos hn hm
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdegree : 3 * m < d := by
    have ht := (lt_div_iff₀ hmR).mp hlow
    exact_mod_cast ht
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hdegree
  have hD : 0 < D := Nat.mul_pos hn hd
  have hscaleddegree : 3 * M < D := by
    dsimp [D, M]
    simpa only [Nat.mul_left_comm n 3 m] using Nat.mul_lt_mul_of_pos_left hdegree hn
  have hu0 : M ≤ D / 3 := (Nat.le_div_iff_mul_le (by decide)).2 (by
    simpa only [Nat.mul_comm M 3] using le_of_lt hscaleddegree)
  have hratio : (D : ℝ) / M = (d : ℝ) / m := by
    dsimp [D, M]
    simpa only [Nat.cast_mul] using ratio_scale (d : ℝ) (m : ℝ) n hn
  have hratioeq : rho = 3 * ((D : ℝ) / M - 3) := by rw [hratio]
  have hhrho : h = (M : ℝ) * rho := by
    rw [hratioeq]
    exact degree_eq_mul_rho (D : ℝ) (M : ℝ) hMR
  obtain ⟨hrho, hrhoa, ha⟩ := rho_bounds (r : ℝ) (d : ℝ) (m : ℝ) hmR hlow hupp
  have hh : 0 < h := by rw [hhrho]; exact mul_pos hMR hrho
  have hr9 : 9 ≤ r := le_trans (by decide : 9 ≤ 10) hr
  have hq : 0 < r - 9 := Nat.sub_pos_iff_lt.mpr (lt_of_lt_of_le (by decide : 9 < 10) hr)
  have hqcast : ((r - 9 : ℕ) : ℝ) = (r : ℝ) - 9 := by
    rw [Nat.cast_sub hr9]
    norm_num
  have hcoef : 2 * a + a ^ 2 / 9 = ((r - 9 : ℕ) : ℝ) := by
    rw [hqcast]
    exact rhoStar_identity (r : ℝ) (Nat.cast_nonneg r)
  have hgap : rho < lam * a - 9 * (1 - lam) := by
    have hp : 0 ≤ Δ * rho / 9 := div_nonneg (mul_nonneg (le_of_lt hΔ) (le_of_lt hrho)) (by norm_num)
    linarith
  have hsum : (∑ i : Fin 9, x i) = 9 / 2 - Δ := by
    have hs := hxsum
    rw [Finset.sum_sub_distrib] at hs
    norm_num at hs
    linarith
  refine ⟨n, D, M, r - 9, rho, a, h, lam, Δ,
    ((∑ i : Fin 9, x i) + a) / 3, x,
    hn, rfl, rfl, rfl, hD, hM, hq, hu0, hratio, hratioeq, rfl, rfl, hhrho,
    hrho, hrhoa, ha, hh, hcoef, hlam0, hlam1, hgap, ?_,
    hΔ, hhalf, hslack, hnonint1, hnonint2, hxinj, hxbounds, hxsum, hsum, rfl, ?_⟩
  · rw [hqcast]
    exact hscale
  · ring

end Nagata.Workers.W05

end

section

namespace Nagata.Workers.W05

/-- Every fixed real period in (0,1) admits a positive exponential chart radius. -/
theorem exists_fixed_period_radius {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ R : ℝ, 0 < R ∧ R < Real.pi / 2 ∧ 2 * R < |Real.log τ| := by
  have hL : 0 < |Real.log τ| := abs_pos.mpr (ne_of_lt (Real.log_neg hτ hτ1))
  refine ⟨min (Real.pi / 4) (|Real.log τ| / 4), ?_, ?_, ?_⟩
  · exact lt_min (div_pos Real.pi_pos (by norm_num)) (div_pos hL (by norm_num))
  · have hm := min_le_left (Real.pi / 4) (|Real.log τ| / 4)
    linarith [Real.pi_pos]
  · have hm := min_le_right (Real.pi / 4) (|Real.log τ| / 4)
    linarith

@[simp] theorem chartPoint_identity (τ : ℝ) : chartPoint τ 0 0 = 1 := by
  apply Units.ext
  simp [chartPoint]

/-- The period action is free on all actual nonzero complex points. -/
theorem positivePeriod_action_free {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (k : ℤ) (z : ℂˣ) (hk : positivePeriod τ hτ ^ k * z = z) : k = 0 := by
  obtain ⟨R, hR, hRpi, hlog⟩ := exists_fixed_period_radius hτ hτ1
  have hper : positivePeriod τ hτ ^ k = 1 := by
    apply mul_right_cancel (b := z)
    simpa using hk
  have hbase : positivePeriod τ hτ ^ k * chartPoint τ 0 0 = chartPoint τ 0 0 := by
    simp [hper]
  exact (chartPoint_deck_unique hτ hR hRpi hlog 0 (by simpa using hR)
    (by simpa using hR) k hbase).1

theorem exists_injective_identity_slice {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    ∃ U : Set ℂˣ, IsOpen U ∧ (1 : ℂˣ) ∈ U ∧
      Set.InjOn (Nagata.W21.torusPointMk (positivePeriod τ hτ)) U := by
  obtain ⟨R, hR, hRpi, hlog⟩ := exists_fixed_period_radius hτ hτ1
  refine ⟨chartPoint τ 0 '' {x : ℂ | ‖x‖ < R},
    isOpen_chartPoint_image hRpi τ 0 (isOpen_chartDisk R) (fun _ h => h), ?_, ?_⟩
  · exact ⟨0, by simpa using hR, chartPoint_identity τ⟩
  · intro z hz w hw heq
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hw
    exact congrArg (chartPoint τ 0) (torusChart_injective_on_disk hτ hR hRpi hlog 0 hx hy heq)

end Nagata.Workers.W05

end

end OAI
