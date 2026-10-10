import OAI.Analysis.KadisonKastler.IndependentOrbitMoments
import OAI.Analysis.KadisonKastler.HilbertSignMoments
import OAI.Analysis.KadisonKastler.MatrixOrbitSampleLaw

namespace OAI

/-! # Expected costs before graph clipping

The cost uses the actual vector state and the two fourth powers. The
finite-sample estimate retains the diagonal correction, so increasing
the number of samples removes the diagonal cost. The final scalar lemma
chooses a stage and a sample size from convergence of the mixed moments.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

local instance graphMomentRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

/-- The nonnegative cost appearing before graph-vector clipping. -/
def graphMomentCost (Ω : H) (k : ℝ) (x : H →L[ℂ] H) : ℝ :=
  realVectorState Ω (star x * x) + k * realVectorState Ω (x * star x) +
    realVectorState Ω ((star x * x) ^ 2) + k * realVectorState Ω ((x * star x) ^ 2)

/-- The exact complex value of the positive vector-state square. -/
theorem operatorVectorState_star_mul_self (Ω : H) (x : H →L[ℂ] H) :
    operatorVectorState Ω (star x * x) = (‖x Ω‖ ^ 2 : ℝ) := by
  simp only [operatorVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Nonempty G]

omit [DecidableEq I] in
/-- Applying an operator sign sum to a vector is the Hilbert sign sum. -/
theorem normalizedFiniteSignSum_apply (a : I → H →L[ℂ] H) (ε : I → Bool) (Ω : H) :
    (normalizedFiniteSignSum a ε) Ω =
      normalizedHilbertSignSum (fun i => a i Ω) ε := by
  simp only [normalizedFiniteSignSum, normalizedHilbertSignSum, finiteSignSum,
    hilbertSignSum, smul_apply, sum_apply]

/-- The exact second moment holds for the vector state, without traciality. -/
theorem expect_normalizedSignSum_vector_second (Ω : H) (a : I → H →L[ℂ] H) :
    (𝔼 ε : I → Bool,
      realVectorState Ω (star (normalizedFiniteSignSum a ε) * normalizedFiniteSignSum a ε)) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, realVectorState Ω (star (a i) * a i) := by
  simp only [realVectorState_star_mul_self, normalizedFiniteSignSum_apply]
  exact expect_normalizedHilbertSignSum_sq (fun i => a i Ω)

omit [DecidableEq I] in
private theorem star_normalizedSignSum (a : I → H →L[ℂ] H) (ε : I → Bool) :
    star (normalizedFiniteSignSum a ε) = normalizedFiniteSignSum (fun i => star (a i)) ε := by
  simp only [normalizedFiniteSignSum, finiteSignSum, star_smul, star_trivial, star_sum]

/-- The second moment after independent sampling is the single-sample
second moment. -/
theorem expect_sampledNormalizedSignSum_vector_second
    [Nonempty I] (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω (star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
        normalizedFiniteSignSum (fun i => a (ω i)) ε)) =
      𝔼 g, realVectorState Ω (star (a g) * a g) := by
  simp_rw [expect_normalizedSignSum_vector_second]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hi (i : I) : (𝔼 ω : I → G, realVectorState Ω (star (a (ω i)) * a (ω i))) =
      𝔼 g, realVectorState Ω (star (a g) * a g) :=
    expect_sample_coordinate i (fun g => realVectorState Ω (star (a g) * a g))
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- The left square has the corresponding exact second moment. -/
theorem expect_sampledNormalizedSignSum_vector_left_second
    [Nonempty I] (Ω : H) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      realVectorState Ω (normalizedFiniteSignSum (fun i => a (ω i)) ε *
        star (normalizedFiniteSignSum (fun i => a (ω i)) ε))) =
      𝔼 g, realVectorState Ω (a g * star (a g)) := by
  simpa only [star_normalizedSignSum, star_star] using
    expect_sampledNormalizedSignSum_vector_second (I := I) Ω (fun g => star (a g))

/-- The four scalar statistics needed for the expected graph cost. -/
def orbitSecondMoment (Ω : H) (k : ℝ) (a : G → H →L[ℂ] H) : ℝ :=
  (𝔼 g, realVectorState Ω (star (a g) * a g)) +
    k * (𝔼 g, realVectorState Ω (a g * star (a g)))

def orbitDiagonalMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, realVectorState Ω ((star (a g) * a g) ^ 2)

def orbitFirstPairMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a g) * (star (a h) * a h))

def orbitThirdPairMoment (Ω : H) (a : G → H →L[ℂ] H) : ℝ :=
  𝔼 g, 𝔼 h, realVectorState Ω ((star (a g) * a h) * (star (a h) * a g))

/-- The actual cost of independently sampled normalized sign sums is
bounded by its single-sample, diagonal, and off-diagonal moments. -/
theorem expect_sampled_graphMomentCost_le [Nonempty I]
    (Ω : H) {k : ℝ} (hk : 0 ≤ k) (a : G → H →L[ℂ] H) :
    (𝔼 ω : I → G, 𝔼 ε : I → Bool,
      graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ≤
      orbitSecondMoment Ω k a +
      (orbitDiagonalMoment Ω a + k * orbitDiagonalMoment Ω (fun g => star (a g))) /
        Fintype.card I +
      (1 - (Fintype.card I : ℝ)⁻¹) *
        (orbitFirstPairMoment Ω a + 2 * orbitThirdPairMoment Ω a +
          k * (orbitFirstPairMoment Ω (fun g => star (a g)) +
            2 * orbitThirdPairMoment Ω (fun g => star (a g)))) := by
  have hr := expect_sampledNormalizedSignSum_vector_fourth_le (I := I) Ω a
  have hl := expect_sampledNormalizedSignSum_vector_fourth_le (I := I) Ω (fun g => star (a g))
  simp_rw [← star_normalizedSignSum, star_star] at hl
  have hcost :
      (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        graphMomentCost Ω k (normalizedFiniteSignSum (fun i => a (ω i)) ε)) =
      orbitSecondMoment Ω k a +
      (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        realVectorState Ω ((star (normalizedFiniteSignSum (fun i => a (ω i)) ε) *
          normalizedFiniteSignSum (fun i => a (ω i)) ε) ^ 2)) +
      k * (𝔼 ω : I → G, 𝔼 ε : I → Bool,
        realVectorState Ω ((normalizedFiniteSignSum (fun i => a (ω i)) ε *
          star (normalizedFiniteSignSum (fun i => a (ω i)) ε)) ^ 2)) := by
    simp only [graphMomentCost, Finset.expect_add_distrib, ← Finset.mul_expect,
      expect_sampledNormalizedSignSum_vector_second,
      expect_sampledNormalizedSignSum_vector_left_second, orbitSecondMoment]
  rw [hcost]
  have hkl := mul_le_mul_of_nonneg_left hl hk
  have hb := add_le_add_left (add_le_add hr hkl) (orbitSecondMoment Ω k a)
  convert hb using 1 <;>
    (try simp only [orbitDiagonalMoment, orbitFirstPairMoment, orbitThirdPairMoment, star_star]) <;> ring

/-- The scalar off-diagonal cost stays bounded uniformly in the graph
rescaling when `α + k β = 1` and `k ≥ 1`. -/
theorem graph_pairing_scalar_le_six {α β k : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hk : 1 ≤ k) (hn : α + k * β ≤ 1) :
    α ^ 2 + k * β ^ 2 + 2 * (k + 1) * α * β ≤ 6 := by
  have hk0 : 0 ≤ k := le_trans zero_le_one hk
  have hα1 : α ≤ 1 := by nlinarith [mul_nonneg hk0 hβ]
  have hkβ : k * β ≤ 1 := by linarith
  have hβ1 : β ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hβ]
  have ha2 : α ^ 2 ≤ 1 := by nlinarith
  have hb2 : k * β ^ 2 ≤ 1 := calc
    _ = (k * β) * β := by ring
    _ ≤ 1 * 1 := mul_le_mul hkβ hβ1 hβ (by norm_num)
    _ = 1 := by ring
  have hab : α * β ≤ 1 := by simpa using mul_le_mul hα1 hβ1 hβ (by norm_num : (0 : ℝ) ≤ 1)
  have hkab : k * α * β ≤ 1 := calc
    _ = α * (k * β) := by ring
    _ ≤ 1 * 1 := mul_le_mul hα1 hkβ (mul_nonneg hk0 hβ) (by norm_num)
    _ = 1 := by ring
  nlinarith

/-- A convergent off-diagonal statistic and a fixed diagonal bound give
an actual finite stage and sample size with expected cost at most ten. -/
theorem exists_stage_sample_cost_le_ten
    (C : ℕ → ℕ → ℝ) (T : ℕ → ℝ) {D L : ℝ}
    (hL0 : 0 ≤ L) (hL : L ≤ 6) (hT : Tendsto T atTop (𝓝 L))
    (hC : ∀ j m, 1 ≤ m →
      C j m ≤ 1 + D / m + (1 - (m : ℝ)⁻¹) * T j) :
    ∃ j m, 1 ≤ m ∧ C j m ≤ 10 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max D 1)
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := lt_trans zero_lt_one hm1
  have hmNat : 1 ≤ m := by exact_mod_cast hm1.le
  have hD : D / m ≤ 1 := (div_le_one hmpos).mpr (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hm))
  have hnear : ∀ᶠ j in atTop, T j ∈ Set.Ioo (-7) 7 :=
    hT.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨j, hj⟩ := hnear.exists
  have habs : |T j| ≤ 7 := abs_le.mpr ⟨hj.1.le, hj.2.le⟩
  have hinv : (m : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hm1.le
  have hc0 : 0 ≤ 1 - (m : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have hc1 : 1 - (m : ℝ)⁻¹ ≤ 1 := sub_le_self _ (inv_nonneg.mpr hmpos.le)
  have hterm : (1 - (m : ℝ)⁻¹) * T j ≤ 7 := calc
    _ ≤ (1 - (m : ℝ)⁻¹) * |T j| := mul_le_mul_of_nonneg_left (le_abs_self _) hc0
    _ ≤ 1 * 7 := mul_le_mul hc1 habs (abs_nonneg _) (by norm_num)
    _ = 7 := by ring
  exact ⟨j, m, hmNat, by linarith [hC j m hmNat]⟩

end

end KadisonKastler

end OAI
