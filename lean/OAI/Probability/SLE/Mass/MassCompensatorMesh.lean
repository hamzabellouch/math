import OAI.Probability.SLE.Mass.MassUniquenessMesh
import OAI.Probability.SLE.MomentGauge
import Mathlib.Topology.Order.Compact

namespace OAI

/-! The deterministic quadratic-error estimate for the prescribed dyadic
potential compensator. A finite terminal limit controls the growing horizon. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

/-- A continuous mass path with a finite terminal limit is uniformly
continuous even though the compensator mesh horizon grows to infinity. -/
lemma mass_path_uniformContinuous (A : ℝ≥0 → ℝ) (L : ℝ)
    (hc : Continuous A) (hl : Tendsto A atTop (𝓝 L)) : UniformContinuous A := by
  apply hc.uniformContinuous_of_tendsto_cocompact
  simpa only [cocompact_eq_atTop] using hl

def compensatorMeshTime (n i : ℕ) : ℝ≥0 :=
  (i : ℝ≥0) * (2 : ℝ≥0)^(-(n:ℤ))

@[simp] lemma compensatorMeshTime_zero (n : ℕ) : compensatorMeshTime n 0=0 := by
  simp [compensatorMeshTime]

lemma compensatorMeshTime_mono (n : ℕ) : Monotone (compensatorMeshTime n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma compensatorMeshTime_dist (n i : ℕ) :
    dist (compensatorMeshTime n (i+1)) (compensatorMeshTime n i) = (2:ℝ)^(-(n:ℤ)) := by
  rw [NNReal.dist_eq]
  simp only [compensatorMeshTime,NNReal.coe_mul,NNReal.coe_zpow,NNReal.coe_ofNat,
    NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,Nat.cast_add,Nat.cast_one]
  rw [show ((i:ℝ)+1)*(2:ℝ)^(-(n:ℤ))-(i:ℝ)*(2:ℝ)^(-(n:ℤ)) =
    (2:ℝ)^(-(n:ℤ)) by ring, abs_of_pos (by positivity)]

lemma compensatorMeshTime_small_increments (A : ℝ≥0 → ℝ) (L : ℝ)
    (hc : Continuous A) (hl : Tendsto A atTop (𝓝 L)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ i : ℕ,
      |A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i)| ≤ ε := by
  intro ε hε
  obtain ⟨δ,hδ,hAδ⟩ := Metric.uniformContinuous_iff.mp
    (mass_path_uniformContinuous A L hc hl) ε hε
  have hmesh : Tendsto (fun n : ℕ => (2:ℝ)^(-(n:ℤ))) atTop (𝓝 0) := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (2:ℝ)⁻¹ by positivity)
        (show (2:ℝ)⁻¹ < 1 by norm_num))
  filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with n hn i
  have h := hAδ (a := compensatorMeshTime n (i+1)) (b := compensatorMeshTime n i)
    (by simpa only [compensatorMeshTime_dist] using hn)
  exact (by simpa only [Real.dist_eq] using h.le)

def compensatorQuadraticError (A : ℝ≥0 → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n*2^n),
    (A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i))^2

lemma compensatorQuadraticError_nonneg (A : ℝ≥0 → ℝ) (n : ℕ) :
    0 ≤ compensatorQuadraticError A n :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma compensatorQuadraticError_le (A : ℝ≥0 → ℝ) (L : ℝ)
    (hm : Monotone A) (h0 : A 0=0) (hb : ∀ t, A t ≤ L)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ i : ℕ, A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i) ≤ ε) :
    compensatorQuadraticError A n ≤ ε*L := by
  have hsum : (∑ i ∈ Finset.range (n*2^n),
      (A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i))) ≤ L := by
    rw [Finset.sum_range_sub (fun i => A (compensatorMeshTime n i)) (n*2^n),
      compensatorMeshTime_zero,h0,sub_zero]
    exact hb _
  calc
    compensatorQuadraticError A n ≤ ∑ i ∈ Finset.range (n*2^n),
        ε*(A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i)) := by
      apply Finset.sum_le_sum
      intro i _
      have hnonneg := sub_nonneg.mpr (hm (compensatorMeshTime_mono n (Nat.le_succ i)))
      nlinarith [hsmall i]
    _ = ε*∑ i ∈ Finset.range (n*2^n),
        (A (compensatorMeshTime n (i+1))-A (compensatorMeshTime n i)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ε*L := mul_le_mul_of_nonneg_left hsum hε

lemma compensatorQuadraticError_le_terminal_sq (A : ℝ≥0 → ℝ) (L : ℝ)
    (hm : Monotone A) (h0 : A 0=0) (hb : ∀ t, A t ≤ L) (n : ℕ) :
    compensatorQuadraticError A n ≤ L^2 := by
  have hL : 0 ≤ L := by simpa only [h0] using hb 0
  simpa only [pow_two] using compensatorQuadraticError_le A L hm h0 hb n hL (fun i => by
    have hAi : 0 ≤ A (compensatorMeshTime n i) := by
      rw [← h0]
      exact hm (show 0 ≤ _ from zero_le)
    linarith [hb (compensatorMeshTime n (i+1))])

/-- The accumulated squared mass increments vanish for the exact growing
horizon and dyadic mesh used by the paper's potential formula. -/
theorem compensatorQuadraticError_tendsto_zero (A : ℝ≥0 → ℝ) (L : ℝ)
    (hm : Monotone A) (h0 : A 0=0) (hc : Continuous A)
    (hl : Tendsto A atTop (𝓝 L)) (hb : ∀ t, A t ≤ L) :
    Tendsto (compensatorQuadraticError A) atTop (𝓝 0) := by
  have hL : 0 ≤ L := by simpa only [h0] using hb 0
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (compensatorQuadraticError_nonneg A n))
  · intro b hb0
    have hd : 0 < b/(L+1) := div_pos hb0 (by linarith)
    filter_upwards [compensatorMeshTime_small_increments A L hc hl _ hd] with n hn
    have hbound := compensatorQuadraticError_le A L hm h0 hb n hd.le
      (fun i => (le_abs_self _).trans (hn i))
    have he : b/(L+1)*(L+1)=b := div_mul_cancel₀ b (by linarith)
    nlinarith

/-- Dominated convergence for the exact quadratic mesh error; the bound
requires only the second terminal moment, not a uniform time horizon. -/
theorem compensatorQuadraticError_mean_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ)
    (hA : ∀ t, Measurable (A t)) (hL : Integrable (fun ω => L ω^2) P)
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧
      Continuous (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop (𝓝 (L ω)) ∧
      ∀ t, A t ω ≤ L ω) :
    Tendsto (fun n => ∫ ω, compensatorQuadraticError (fun t => A t ω) n ∂P)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : Measurable (fun ω => compensatorQuadraticError (fun t => A t ω) n) := by
    apply Finset.measurable_sum
    intro i _
    exact ((hA _).sub (hA _)).pow_const 2
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖compensatorQuadraticError (fun t => A t ω) n‖ ≤ L ω^2 := by
    filter_upwards [hp] with ω hω
    rw [Real.norm_of_nonneg (compensatorQuadraticError_nonneg _ _)]
    exact compensatorQuadraticError_le_terminal_sq _ _ hω.1 hω.2.1 hω.2.2.2.2 n
  have hl : ∀ᵐ ω ∂P, Tendsto (fun n => compensatorQuadraticError (fun t => A t ω) n)
      atTop (𝓝 0) := by
    filter_upwards [hp] with ω hω
    exact compensatorQuadraticError_tendsto_zero _ _ hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun ω => L ω^2) (fun n => (hm n).aestronglyMeasurable) hL hb hl

end SLEExactGauge

end

end OAI
