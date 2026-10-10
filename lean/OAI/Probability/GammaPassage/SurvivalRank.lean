import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.FirstMoment
import OAI.Probability.GammaPassage.SurvivalQuantile
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Independence.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {shape rate : ℝ}

lemma gammaSurvival_nonneg (x : ℝ) : 0 ≤ gammaSurvival shape rate x := by
  exact sub_nonneg.mpr (cdf_le_one (gammaMeasure shape rate) x)

lemma gammaSurvival_measurable (hs : 0 < shape) (hr : 0 < rate) :
    Measurable (gammaSurvival shape rate) :=
  measurable_const.sub (gamma_cdf_continuous hs hr).measurable

lemma gammaSurvival_lt_one (hs : 0 < shape) (hr : 0 < rate)
    {x : ℝ} (hx : 0 < x) : gammaSurvival shape rate x < 1 := by
  have hc := gamma_cdf_strictMonoOn hs hr (show (0 : ℝ) ∈ Ici (0 : ℝ) from (le_refl (0 : ℝ))) hx.le hx
  rw [gamma_cdf_zero hs hr] at hc
  dsimp [gammaSurvival]
  linarith

lemma gammaSurvival_lt_iff (hs : 0 < shape) (hr : 0 < rate)
    {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) (hu1 : u ≤ 1) :
    gammaSurvival shape rate x < u ↔ gammaSurvivalQuantile hs hr u < x := by
  have hq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-u by linarith)
    (show 1-u < 1 by linarith)
  change gammaSurvival shape rate x < u ↔
    gammaQuantileReal shape rate hs hr (1-u) < x
  constructor
  · intro h
    apply lt_of_not_ge
    intro hn
    have hc := monotone_cdf (gammaMeasure shape rate) hn
    rw [hq.2] at hc
    dsimp [gammaSurvival] at h
    linarith
  · intro h
    have hc := gamma_cdf_strictMonoOn hs hr hq.1 hx h
    rw [hq.2] at hc
    dsimp [gammaSurvival]
    linarith

/-- The exceptional zero-weight endpoint is deliberately outside ranks 0,...,m-1. -/
lemma gammaSurvival_rank_zero (hs : 0 < shape) (hr : 0 < rate) (m : ℕ) :
    ⌊(m : ℝ) * gammaSurvival shape rate 0⌋₊ = m := by
  simp [gammaSurvival, gamma_cdf_zero hs hr]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : PlanarFPP.Edge → Ω → ℝ}

namespace GammaEnvironment

/-- Native Gamma strict positivity transfers through the actual edge marginal. -/
lemma edge_ae_pos (h : GammaEnvironment shape rate P τ) (e : PlanarFPP.Edge) :
    ∀ᵐ ω ∂P, 0 < τ e ω := by
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

lemma edge_tail_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) (r : ℝ) :
    P.real {ω | r < τ e ω} = gammaSurvival shape rate r := by
  let := h.probability
  let := isProbabilityMeasure_gammaMeasure hs hr
  have hm : P {ω | τ e ω ≤ r} = gammaMeasure shape rate (Iic r) := by
    rw [← h.marginal e, Measure.map_apply (h.measurable e) measurableSet_Iic]
    rfl
  have hc : P.real {ω | τ e ω ≤ r} = cdf (gammaMeasure shape rate) r := by
    rw [measureReal_def, hm, cdf_eq_real, measureReal_def]
  have he : {ω | r < τ e ω} = {ω | τ e ω ≤ r}ᶜ := by
    ext ω
    simp
  rw [he, measureReal_compl (measurableSet_le (h.measurable e) measurable_const), hc]
  simp [gammaSurvival]

/-- Strict uniform CDF on the closed parameter interval, proved from actual tails. -/
theorem survival_lt_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    P.real {ω | gammaSurvival shape rate (τ e ω) < u} = u := by
  by_cases hz : u = 0
  · subst u
    have he : {ω | gammaSurvival shape rate (τ e ω) < 0} = ∅ := by
      ext ω
      simp [not_lt.mpr (gammaSurvival_nonneg (shape := shape) (rate := rate) (τ e ω))]
    rw [he]
    simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have he : {ω | gammaSurvival shape rate (τ e ω) < u} =ᵐ[P]
        {ω | gammaSurvivalQuantile hs hr u < τ e ω} := by
      filter_upwards [h.edge_ae_pos e] with ω hω
      exact propext (gammaSurvival_lt_iff hs hr hω.le hup hu1)
    rw [measureReal_congr he, h.edge_tail_real hs hr]
    have hq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-u by linarith)
      (show 1-u < 1 by linarith)
    dsimp [gammaSurvival, gammaSurvivalQuantile]
    rw [hq.2]
    ring

theorem survival_bin_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    P.real {ω | a ≤ gammaSurvival shape rate (τ e ω) ∧
      gammaSurvival shape rate (τ e ω) < b} = b-a := by
  let := h.probability
  let A : Set Ω := {ω | gammaSurvival shape rate (τ e ω) < a}
  let B : Set Ω := {ω | gammaSurvival shape rate (τ e ω) < b}
  have hA : MeasurableSet A := measurableSet_lt
    ((gammaSurvival_measurable hs hr).comp (h.measurable e)) measurable_const
  have hAB : A ⊆ B := fun ω hω => lt_of_lt_of_le hω hab
  have he : {ω | a ≤ gammaSurvival shape rate (τ e ω) ∧
      gammaSurvival shape rate (τ e ω) < b} = B \ A := by
    ext ω
    simp only [mem_ofPred_eq, mem_sdiff, A, B, not_lt]
    tauto
  rw [he, measureReal_sdiff hAB hA]
  exact congrArg₂ (·-·) (h.survival_lt_real hs hr e b (ha.trans hab) hb)
    (h.survival_lt_real hs hr e a ha (hab.trans hb))

/-- Exact floor-rank law; validity does not require pointwise positive weights. -/
theorem survival_rank_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge)
    (m i : ℕ) (hm : 0 < m) (hi : i < m) :
    P.real {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i} = 1/(m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i} =
      {ω | (i : ℝ)/m ≤ gammaSurvival shape rate (τ e ω) ∧
        gammaSurvival shape rate (τ e ω) < ((i : ℝ)+1)/m} := by
    ext ω
    have hp := gammaSurvival_nonneg (shape := shape) (rate := rate) (τ e ω)
    rw [mem_ofPred_eq, mem_ofPred_eq, Nat.floor_eq_iff (by positivity)]
    rw [div_le_iff₀ hm', lt_div_iff₀ hm']
    simp only [mul_comm]
  have hu : ((i : ℝ)+1)/m ≤ 1 := by
    rw [div_le_iff₀ hm']
    have hi' : (i : ℝ)+1 ≤ m := by exact_mod_cast (show i+1 ≤ m by omega)
    simpa using hi'
  rw [he, h.survival_bin_real hs hr e ((i : ℝ)/m) (((i : ℝ)+1)/m)
    (by positivity) (div_le_div_of_nonneg_right (by linarith) hm'.le) hu]
  ring

/-- Every original physical edge has an admissible rank simultaneously a.s.
This uses strict positivity, not merely nonnegative support: zero has rank m. -/
theorem survival_ranks_ae_lt (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (m : ℕ) (hm : 0 < m) :
    ∀ᵐ ω ∂P, ∀ e, ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ < m := by
  rw [ae_all_iff]
  intro e
  filter_upwards [h.edge_ae_pos e] with ω hω
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp := gammaSurvival_nonneg (shape := shape) (rate := rate) (τ e ω)
  apply (Nat.floor_lt (show 0 ≤ (m : ℝ) * gammaSurvival shape rate (τ e ω) by positivity)).mpr
  simpa only [mul_one] using mul_lt_mul_of_pos_left (gammaSurvival_lt_one hs hr hω) hm'

/-- Finite joint law from actual `iIndepFun`, including the empty edge set. -/
theorem survival_ranks_joint_real (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset PlanarFPP.Edge)
    (m : ℕ) (hm : 0 < m) (i : PlanarFPP.Edge → ℕ) (hi : ∀ e ∈ S, i e < m) :
    P.real {ω | ∀ e ∈ S, ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e} =
      (1/(m : ℝ))^S.card := by
  let A : PlanarFPP.Edge → Set ℝ := fun e =>
    {x | ⌊(m : ℝ) * gammaSurvival shape rate x⌋₊ = i e}
  have hA : ∀ e ∈ S, MeasurableSet (A e) := by
    intro e _
    apply measurableSet_eq_fun _ measurable_const
    exact (measurable_const.mul (gammaSurvival_measurable hs hr)).nat_floor
  have hj := h.independent.measure_inter_preimage_eq_mul S (sets := A) hA
  have he : {ω | ∀ e ∈ S, ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e} =
      ⋂ e ∈ S, τ e ⁻¹' A e := by
    ext ω
    simp [A]
  rw [he, measureReal_def, hj, ENNReal.toReal_prod]
  change (∏ e ∈ S, P.real {ω | ⌊(m : ℝ) * gammaSurvival shape rate (τ e ω)⌋₊ = i e}) = _
  calc
    _ = ∏ _e ∈ S, (1/(m : ℝ)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact h.survival_rank_real hs hr e m (i e) hm (hi e he)
    _ = _ := by simp

end GammaEnvironment
end GammaFPP

end OAI
