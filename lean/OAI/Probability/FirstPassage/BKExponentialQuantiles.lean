import OAI.Probability.FirstPassage.BKQuantization
import OAI.Probability.FirstPassage.FiniteEdgeEvents
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma ExponentialEnvironment.edge_tail_real (h : ExponentialEnvironment P τ)
    (e : Edge) (r : ℝ) (hr : 0 ≤ r) : P.real {ω | r < τ e ω} = Real.exp (-r) := by
  let _ := h.probability
  have hm : P {ω | τ e ω ≤ r} = expMeasure 1 (Iic r) := by
    rw [← h.marginal e,Measure.map_apply (h.measurable e) measurableSet_Iic]
    rfl
  have hc : P.real {ω | τ e ω ≤ r} = 1-Real.exp (-r) := by
    change (P {ω | τ e ω ≤ r}).toReal = _
    rw [hm,← measureReal_def,← cdf_eq_real,cdf_expMeasure_eq (by norm_num)]
    simp [hr]
  have he : {ω | r < τ e ω} = {ω | τ e ω ≤ r}ᶜ := by ext ω; simp
  rw [he,measureReal_compl (measurableSet_le (h.measurable e) measurable_const),hc]
  simp

theorem ExponentialEnvironment.survival_lt_real (h : ExponentialEnvironment P τ)
    (e : Edge) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    P.real {ω | Real.exp (-τ e ω) < u} = u := by
  by_cases hz : u=0
  · subst u
    have he : {ω | Real.exp (-τ e ω) < 0} = ∅ := by
      ext ω; simp [not_lt.mpr (Real.exp_pos (-τ e ω)).le]
    rw [he]; simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have he : {ω | Real.exp (-τ e ω) < u} = {ω | -Real.log u < τ e ω} := by
      ext ω
      rw [mem_ofPred_eq,mem_ofPred_eq,← Real.exp_log hup,Real.exp_lt_exp]
      simp only [Real.log_exp]
      constructor <;> intro hh <;> linarith
    rw [he,h.edge_tail_real e (-Real.log u) (neg_nonneg.mpr (Real.log_nonpos hu hu1))]
    simp [Real.exp_log hup]

theorem ExponentialEnvironment.survival_bin_real (h : ExponentialEnvironment P τ)
    (e : Edge) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    P.real {ω | a ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < b} = b-a := by
  let _ := h.probability
  let A : Set Ω := {ω | Real.exp (-τ e ω) < a}
  let B : Set Ω := {ω | Real.exp (-τ e ω) < b}
  have hA : MeasurableSet A := measurableSet_lt (Real.measurable_exp.comp (h.measurable e).neg) measurable_const
  have hAB : A ⊆ B := fun ω hω => lt_of_lt_of_le hω hab
  have he : {ω | a ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < b} = B \ A := by
    ext ω
    simp only [mem_ofPred_eq,mem_sdiff,A,B,not_lt]
    tauto
  rw [he,measureReal_sdiff hAB hA]
  exact congrArg₂ (·-·) (h.survival_lt_real e b (ha.trans hab) hb)
    (h.survival_lt_real e a ha (hab.trans hb))

theorem ExponentialEnvironment.survival_rank_real (h : ExponentialEnvironment P τ)
    (e : Edge) (m i : ℕ) (hm : 0 < m) (hi : i < m) :
    P.real {ω | ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i} = 1/(m:ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have he : {ω | ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i} =
      {ω | (i:ℝ)/m ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < ((i:ℝ)+1)/m} := by
    ext ω
    rw [mem_ofPred_eq,mem_ofPred_eq,Nat.floor_eq_iff (by positivity)]
    rw [div_le_iff₀ hm',lt_div_iff₀ hm']
    simp only [mul_comm]
  have hu : ((i:ℝ)+1)/m ≤ 1 := by
    rw [div_le_iff₀ hm']
    have hi' : (i:ℝ)+1 ≤ m := by exact_mod_cast (show i+1 ≤ m by omega)
    simpa using hi'
  rw [he,h.survival_bin_real e ((i:ℝ)/m) (((i:ℝ)+1)/m) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hm'.le) hu]
  ring

theorem ExponentialEnvironment.survival_ranks_joint_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (m : ℕ) (hm : 0 < m) (i : Edge → ℕ) (hi : ∀ e ∈ S, i e < m) :
    P.real {ω | ∀ e ∈ S, ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i e} = (1/(m:ℝ))^S.card := by
  let A : Edge → Set (Edge → ℝ) := fun e => {w | ⌊(m:ℝ)*Real.exp (-w e)⌋₊ = i e}
  have hA : ∀ e ∈ S, MeasurableSet (A e) := by
    intro e _
    apply measurableSet_eq_fun _ measurable_const
    fun_prop
  have hAS : ∀ e ∈ S, DependsOnEdges (A e) {e} := by
    intro e _ w w' hw
    have he := hw e (Finset.mem_singleton_self e)
    simp only [A,mem_ofPred_eq,he]
  have hd : Set.Pairwise (↑S : Set Edge) (fun e f => Disjoint ({e} : Finset Edge) {f}) := by
    intro e _ f _ hef
    simpa using hef
  have hj := disjoint_edge_events_inter_probability h S A (fun e => {e}) hA hAS hd
  have hr := congrArg ENNReal.toReal hj
  simp only [ENNReal.toReal_prod] at hr
  change P.real _ = ∏ e ∈ S, P.real _ at hr
  dsimp [A] at hr
  rw [hr]
  calc
    _ = ∏ _e ∈ S, (1/(m:ℝ)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact h.survival_rank_real e m (i e) hm (hi e he)
    _ = _ := by simp

end PlanarFPP

end OAI
