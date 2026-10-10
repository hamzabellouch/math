import OAI.Probability.MatroidSecretary.Transport.GeneralSimulationModel
import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! One-sample simulation for an arbitrary measurable complete seed. -/

namespace MatroidProphet.General

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {R : Type*} [MeasurableSpace R]

lemma measurable_mask_membership :
    MeasurableSet {x : Finset (Fin n) × Fin n | x.2 ∈ x.1} :=
  (Set.toFinite _).measurableSet

lemma measurable_observed (A : HiddenRule n R) :
    Measurable (fun x : R × Weights n => observed A x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro e
  have hm : MeasurableSet {x : R × Weights n | e ∈ A.mask x.1} :=
    (measurableSet_mem_finset e).preimage (A.measurable_mask.comp measurable_fst)
  exact Measurable.ite hm ((measurable_pi_apply e).comp measurable_snd) measurable_const

lemma measurable_simulationHistory (A : HiddenRule n R) (k : Fin n) :
    Measurable (fun x : R × (Weights n × History n k) =>
      simulationHistory A x.1 x.2.1 x.2.2) := by
  classical
  apply Measurable.of_eval
  intro j
  have hh : Measurable (fun x : R × (Weights n × History n k) => x.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hm : MeasurableSet {x : R × (Weights n × History n k) |
      (x.2.2 j).1 ∈ A.mask x.1} :=
    measurable_mask_membership.preimage
      ((A.measurable_mask.comp measurable_fst).prodMk (measurable_fst.comp hh))
  exact (measurable_fst.comp hh).prodMk (Measurable.ite hm
    (MatroidProphet.measurable_weight_eval.comp
      ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp hh)))
    (measurable_snd.comp hh))

lemma measurable_simulationDecision (A : HiddenRule n R) (k : Fin n) :
    Measurable (fun x : R × (Weights n × History n k) =>
      simulationDecision A k x.1 x.2.1 x.2.2) := by
  classical
  have hc : Measurable (fun x : R × (Weights n × History n k) =>
      (x.2.2 ⟨k.val, Nat.lt_succ_self _⟩).1) :=
    measurable_fst.comp ((measurable_pi_apply
      (⟨k.val, Nat.lt_succ_self _⟩ : Fin (k.val + 1))).comp
        (measurable_snd.comp measurable_snd))
  have hm : MeasurableSet {x : R × (Weights n × History n k) |
      (x.2.2 ⟨k.val, Nat.lt_succ_self _⟩).1 ∈ A.mask x.1} :=
    measurable_mask_membership.preimage
      ((A.measurable_mask.comp measurable_fst).prodMk hc)
  exact Measurable.ite hm measurable_const
    ((A.core.measurable_decide k).comp (measurable_fst.prodMk
      (((measurable_observed A).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_simulationHistory A k))))

noncomputable def sampleSimulation (A : HiddenRule n R) : OnlineRule n R where
  decide := simulationDecision A
  measurable_decide := measurable_simulationDecision A

lemma observed_glue (A : HiddenRule n R) (r : R) (s v : Weights n) :
    observed A r (glue (A.mask r) s v) = observed A r s := by
  classical
  funext e
  by_cases he : e ∈ A.mask r <;> simp [observed, glue, he]

lemma simulationHistory_eq (A : HiddenRule n R) (r : R)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    simulationHistory A r s (history v π k) = history (glue (A.mask r) s v) π k := rfl

theorem sampleSimulation_acceptedThrough (A : HiddenRule n R) (r : R)
    (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r s v π t =
      hiddenAcceptedThrough A r (glue (A.mask r) s v) π t := by
  classical
  ext e
  by_cases he : e ∈ A.mask r <;>
    simp [acceptedThrough, hiddenAcceptedThrough, decisionAt, sampleSimulation,
      simulationDecision, history, prefixIndex, simulationHistory_eq, observed_glue, he]

theorem sampleSimulation_reward (A : HiddenRule n R) (r : R)
    (s v : Weights n) (π : ArrivalOrder n) :
    reward (sampleSimulation A) r s v π = hiddenReward A r (glue (A.mask r) s v) π := by
  classical
  unfold reward hiddenReward
  rw [sampleSimulation_acceptedThrough]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e ∉ A.mask r := (Finset.mem_sdiff.mp he).2
  simp [glue, he']

theorem sampleSimulation_feasible (M : Matroid (Fin n)) (A : HiddenRule n R)
    (hA : HiddenFeasible M A) : Feasible M (sampleSimulation A) := by
  intro r s v π t hs hv
  rw [sampleSimulation_acceptedThrough]
  apply hA
  intro e
  classical
  by_cases he : e ∈ A.mask r
  · simpa [glue, he] using hs e
  · simpa [glue, he] using hv e

lemma reward_nonneg (A : OnlineRule n R) (r : R) (s v : Weights n)
    (π : ArrivalOrder n) (hv : ∀ e, 0 ≤ v e) : 0 ≤ reward A r s v π :=
  Finset.sum_nonneg fun e _ => hv e

lemma reward_le_optimum (M : Matroid (Fin n)) (A : OnlineRule n R)
    (hA : Feasible M A) (r : R) (s v : Weights n) (π : ArrivalOrder n)
    (hs : ∀ e, 0 ≤ s e) (hv : ∀ e, 0 ≤ v e) :
    reward A r s v π ≤ optimum M v :=
  sum_le_optimum M v _ (hA r s v π n hs hv)

lemma hiddenWorstReward_le (A : HiddenRule n R) (w : Weights n)
    (r : R) (π : ArrivalOrder n) :
    hiddenWorstReward A w r ≤ hiddenReward A r w π := by
  classical
  exact Finset.inf'_le (hiddenReward A r w) (Finset.mem_univ π)

lemma hiddenWorstReward_nonneg (A : HiddenRule n R) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (r : R) : 0 ≤ hiddenWorstReward A w r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact Finset.sum_nonneg fun e _ => hw e

lemma hiddenWorstReward_le_optimum (M : Matroid (Fin n)) (A : HiddenRule n R)
    (hA : HiddenFeasible M A) (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : R) :
    hiddenWorstReward A w r ≤ optimum M w := by
  apply (hiddenWorstReward_le A w r (Equiv.refl _)).trans
  exact sum_le_optimum M w _ (hA w hw r (Equiv.refl _) n)

lemma measurable_decisionAt {n : ℕ} {R : Type*} [MeasurableSpace R] (A : OnlineRule n R)
    (π : ArrivalOrder n) (k : Fin n) :
    Measurable (fun x : R × (Weights n × Weights n) =>
      decisionAt A x.1 x.2.1 x.2.2 π k) :=
  (A.measurable_decide k).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_history π k).comp (measurable_snd.comp measurable_snd))))

lemma reward_eq_sum {n : ℕ} {R : Type*} [MeasurableSpace R] (A : OnlineRule n R) (r : R)
    (s v : Weights n) (π : ArrivalOrder n) :
    reward A r s v π =
      ∑ e : Fin n, if decisionAt A r s v π (π.symm e) = true then v e else 0 := by
  classical
  unfold reward acceptedThrough
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [(π.symm e).isLt, true_and]

lemma measurable_reward_fixed_order {n : ℕ} {R : Type*} [MeasurableSpace R] (A : OnlineRule n R)
    (π : ArrivalOrder n) :
    Measurable (fun x : R × (Weights n × Weights n) =>
      reward A x.1 x.2.1 x.2.2 π) := by
  classical
  simp_rw [reward_eq_sum]
  apply Finset.measurable_sum
  intro e _
  have hd := measurable_decisionAt A π (π.symm e)
  have ht : MeasurableSet {x : R × (Weights n × Weights n) |
      decisionAt A x.1 x.2.1 x.2.2 π (π.symm e) = true} :=
    hd (measurableSet_singleton true)
  exact Measurable.ite ht
    ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd)) measurable_const

/-- The realized reward remains measurable for arbitrary measurable adversarial permutations. -/
theorem measurable_reward {n : ℕ} {R : Type*} [MeasurableSpace R] (A : OnlineRule n R) :
    Measurable (fun x : ArrivalOrder n × (R × (Weights n × Weights n)) =>
      reward A x.2.1 x.2.2.1 x.2.2.2 x.1) :=
  measurable_from_prod_countable_right (measurable_reward_fixed_order A)

@[simp] lemma glue_self (mask : Finset (Fin n)) (w : Weights n) :
    glue mask w w = w := by
  classical
  funext e
  simp [glue]

lemma measurable_hiddenReward {n : ℕ} {R : Type*} [MeasurableSpace R] (A : HiddenRule n R) (π : ArrivalOrder n) :
    Measurable (fun x : R × Weights n => hiddenReward A x.1 x.2 π) := by
  have hm := (measurable_reward_fixed_order (sampleSimulation A) π).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
  simpa only [Function.comp_def, sampleSimulation_reward, glue_self] using hm

lemma measurable_hiddenWorstReward {n : ℕ} {R : Type*} [MeasurableSpace R] (A : HiddenRule n R) :
    Measurable (fun x : R × Weights n => hiddenWorstReward A x.2 x.1) := by
  classical
  have hm : Measurable ((Finset.univ : Finset (ArrivalOrder n)).inf'
      Finset.univ_nonempty (fun π (x : R × Weights n) => hiddenReward A x.1 x.2 π)) :=
    Finset.inf'_induction Finset.univ_nonempty _
      (fun _ hf _ hg => hf.inf hg) (fun π _ => measurable_hiddenReward A π)
  convert hm using 1
  ext x
  simp only [hiddenWorstReward, Finset.inf'_apply]

lemma measurable_glue (mask : Finset (Fin n)) :
    Measurable (fun x : Weights n × Weights n => glue mask x.1 x.2) :=
  MatroidProphet.measurable_glue mask

lemma measurable_glue_seed (mask : R → Finset (Fin n)) (hmask : Measurable mask) :
    Measurable (fun x : R × (Weights n × Weights n) => glue (mask x.1) x.2.1 x.2.2) := by
  have h : Measurable (fun x : Finset (Fin n) × (Weights n × Weights n) =>
      glue x.1 x.2.1 x.2.2) :=
    measurable_from_prod_countable_right measurable_glue
  exact h.comp ((hmask.comp measurable_fst).prodMk measurable_snd)

theorem glue_fixed_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (hS : Measurable S) (hV : Measurable V)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (mask : Finset (Fin n)) :
    μ.map (fun ω => glue mask (S ω) (V ω)) = μ.map V :=
  MatroidProphet.glue_fixed_law μ S V hS hV hi hlaw mask

/-- Joint gluing law with an arbitrary measurable complete seed; in particular,
the observation mask may depend on all of that seed. -/
theorem glue_seed_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (S V : Ω → Weights n) (seed : Ω → R)
    (hS : Measurable S) (hV : Measurable V) (hseedM : Measurable seed)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) seed μ)
    (hseedLaw : μ.map seed = ν) (mask : R → Finset (Fin n)) (hmask : Measurable mask) :
    MeasurePreserving (fun ω => (seed ω, glue (mask (seed ω)) (S ω) (V ω)))
      μ (ν.prod (μ.map V)) := by
  have hfiber (r : R) :
      (μ.map (fun ω => (S ω, V ω))).map (fun d => glue (mask r) d.1 d.2) = μ.map V := by
    rw [Measure.map_map (measurable_glue (mask r)) (hS.prodMk hV)]
    exact glue_fixed_law μ S V hS hV hi hlaw (mask r)
  have hstart : MeasurePreserving (fun ω => (seed ω, (S ω, V ω))) μ
      (ν.prod (μ.map (fun ω => (S ω, V ω)))) := by
    refine ⟨hseedM.prodMk (hS.prodMk hV), ?_⟩
    rw [hseed.symm.map_prod_eq_prod_map_map hseedM.aemeasurable
      (hS.prodMk hV).aemeasurable, hseedLaw]
  have hend := (MeasurePreserving.id ν).skew_product
    (g := fun (r : R) (d : Weights n × Weights n) => glue (mask r) d.1 d.2)
    (measurable_glue_seed mask hmask) (ae_of_all _ hfiber)
  exact hend.comp hstart

/-- Nonnegativity of a finite vector is a Borel condition. -/
lemma measurableSet_nonnegative (n : ℕ) :
    MeasurableSet {w : Weights n | ∀ e, 0 ≤ w e} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun e => measurableSet_le measurable_const (measurable_pi_apply e)

lemma integrable_hidden_product {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (M : Matroid (Fin n)) (A : HiddenRule n Ξ)
    (ν : Measure (Ξ)) [IsProbabilityMeasure ν] (ρ : Measure (Weights n)) [SFinite ρ]
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Ξ) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ) :
    Integrable (fun x : Ξ × Weights n => hiddenWorstReward A x.2 x.1)
      (ν.prod ρ) := by
  apply (hopt.comp_snd ν).mono' (measurable_hiddenWorstReward A).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).ae hNN] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hiddenWorstReward_nonneg A x.2 hx x.1)]
  exact hiddenWorstReward_le_optimum M A hA x.2 hx x.1

lemma hidden_product_integral_bound {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (M : Matroid (Fin n))
    (A : HiddenRule n Ξ) (ν : Measure (Ξ)) [IsProbabilityMeasure ν]
    (ρ : Measure (Weights n)) [IsProbabilityMeasure ρ] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Ξ) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ)
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν) :
    c * (∫ w, optimum M w ∂ρ) ≤
      ∫ x : Ξ × Weights n, hiddenWorstReward A x.2 x.1 ∂ν.prod ρ := by
  have hip := integrable_hidden_product M A ν ρ hA hNN hopt
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ w, ∫ r, hiddenWorstReward A w r ∂ν ∂ρ := by
      apply integral_mono_ae (hopt.const_mul c) hip.integral_prod_right
      filter_upwards [hNN] with w hw
      exact hbound w hw
    _ = _ := (integral_prod_symm _ hip).symm

lemma integrable_feasible_reward {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (M : Matroid (Fin n))
    (A : OnlineRule n Ξ) (hA : Feasible M A)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (R : Ω → Ξ) (π : Ω → ArrivalOrder n)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R) (hπ : Measurable π)
    (hSN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ) :
    Integrable (fun ω => reward A (R ω) (S ω) (V ω) (π ω)) μ := by
  have hrm := (measurable_reward A).comp (hπ.prodMk (hR.prodMk (hS.prodMk hV)))
  apply hopt.mono' hrm.aestronglyMeasurable
  filter_upwards [hSN, hVN] with ω hs hv
  change ‖reward A (R ω) (S ω) (V ω) (π ω)‖ ≤ optimum M (V ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (reward_nonneg A (R ω) (S ω) (V ω) (π ω) hv)]
  exact reward_le_optimum M A hA (R ω) (S ω) (V ω) (π ω) hs hv

/-- The full one-sample integration step preserves the expected minimum over all orders. -/
theorem oneSample_of_hidden {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (M : Matroid (Fin n)) (A : HiddenRule n Ξ)
    (ν : Measure (Ξ)) [IsProbabilityMeasure ν] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Ξ) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S V : Ω → Weights n) (R : Ω → Ξ)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hSN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ)
    (π : Ω → ArrivalOrder n) (hπ : Measurable π) :
    Integrable (fun ω => reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω)) μ ∧
      c * (∫ ω, optimum M (V ω) ∂μ) ≤
        ∫ ω, reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω) ∂μ := by
  have hj := glue_seed_joint_law μ ν S V R hS hV hR hi hlaw hseed hRlaw A.mask A.measurable_mask
  have hoptLaw : Integrable (optimum M) (μ.map V) :=
    (integrable_map_measure (measurable_optimum M).aestronglyMeasurable hV.aemeasurable).2 hopt
  have hNNLaw : ∀ᵐ w ∂μ.map V, ∀ e, 0 ≤ w e :=
    (ae_map_iff hV.aemeasurable (measurableSet_nonnegative n)).2 hVN
  have hip := integrable_hidden_product M A ν (μ.map V) hA hNNLaw hoptLaw
  have him := hj.integrable_comp_of_integrable hip
  have hri := integrable_feasible_reward M (sampleSimulation A)
    (sampleSimulation_feasible M A hA) μ S V R π hS hV hR hπ hSN hVN hopt
  have hb := hidden_product_integral_bound M A ν (μ.map V) c hA hNNLaw hoptLaw hbound
  have hoptEq := integral_map_of_stronglyMeasurable (μ := μ) hV
    (measurable_optimum M).stronglyMeasurable
  have hminEq := integral_map_of_stronglyMeasurable (μ := μ) hj.measurable
    (measurable_hiddenWorstReward A).stronglyMeasurable
  rw [hj.map_eq] at hminEq
  rw [hoptEq, hminEq] at hb
  refine ⟨hri, hb.trans (integral_mono_ae him hri (ae_of_all _ ?_))⟩
  intro ω
  change hiddenWorstReward A (glue (A.mask (R ω)) (S ω) (V ω)) (R ω) ≤
    reward (sampleSimulation A) (R ω) (S ω) (V ω) (π ω)
  rw [sampleSimulation_reward]
  exact hiddenWorstReward_le A _ (R ω) (π ω)

/-- The manuscript's simulation lemma without any finite-seed restriction. -/
theorem simulation_contract.{u, v} : SimulationContract.{u, v} := by
  intro n R mR M A ν hν c hA hbound
  let := hν
  refine ⟨sampleSimulation A, ?_, sampleSimulation_feasible M A hA,
    sampleSimulation_acceptedThrough A, sampleSimulation_reward A, ?_⟩
  · intro k r s h
    rfl
  · intro Ω mΩ μ hμ S V seed hS hV hseedM hSN hVN hi hlaw hseed hseedLaw hopt π hπ
    exact ⟨glue_seed_joint_law μ ν S V seed hS hV hseedM hi hlaw hseed hseedLaw
      A.mask A.measurable_mask,
      oneSample_of_hidden M A ν c hA hbound μ S V seed hS hV hseedM hSN hVN
        hi hlaw hseed hseedLaw hopt π hπ⟩

/-- The concrete finite-seed information model is a special case, with exactly
the same decisions rather than an unrelated replacement rule. -/
def OnlineRule.ofFinite {bits : ℕ} (A : MatroidProphet.OnlineRule n bits) :
    OnlineRule n (Seed bits) where
  decide := A.decide
  measurable_decide := A.measurable_decide

def HiddenRule.ofFinite {bits : ℕ} (A : MatroidProphet.HiddenRule n bits) :
    HiddenRule n (Seed bits) where
  mask := A.mask
  measurable_mask := measurable_of_countable A.mask
  core := OnlineRule.ofFinite A.core

@[simp] lemma acceptedThrough_ofFinite {bits : ℕ}
    (A : MatroidProphet.OnlineRule n bits) (r : Seed bits) (s v : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (OnlineRule.ofFinite A) r s v π t =
      MatroidProphet.acceptedThrough A r s v π t := rfl

@[simp] lemma hiddenAcceptedThrough_ofFinite {bits : ℕ}
    (A : MatroidProphet.HiddenRule n bits) (r : Seed bits) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (HiddenRule.ofFinite A) r w π t =
      MatroidProphet.hiddenAcceptedThrough A r w π t := rfl

@[simp] lemma hiddenWorstReward_ofFinite {bits : ℕ}
    (A : MatroidProphet.HiddenRule n bits) (w : Weights n) (r : Seed bits) :
    hiddenWorstReward (HiddenRule.ofFinite A) w r = MatroidProphet.hiddenWorstReward A w r := rfl

end MatroidProphet.General

end OAI
