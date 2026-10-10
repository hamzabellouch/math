import OAI.Probability.MatroidProphet.Simulation
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

lemma measurableSet_nonnegative (n : ℕ) :
    MeasurableSet {w : Weights n | ∀ e, 0 ≤ w e} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun e => measurableSet_le measurable_const (measurable_pi_apply e)

lemma integrable_hidden_product {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (ρ : Measure (Weights n)) [SFinite ρ]
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ) :
    Integrable (fun x : Seed bits × Weights n => hiddenWorstReward A x.2 x.1)
      (ν.prod ρ) := by
  apply (hopt.comp_snd ν).mono' (measurable_hiddenWorstReward A).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).ae hNN] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hiddenWorstReward_nonneg A x.2 hx x.1)]
  exact hiddenWorstReward_le_optimum M A hA x.2 hx x.1

lemma hidden_product_integral_bound {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (ρ : Measure (Weights n)) [IsProbabilityMeasure ρ] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hNN : ∀ᵐ w ∂ρ, ∀ e, 0 ≤ w e) (hopt : Integrable (optimum M) ρ)
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν) :
    c * (∫ w, optimum M w ∂ρ) ≤
      ∫ x : Seed bits × Weights n, hiddenWorstReward A x.2 x.1 ∂ν.prod ρ := by
  have hip := integrable_hidden_product M A ν ρ hA hNN hopt
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ w, ∫ r, hiddenWorstReward A w r ∂ν ∂ρ := by
      apply integral_mono_ae (hopt.const_mul c) hip.integral_prod_right
      filter_upwards [hNN] with w hw
      exact hbound w hw
    _ = _ := (integral_prod_symm _ hip).symm

lemma integrable_feasible_reward {n bits : ℕ} (M : Matroid (Fin n))
    (A : OnlineRule n bits) (hA : Feasible M A)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (R : Ω → Seed bits) (π : Ω → ArrivalOrder n)
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

theorem oneSample_of_hidden {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν] (c : ℝ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hbound : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
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
  have hj := glue_seed_joint_law μ ν S V R hS hV hR hi hlaw hseed hRlaw A.mask
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

end MatroidProphet

end OAI
