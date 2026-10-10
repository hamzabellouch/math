import OAI.Probability.MatroidProphet.Information
import Mathlib.Probability.Independence.Basic

namespace OAI

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

noncomputable def glue {n : ℕ} (mask : Finset (Fin n)) (s v : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ mask then s e else v e

lemma measurable_glue {n : ℕ} (mask : Finset (Fin n)) :
    Measurable (fun x : Weights n × Weights n => glue mask x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ mask
  · simpa [glue, he, Function.comp_def] using (measurable_pi_apply e).comp measurable_fst
  · simpa [glue, he, Function.comp_def] using (measurable_pi_apply e).comp measurable_snd

lemma measurable_glue_seed {n bits : ℕ} (mask : Seed bits → Finset (Fin n)) :
    Measurable (fun x : Seed bits × (Weights n × Weights n) =>
      glue (mask x.1) x.2.1 x.2.2) := by
  apply measurable_from_prod_countable_right
  intro r
  exact measurable_glue (mask r)

theorem glue_fixed_law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S V : Ω → Weights n) (hS : Measurable S) (hV : Measurable V)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (mask : Finset (Fin n)) :
    μ.map (fun ω => glue mask (S ω) (V ω)) = μ.map V := by
  classical
  let select : Fin n → Fin n × Bool := fun e => (e, decide (e ∈ mask))
  have hs : Function.Injective select := by
    intro a b h
    exact congrArg Prod.fst h
  have hg : iIndepFun (fun e ω => glue mask (S ω) (V ω) e) μ := by
    convert hi.precomp hs using 1
    funext e ω
    by_cases he : e ∈ mask <;> simp [select, pairedCoordinates, glue, he]
  have hv : iIndepFun (fun e ω => V ω e) μ := by
    have hj : Function.Injective (fun e : Fin n => (e, false)) := by
      intro a b h
      exact congrArg Prod.fst h
    simpa [pairedCoordinates] using hi.precomp hj
  have hgm : ∀ e, AEMeasurable (fun ω => glue mask (S ω) (V ω) e) μ := by
    intro e
    exact ((measurable_pi_apply e).comp
      ((measurable_glue mask).comp (hS.prodMk hV))).aemeasurable
  have hvm : ∀ e, AEMeasurable (fun ω => V ω e) μ := by
    intro e
    exact ((measurable_pi_apply e).comp hV).aemeasurable
  calc
    μ.map (fun ω => glue mask (S ω) (V ω)) =
        Measure.pi (fun e => μ.map (fun ω => glue mask (S ω) (V ω) e)) :=
      hg.map_fun_eq_pi_map hgm
    _ = Measure.pi (fun e => μ.map (fun ω => V ω e)) := by
      congr 1
      funext e
      by_cases he : e ∈ mask
      · simpa [glue, he, Function.comp_def] using hlaw e
      · simp [glue, he]
    _ = μ.map V := (hv.map_fun_eq_pi_map hvm).symm

theorem glue_seed_joint_law {n bits : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν) (mask : Seed bits → Finset (Fin n)) :
    MeasurePreserving (fun ω => (R ω, glue (mask (R ω)) (S ω) (V ω)))
      μ (ν.prod (μ.map V)) := by
  have hfiber (r : Seed bits) :
      (μ.map (fun ω => (S ω, V ω))).map (fun d => glue (mask r) d.1 d.2) =
        μ.map V := by
    rw [Measure.map_map (measurable_glue (mask r)) (hS.prodMk hV)]
    exact glue_fixed_law μ S V hS hV hi hlaw (mask r)
  have hstart : MeasurePreserving (fun ω => (R ω, (S ω, V ω))) μ
      (ν.prod (μ.map (fun ω => (S ω, V ω)))) := by
    refine ⟨hR.prodMk (hS.prodMk hV), ?_⟩
    rw [hseed.symm.map_prod_eq_prod_map_map hR.aemeasurable
      (hS.prodMk hV).aemeasurable, hRlaw]
  have hend := (MeasurePreserving.id ν).skew_product
    (g := fun (r : Seed bits) (d : Weights n × Weights n) => glue (mask r) d.1 d.2)
    (measurable_glue_seed mask) (ae_of_all _ hfiber)
  exact hend.comp hstart

theorem glue_seed_law {n bits : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure (Seed bits)) [IsProbabilityMeasure ν]
    (S V : Ω → Weights n) (R : Ω → Seed bits)
    (hS : Measurable S) (hV : Measurable V) (hR : Measurable R)
    (hi : iIndepFun (pairedCoordinates S V) μ)
    (hlaw : ∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e))
    (hseed : IndepFun (fun ω => (S ω, V ω)) R μ)
    (hRlaw : μ.map R = ν) (mask : Seed bits → Finset (Fin n)) :
    μ.map (fun ω => glue (mask (R ω)) (S ω) (V ω)) = μ.map V := by
  have hj := glue_seed_joint_law μ ν S V R hS hV hR hi hlaw hseed hRlaw mask
  exact ((measurePreserving_snd (μ := ν) (ν := μ.map V)).comp hj).map_eq

lemma measurable_weight_eval {n : ℕ} :
    Measurable (fun x : Weights n × Fin n => x.1 x.2) :=
  measurable_from_prod_countable_left fun e => measurable_pi_apply e

noncomputable def simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s : Weights n) {k : Fin n} (h : History n k) : History n k := by
  classical
  exact fun j => ((h j).1, if (h j).1 ∈ A.mask r then s (h j).1 else (h j).2)

lemma measurable_simulationHistory {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (k : Fin n) :
    Measurable (fun x : Weights n × History n k => simulationHistory A r x.1 x.2) := by
  classical
  apply Measurable.of_eval
  intro j
  have hh : Measurable (fun x : Weights n × History n k => x.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hm : MeasurableSet {x : Weights n × History n k | (x.2 j).1 ∈ A.mask r} :=
    (measurable_fst.comp hh) (by trivial)
  exact (measurable_fst.comp hh).prodMk (Measurable.ite hm
    (measurable_weight_eval.comp (measurable_fst.prodMk (measurable_fst.comp hh)))
    (measurable_snd.comp hh))

lemma measurable_observed {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits) :
    Measurable (observed A r) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ A.mask r
  · simpa [observed, he] using (measurable_pi_apply e : Measurable (fun w : Weights n => w e))
  · simp [observed, he]

def currentLabel {n : ℕ} {k : Fin n} (h : History n k) : Fin n :=
  (h ⟨k.val, Nat.lt_succ_self _⟩).1

noncomputable def sampleSimulation {n bits : ℕ} (A : HiddenRule n bits) : OnlineRule n bits where
  decide k r s h := if currentLabel h ∈ A.mask r then false
    else A.core.decide k r (observed A r s) (simulationHistory A r s h)
  measurable_decide k := by
    classical
    apply measurable_from_prod_countable_right
    intro r
    have hc : Measurable (fun x : Weights n × History n k => currentLabel x.2) :=
      measurable_fst.comp ((measurable_pi_apply (⟨k.val, Nat.lt_succ_self _⟩ : Fin (k.val + 1))).comp measurable_snd)
    have hm : MeasurableSet {x : Weights n × History n k | currentLabel x.2 ∈ A.mask r} :=
      hc (by trivial)
    exact Measurable.ite hm measurable_const
      ((A.core.measurable_decide k).comp (measurable_const.prodMk
        (((measurable_observed A r).comp measurable_fst).prodMk
          (measurable_simulationHistory A r k))))

lemma observed_glue {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s v : Weights n) : observed A r (glue (A.mask r) s v) = observed A r s := by
  classical
  funext e
  by_cases he : e ∈ A.mask r <;> simp [observed, glue, he]

lemma simulationHistory_eq {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s v : Weights n) (π : ArrivalOrder n) (k : Fin n) :
    simulationHistory A r s (history v π k) = history (glue (A.mask r) s v) π k := by
  classical
  rfl

@[simp] lemma currentLabel_history {n : ℕ} (v : Weights n)
    (π : ArrivalOrder n) (k : Fin n) : currentLabel (history v π k) = π k := by
  rfl

theorem sampleSimulation_acceptedThrough {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r s v π t =
      hiddenAcceptedThrough A r (glue (A.mask r) s v) π t := by
  classical
  ext e
  by_cases he : e ∈ A.mask r <;>
    simp [acceptedThrough, hiddenAcceptedThrough, decisionAt, sampleSimulation,
      simulationHistory_eq, observed_glue, he]

theorem sampleSimulation_reward {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) :
    reward (sampleSimulation A) r s v π = hiddenReward A r (glue (A.mask r) s v) π := by
  classical
  unfold reward accepted hiddenReward
  rw [sampleSimulation_acceptedThrough]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e ∉ A.mask r := (Finset.mem_sdiff.mp he).2
  simp [glue, he']

theorem sampleSimulation_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) :
    Feasible M (sampleSimulation A) := by
  intro r s v π t hs hv
  rw [sampleSimulation_acceptedThrough]
  apply hA
  intro e
  classical
  by_cases he : e ∈ A.mask r
  · simpa [glue, he, Function.comp_def] using hs e
  · simpa [glue, he, Function.comp_def] using hv e

@[simp] lemma glue_self {n : ℕ} (mask : Finset (Fin n)) (w : Weights n) :
    glue mask w w = w := by
  classical
  funext e
  simp [glue]

lemma hiddenWorstReward_le {n bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (r : Seed bits) (π : ArrivalOrder n) :
    hiddenWorstReward A w r ≤ hiddenReward A r w π := by
  classical
  exact Finset.inf'_le (hiddenReward A r w) (Finset.mem_univ π)

lemma hiddenWorstReward_nonneg {n bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (hw : ∀ e, 0 ≤ w e) (r : Seed bits) : 0 ≤ hiddenWorstReward A w r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact Finset.sum_nonneg fun e _ => hw e

lemma hiddenWorstReward_le_optimum {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed bits) :
    hiddenWorstReward A w r ≤ optimum M w := by
  apply (hiddenWorstReward_le A w r (Equiv.refl _)).trans
  exact sum_le_optimum M w _ (hA w hw r (Equiv.refl _) n)

lemma measurable_hiddenReward {n bits : ℕ} (A : HiddenRule n bits) (π : ArrivalOrder n) :
    Measurable (fun x : Seed bits × Weights n => hiddenReward A x.1 x.2 π) := by
  have hm := (measurable_reward_fixed_order (sampleSimulation A) π).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))
  simpa only [Function.comp_def, sampleSimulation_reward, glue_self] using hm

lemma measurable_hiddenWorstReward {n bits : ℕ} (A : HiddenRule n bits) :
    Measurable (fun x : Seed bits × Weights n => hiddenWorstReward A x.2 x.1) := by
  classical
  have hm : Measurable ((Finset.univ : Finset (ArrivalOrder n)).inf'
      Finset.univ_nonempty (fun π (x : Seed bits × Weights n) => hiddenReward A x.1 x.2 π)) :=
    Finset.inf'_induction Finset.univ_nonempty _
      (fun _ hf _ hg => hf.inf hg) (fun π _ => measurable_hiddenReward A π)
  convert hm using 1
  ext x
  simp only [hiddenWorstReward, Finset.inf'_apply]

end MatroidProphet

end OAI
