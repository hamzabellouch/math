import OAI.Probability.MatroidSecretary.Labels.RelabelingProbability
import OAI.Probability.MatroidSecretary.Secretary.Final
import OAI.Probability.MatroidSecretary.Secretary.Execution
import OAI.Probability.MatroidSecretary.Secretary.SeedModel

namespace OAI

namespace MatroidProphet.Relabeling

open Finset MeasureTheory ProbabilityTheory

variable {α : Type*} {n : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- Bijective enumeration of complete arrival lists; the arrival index is unchanged. -/
def orderEquiv (e : α ≃ Fin n) : LabeledOrder α n ≃ ArrivalOrder n where
  toFun π := π.trans e
  invFun π := π.trans e.symm
  left_inv π := by ext k; simp
  right_inv π := by ext k; simp

/-- Exact decision on original labels, reading only the current available history. -/
def transportedSecretaryDecision (e : α ≃ Fin n) (A : SecretaryRule n Q)
    (k : Fin n) (q : Q) (h : LabeledHistory α k) : Bool :=
  if k.val < (A.prefixLength q).val then false
  else A.decide k q (encodeHistory e k h)

noncomputable def transportedSecretaryAcceptedThrough [Fintype α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) (t : ℕ) : Finset α := by
  classical
  exact univ.filter fun a => (π.symm a).val < t ∧
    transportedSecretaryDecision e A (π.symm a) q
      (labeledHistory w π (π.symm a)) = true

noncomputable def transportedSecretaryReward [Fintype α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) : ℝ :=
  ∑ a ∈ transportedSecretaryAcceptedThrough e A q w π n, w a

theorem measurable_transportedSecretaryDecision [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (k : Fin n) :
    Measurable (fun x : Q × LabeledHistory α k =>
      transportedSecretaryDecision e A k x.1 x.2) := by
  have hp : MeasurableSet {x : Q × LabeledHistory α k |
      k.val < (A.prefixLength x.1).val} :=
    (A.measurable_prefixLength.comp measurable_fst)
      (by trivial : MeasurableSet {K : Fin (n + 1) | k.val < K.val})
  exact Measurable.ite hp measurable_const
    ((A.measurable_decide k).comp
      (measurable_fst.prodMk ((measurable_encodeHistory e k).comp measurable_snd)))

@[simp] theorem transportedSecretaryDecision_eq (e : α ≃ Fin n)
    (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) (k : Fin n) :
    transportedSecretaryDecision e A k q (labeledHistory w π k) =
      secretaryDecisionAt A q (encodeWeights e w) (π.trans e) k := by
  simp only [transportedSecretaryDecision, secretaryDecisionAt,
    encodeHistory_labeledHistory]

/-- Every acceptance, at every prefix, is transported by the label bijection. -/
theorem transportedSecretaryAcceptedThrough_eq_map [Fintype α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) (t : ℕ) :
    transportedSecretaryAcceptedThrough e A q w π t =
      (secretaryAcceptedThrough A q (encodeWeights e w) (π.trans e) t).map
        e.symm.toEmbedding := by
  classical
  ext a
  rw [Finset.mem_map_equiv]
  simp only [transportedSecretaryAcceptedThrough, secretaryAcceptedThrough, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp only [transportedSecretaryDecision_eq, Equiv.symm_symm,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply]

/-- The accepted real-valued payoff is unchanged, without positivity assumptions. -/
theorem transportedSecretaryReward_eq [Fintype α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) :
    transportedSecretaryReward e A q w π =
      secretaryReward A q (encodeWeights e w) (π.trans e) := by
  simp [transportedSecretaryReward, transportedSecretaryAcceptedThrough_eq_map,
    secretaryReward, encodeWeights]

/-- Feasibility includes all seeds, all prefixes and the empty ground set. -/
theorem transportedSecretary_feasible [Fintype α]
    (M : Matroid α) (e : α ≃ Fin n) (A : SecretaryRule n Q)
    (hA : SecretaryFeasible (M.mapEquiv e) A)
    (q : Q) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (π : LabeledOrder α n) (t : ℕ) :
    M.Indep (transportedSecretaryAcceptedThrough e A q w π t : Set α) := by
  have hi := hA q (encodeWeights e w) ((encodeWeights_nonnegative_iff e w).2 hw)
    (π.trans e) t
  simpa only [transportedSecretaryAcceptedThrough_eq_map, coe_map,
    Equiv.coe_toEmbedding] using Matroid.mapEquiv_indep_iff.mp hi

/-- Equality of actual ordered prefixes is invariant under reindexing. -/
theorem samePrefix_encode_iff (e : α ≃ Fin n) (K : ℕ)
    (σ π : LabeledOrder α n) :
    SamePrefix K (σ.trans e) (π.trans e) ↔
      ∀ k : Fin n, k.val < K → σ k = π k := by
  simp [SamePrefix, e.injective.eq_iff]

/-- Observation-prefix labels are never accepted after reindexing. -/
theorem transportedSecretary_rejects_prefix [Fintype α]
    (e : α ≃ Fin n) (A : SecretaryRule n Q) (q : Q) (w : α → ℝ)
    (π : LabeledOrder α n) (t : ℕ) (a : α)
    (ha : (π.symm a).val < (A.prefixLength q).val) :
    a ∉ transportedSecretaryAcceptedThrough e A q w π t := by
  classical
  simp [transportedSecretaryAcceptedThrough, transportedSecretaryDecision, ha]

/-- Uniform finite laws are preserved by a genuine equivalence, including singleton laws. -/
theorem uniform_measure_map_equiv {β γ : Type*} [Fintype β] [Fintype γ]
    [Nonempty β] [Nonempty γ] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass β] [MeasurableSingletonClass γ] (e : β ≃ γ) :
    (PMF.uniformOfFintype β).toMeasure.map e = (PMF.uniformOfFintype γ).toMeasure := by
  classical
  rw [PMF.toMeasure_map e _ (measurable_of_finite e)]
  congr 1
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  have he (a : β) : b = e a ↔ e.symm b = a := by
    constructor
    · intro h; simpa using congrArg e.symm h
    · intro h; simpa using congrArg e h
  simp_rw [he]
  rw [tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    simp [Ne.symm ha]

/-- The original-label arrival law is literally uniform over all enumerations. -/
noncomputable def labeledUniformArrivalLaw [Fintype α] (e : α ≃ Fin n)
    [MeasurableSpace (LabeledOrder α n)] : Measure (LabeledOrder α n) := by
  classical
  letI : Nonempty (LabeledOrder α n) := ⟨e.symm⟩
  exact (PMF.uniformOfFintype (LabeledOrder α n)).toMeasure

theorem labeledUniformArrivalLaw_map [Fintype α]
    [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]
    (e : α ≃ Fin n) :
    (labeledUniformArrivalLaw e).map (fun π => π.trans e) =
      Secretary.uniformArrivalLaw n := by
  classical
  let : Nonempty (LabeledOrder α n) := ⟨e.symm⟩
  exact uniform_measure_map_equiv (orderEquiv e)

/-- Full expected guarantee on the original labels. The fixed rule and seed law
are chosen before the input vector and the probability space. Reindexing assumes
no independence for the executed order and retains every full-seed adversary. -/
theorem secretary_guarantee_labeled.{u} [Fintype α]
    [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]
    (M : Matroid α) (e : α ≃ Fin n) (A : SecretaryRule n Q)
    (ν : Measure Q) (c : ℝ) (h : SecretaryGuarantee.{u} (M.mapEquiv e) A ν c)
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Q) (σ π : Ω → LabeledOrder α n)
    (hR : Measurable R) (hσ : Measurable σ) (hπ : Measurable π)
    (hRlaw : μ.map R = ν) (hσlaw : μ.map σ = labeledUniformArrivalLaw e)
    (hind : IndepFun R σ μ)
    (hprefix : ∀ᵐ ω ∂μ, ∀ k : Fin n, k.val < (A.prefixLength (R ω)).val →
      σ ω k = π ω k) :
    Integrable (fun ω => transportedSecretaryReward e A (R ω) w (π ω)) μ ∧
      c * finiteOptimum M w ≤
        ∫ ω, transportedSecretaryReward e A (R ω) w (π ω) ∂μ := by
  have he : Measurable (fun p : LabeledOrder α n => p.trans e) := measurable_of_finite _
  have hlaw : μ.map (fun ω => (σ ω).trans e) = Secretary.uniformArrivalLaw n := by
    change μ.map ((fun p : LabeledOrder α n => p.trans e) ∘ σ) = _
    rw [← Measure.map_map he hσ, hσlaw, labeledUniformArrivalLaw_map]
  have hi : IndepFun R (fun ω => (σ ω).trans e) μ := by
    simpa only [Function.comp_def, id_eq] using hind.comp measurable_id he
  have hp : ∀ᵐ ω ∂μ, SamePrefix (A.prefixLength (R ω)).val
      ((σ ω).trans e) ((π ω).trans e) := by
    filter_upwards [hprefix] with ω hω
    exact (samePrefix_encode_iff e _ _ _).2 hω
  have hb := h (encodeWeights e w) ((encodeWeights_nonnegative_iff e w).2 hw)
    μ R (fun ω => (σ ω).trans e) (fun ω => (π ω).trans e)
    hR (he.comp hσ) (he.comp hπ) hRlaw hlaw hi hp
  have ho : optimum (M.mapEquiv e) (encodeWeights e w) = finiteOptimum M w :=
    finiteOptimum_mapEquiv M e w
  simpa only [ho, transportedSecretaryReward_eq] using hb

/-- An actual unconditional secretary witness for every finite label type.
The enumeration is fixed before weights or randomness; its choice imposes no
positive-size, positive-rank, or nonloop assumption. -/
theorem exists_labeled_secretary.{u} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace (LabeledOrder α n)] [MeasurableSingletonClass (LabeledOrder α n)]
    (M : Matroid α) (hE : M.E = Set.univ) (e : α ≃ Fin n) :
    ∃ (q : ℕ) (ν : Measure (Fin q)), IsProbabilityMeasure ν ∧
      ∃ (A : SecretaryRule n (Fin q)),
        (∀ k : Fin n, Measurable (fun x : Fin q × LabeledHistory α k =>
          transportedSecretaryDecision e A k x.1 x.2)) ∧
        (∀ (r : Fin q) (w : α → ℝ), (∀ a, 0 ≤ w a) →
          ∀ (π : LabeledOrder α n) (t : ℕ),
            M.Indep (transportedSecretaryAcceptedThrough e A r w π t : Set α)) ∧
        ∀ (w : α → ℝ), (∀ a, 0 ≤ w a) →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (R : Ω → Fin q) (σ π : Ω → LabeledOrder α n),
          Measurable R → Measurable σ → Measurable π →
          μ.map R = ν → μ.map σ = labeledUniformArrivalLaw e →
          IndepFun R σ μ →
          (∀ᵐ ω ∂μ, ∀ k : Fin n, k.val < (A.prefixLength (R ω)).val →
            σ ω k = π ω k) →
          Integrable (fun ω => transportedSecretaryReward e A (R ω) w (π ω)) μ ∧
            ((2 : ℝ) ^ 293)⁻¹ * finiteOptimum M w ≤
              ∫ ω, transportedSecretaryReward e A (R ω) w (π ω) ∂μ := by
  obtain ⟨q, ν, hν, A, hA, hbound⟩ :=
    MatroidProphet.secretary.{u} n (M.mapEquiv e) (mapEquiv_ground_univ M e hE)
  refine ⟨q, ν, hν, A, measurable_transportedSecretaryDecision e A, ?_, ?_⟩
  · exact transportedSecretary_feasible M e A hA
  · exact secretary_guarantee_labeled M e A ν (((2 : ℝ) ^ 293)⁻¹) hbound

end MatroidProphet.Relabeling

end OAI
