import OAI.Probability.FreeIsing.Estimates.KernelCompatibility

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSplit

variable {T E : Type*} [LinearOrder T] [AddCommGroup E]
    [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E]

def pastPath (t : T) (w : T → E) : Set.Iic t → E := fun s => w s

def futureIncrements (t : T) (w : T → E) : Set.Ioi t → E :=
  fun s => w s - w t

def pastePath (t : T) (p : Set.Iic t → E) (f : Set.Ioi t → E) (s : T) : E :=
  if h : s ≤ t then p ⟨s, h⟩ else p ⟨t, le_rfl⟩ + f ⟨s, lt_of_not_ge h⟩

omit [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E] in
theorem measurable_pastPath (t : T) : Measurable (pastPath (E := E) t) := by
  apply Measurable.of_eval
  intro s
  change Measurable (fun w : T → E => w (s : T))
  exact measurable_pi_apply (s : T)

omit [MeasurableAdd₂ E] in
theorem measurable_futureIncrements (t : T) :
    Measurable (futureIncrements (E := E) t) := by
  apply Measurable.of_eval
  intro s
  change Measurable (fun w : T → E => w (s : T) - w t)
  exact (measurable_pi_apply (s : T)).sub (measurable_pi_apply t)

omit [MeasurableSub₂ E] in
theorem measurable_pastePath (t : T) :
    Measurable (fun q : (Set.Iic t → E) × (Set.Ioi t → E) => pastePath t q.1 q.2) := by
  apply Measurable.of_eval
  intro s
  by_cases h : s ≤ t
  · simp only [pastePath, dite_eq_left h]
    exact (measurable_pi_apply (⟨s, h⟩ : Set.Iic t)).comp measurable_fst
  · simp only [pastePath, dite_eq_right h]
    exact ((measurable_pi_apply (⟨t, le_rfl⟩ : Set.Iic t)).comp measurable_fst).add
      ((measurable_pi_apply (⟨s, lt_of_not_ge h⟩ : Set.Ioi t)).comp measurable_snd)

def equiv (t : T) : (T → E) ≃ᵐ ((Set.Iic t → E) × (Set.Ioi t → E)) where
  toFun w := (pastPath t w, futureIncrements t w)
  invFun q := pastePath t q.1 q.2
  left_inv w := by
    funext s
    by_cases h : s ≤ t
    · simp [pastePath, pastPath, h]
    · simp [pastePath, pastPath, futureIncrements, h]
  right_inv q := by
    apply Prod.ext
    · funext s
      change pastePath t q.1 q.2 (s : T) = q.1 s
      rw [pastePath, dite_eq_left (show (s : T) ≤ t from s.property)]
    · funext s
      have hs : ¬ (s : T) ≤ t := not_le.mpr s.property
      simp [futureIncrements, pastePath, hs, add_sub_cancel_left]
  measurable_toFun := (measurable_pastPath t).prodMk (measurable_futureIncrements t)
  measurable_invFun := measurable_pastePath t

theorem measurableEmbedding_split (t : T) :
    MeasurableEmbedding (fun w : T → E => (pastPath t w, futureIncrements t w)) :=
  (equiv t).measurableEmbedding

theorem indepFun_future_conditionalCopies {O X : Type*}
    [MeasurableSpace O] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (t : T) (rho : Measure (T → E)) [IsProbabilityMeasure rho]
    (eta : Kernel (T → E) O) [IsMarkovKernel eta]
    (past : O → X) (hpast : Measurable past)
    (hind : IndepFun (fun q : (T → E) × O => (pastPath t q.1, past q.2))
      (fun q => futureIncrements t q.1) (rho ⊗ₘ eta)) :
    IndepFun (fun q : (T → E) × (O × O) => (pastPath t q.1, (past q.2.1, past q.2.2)))
      (fun q => futureIncrements t q.1) (rho ⊗ₘ (eta ×ₖ eta)) :=
  KernelCompatibility.indepFun_future_conditionalCopies_of_reconstructible_split
    rho (pastPath t) (measurable_pastPath t) (futureIncrements t)
    (measurable_futureIncrements t) (measurableEmbedding_split t) eta past hpast hind

end Problem367.PathSplit

end

end OAI
