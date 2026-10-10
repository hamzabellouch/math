import OAI.Probability.GaussianReplacement.StreamingModel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection

namespace StreamKernel
open NoiselessRegression unitInterval
namespace CompletedLearner
variable {d M T : ℕ} {K : CompletedLearner d M T}

def Sampling.initialStatus (R : K.Sampling) (u : I) : NoiselessRegression.Learner.RunStatus M :=
  startStatus (R.initial u)

def Sampling.stepStatus (R : K.Sampling) (s : UnitSphere d) (x : Samples d T) :
    ℕ → NoiselessRegression.Learner.RunStatus M → I → NoiselessRegression.Learner.RunStatus M
  | 0, a, _ => a
  | _+1, .inr done, _ => .inr done
  | n+1, .inl a, u => if hn : n < T then
      choiceStatus (n+1) (R.transition ((n+1,a),(x ⟨n,hn⟩,⟪x ⟨n,hn⟩,s.val⟫)) u)
    else .inl a

lemma Sampling.measurable_initialStatus (R : K.Sampling) : Measurable R.initialStatus :=
  (measurable_of_countable startStatus).comp R.measurable_initial

lemma Sampling.measurable_stepStatus (R : K.Sampling) (s : UnitSphere d) (x : Samples d T)
    (n : ℕ) : Measurable (Function.uncurry (R.stepStatus s x n)) := by
  cases n with
  | zero => exact measurable_fst
  | succ n =>
    apply measurable_from_prod_countable_right
    intro a
    cases a with
    | inr done => exact measurable_const
    | inl a =>
      by_cases hn : n < T
      · change Measurable (fun u : I => if h : n < T then
            choiceStatus (n+1) (R.transition ((n+1,a),(x ⟨n,h⟩,⟪x ⟨n,h⟩,s.val⟫)) u)
            else Sum.inl a)
        simp only [dite_eq_left hn]
        exact (measurable_of_countable (choiceStatus (M:=M) (n+1))).comp
          R.measurable_transition.of_uncurry_left
      · change Measurable (fun u : I => if h : n < T then
            choiceStatus (n+1) (R.transition ((n+1,a),(x ⟨n,h⟩,⟪x ⟨n,h⟩,s.val⟫)) u)
            else Sum.inl a)
        simpa only [dite_eq_right hn] using
          (measurable_const : Measurable (fun _ : I =>
            (Sum.inl a : NoiselessRegression.Learner.RunStatus M)))

lemma Sampling.stepStatus_law (R : K.Sampling) (s : UnitSphere d) (x : Samples d T)
    (n : ℕ) (a : NoiselessRegression.Learner.RunStatus M) :
    (volume : Measure I).map (R.stepStatus s x (n+1) a) = K.borel.nextLaw s x n a := by
  cases a with
  | inr done =>
    change (volume : Measure I).map (fun _ => Sum.inr done) = Measure.dirac (Sum.inr done)
    simp
  | inl a =>
    by_cases hn : n < T
    · change (volume : Measure I).map (fun u => if h : n < T then
          choiceStatus (n+1) (R.transition ((n+1,a),(x ⟨n,h⟩,⟪x ⟨n,h⟩,s.val⟫)) u)
          else Sum.inl a) = _
      simp only [nextLaw, dite_eq_left hn]
      rw [← R.transition_law ((n+1,a),(x ⟨n,hn⟩,⟪x ⟨n,hn⟩,s.val⟫)),
        Measure.map_map (measurable_of_countable _) R.measurable_transition.of_uncurry_left]
      rfl
    · change (volume : Measure I).map (fun u => if h : n < T then
          choiceStatus (n+1) (R.transition ((n+1,a),(x ⟨n,h⟩,⟪x ⟨n,h⟩,s.val⟫)) u)
          else Sum.inl a) = _
      simp [nextLaw, hn]

lemma Sampling.foldCoins_law (R : K.Sampling) (s : UnitSphere d) (x : Samples d T)
    (n : ℕ) :
    (coinLaw n).map (foldCoins R.initialStatus (R.stepStatus s x) n) = K.borel.runLaw s x n := by
  induction n with
  | zero =>
    have he := (measurePreserving_eval (fun _ : Fin 1 => (volume : Measure I)) 0).map_eq
    change (coinLaw 0).map (fun z => R.initialStatus (z 0)) = K.initial.map startStatus
    have hm : Measurable (fun z : Coins 0 => z 0) := measurable_pi_apply 0
    trans ((coinLaw 0).map (fun z => z 0)).map R.initialStatus
    · exact (Measure.map_map (μ:=coinLaw 0) R.measurable_initialStatus hm).symm
    change ((Measure.pi (fun _ : Fin 1 => (volume : Measure I))).map (fun z => z 0)).map _ = _
    rw [he, ← R.initial_law,
      Measure.map_map (measurable_of_countable _) R.measurable_initial]
    rfl
  | succ n ih =>
    rw [map_foldCoins_succ _ _ R.measurable_initialStatus (R.measurable_stepStatus s x), ih]
    change (K.borel.runLaw s x n).bind _ = (K.borel.runLaw s x n).bind _
    congr 1
    funext a
    exact R.stepStatus_law s x n a

lemma Sampling.run_eq_fold (R : K.Sampling) (s : UnitSphere d) (z : Coins (T+1))
    (x : Samples d T) (n : ℕ) (hn : n ≤ T) :
    R.program.run s z x n =
      foldCoins R.initialStatus (R.stepStatus s x) n
        (fun i => z ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ T := by omega
    rw [NoiselessRegression.Learner.run, ih hn']
    simp only [foldCoins, Sampling.stepStatus]
    have he : (Fin.init (fun i : Fin (n+2) => z ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩)) =
        (fun i : Fin (n+1) => z ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) := rfl
    rw [he]
    cases hstatus : foldCoins R.initialStatus (R.stepStatus s x) n
        (fun i : Fin (n+1) => z ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩) with
    | inr done => rfl
    | inl a =>
      simp only [dite_eq_left (show n < T by omega), Sampling.program, coinIndex,
        dite_eq_left (show n+1 < T+2 by omega), choiceStatus]
      rfl

lemma Sampling.estimate_law (R : K.Sampling) (s : UnitSphere d) (x : Samples d T) :
    (coinLaw (T+1)).map (fun z => R.program.estimate s z x) = K.borel.estimateLaw s x := by
  have hr : (fun z : Coins (T+1) => R.program.estimate s z x) =
      (fun z => R.output (terminalStatus (T:=T)
        (foldCoins R.initialStatus (R.stepStatus s x) T (Fin.init z))) (z (Fin.last (T+1)))) := by
    funext z
    have he := R.run_eq_fold s z x T le_rfl
    change R.output (terminalStatus (T:=T) (R.program.run s z x T))
      (z (Fin.last (T+1))) = _
    rw [he]
    rfl
  rw [hr]
  have hf := measurable_foldCoins _ _ R.measurable_initialStatus (R.measurable_stepStatus s x) T
  have ht : Measurable (terminalStatus (M:=M) (T:=T)) := measurable_of_countable _
  trans ((coinLaw T).map (fun w => terminalStatus (T:=T)
    (foldCoins R.initialStatus (R.stepStatus s x) T w))).bind
      (fun a => (volume : Measure I).map (R.output a))
  · exact map_freshCoin T (fun w => terminalStatus (T:=T)
      (foldCoins R.initialStatus (R.stepStatus s x) T w)) R.output (ht.comp hf) R.measurable_output
  · have he : (coinLaw T).map (fun w => terminalStatus (T:=T)
        (foldCoins R.initialStatus (R.stepStatus s x) T w)) =
        ((coinLaw T).map (foldCoins R.initialStatus (R.stepStatus s x) T)).map
          (terminalStatus (T:=T)) := (Measure.map_map ht hf).symm
    rw [he, R.foldCoins_law s x T]
    simp only [R.output_law]
    rfl

end CompletedLearner
end StreamKernel



namespace StreamKernel
open NoiselessRegression unitInterval
namespace CompletedLearner
variable {d M T : ℕ} {K : CompletedLearner d M T}

lemma Sampling.uniformSuccess_eq (R : K.Sampling) (ε : ℝ)
    [SFinite (NoiselessRegression.uniformSphere d)] [SFinite (sampleLaw d T)] :
    R.program.uniformSuccess (coinLaw (T+1)) ε = K.borel.uniformSuccess ε := by
  let S : Set (UnitSphere d × (Coins (T+1) × Samples d T)) :=
    {z | NoiselessRegression.Learner.angularError z.1 (R.program.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hE := measurable_program_estimate R.program R.measurable_initialChoice
    R.measurable_program_transition R.measurable_program_output
  have hS : MeasurableSet S := by
    exact measurableSet_le
      (Real.continuous_arccos.measurable.comp
        ((measurable_subtype_coe.comp hE).inner measurable_fst.subtype_val)) measurable_const
  let P : ((UnitSphere d × Samples d T) × Coins (T+1)) →
      UnitSphere d × (Coins (T+1) × Samples d T) := fun z => (z.1.1,(z.2,z.1.2))
  have hp : MeasurePreserving P
      (((NoiselessRegression.uniformSphere d).prod (sampleLaw d T)).prod (coinLaw (T+1)))
      ((NoiselessRegression.uniformSphere d).prod ((coinLaw (T+1)).prod (sampleLaw d T))) := by
    exact ((MeasurePreserving.id (NoiselessRegression.uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ:=sampleLaw d T) (ν:=coinLaw (T+1)))).comp
        (measurePreserving_prodAssoc _ _ _)
  have he := hp.measure_preimage hS.nullMeasurableSet
  change _ = _ at he
  change ((NoiselessRegression.uniformSphere d).prod ((coinLaw (T+1)).prod (sampleLaw d T))) S = _
  rw [← he, Measure.prod_apply (hp.measurable hS)]
  apply lintegral_congr
  intro z
  change (coinLaw (T+1)) {u | NoiselessRegression.Learner.angularError z.1
      (R.program.estimate z.1 u z.2) ≤ ε} = _
  have hc : MeasurableSet {v : UnitSphere d |
      NoiselessRegression.Learner.angularError z.1 v ≤ ε} :=
    measurableSet_le (Real.continuous_arccos.measurable.comp
      (measurable_subtype_coe.inner measurable_const)) measurable_const
  have hf : Measurable (fun u : Coins (T+1) => R.program.estimate z.1 u z.2) :=
    hE.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  calc
    _ = ((coinLaw (T+1)).map (fun u => R.program.estimate z.1 u z.2))
        {v | NoiselessRegression.Learner.angularError z.1 v ≤ ε} :=
      (Measure.map_apply hf hc).symm
    _ = _ := by rw [R.estimate_law]

end CompletedLearner
end StreamKernel




end CurrentProjection

end

end OAI
