import OAI.Probability.GaussianReplacement.CompletedModel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection

namespace StreamKernel
open NoiselessRegression unitInterval
namespace CompletedLearner
variable {d M T : ℕ} (K : CompletedLearner d M T)

structure Sampling where
  initial : I → Bool × State M
  measurable_initial : Measurable initial
  initial_law : (volume : Measure I).map initial = K.initial
  transition : ((ℕ × State M) × (NoiselessRegression.Vector d × ℝ)) → I → Bool × State M
  measurable_transition : Measurable (Function.uncurry transition)
  transition_law : ∀ p, (volume : Measure I).map (transition p) = K.borel.transition p.1.1 p.1.2 p.2
  output : (ℕ × State M) → I → UnitSphere d
  measurable_output : Measurable (Function.uncurry output)
  output_law : ∀ p, (volume : Measure I).map (output p) = K.output p.1 p.2

lemma exists_sampling : Nonempty K.Sampling := by
  let : IsProbabilityMeasure K.initial := K.initial_probability
  let : IsProbabilityMeasure (K.output 0 0) := K.output_probability 0 0
  let : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 0)
  obtain ⟨i, hi, hei⟩ := K.initial.exists_measurable_map_eq
  obtain ⟨t, ht, het⟩ := K.transitionKernel.exists_measurable_map_eq_unitInterval
  obtain ⟨o, ho, heo⟩ := K.outputKernel.exists_measurable_map_eq_unitInterval
  exact ⟨⟨i,hi,hei,t,ht,het,o,ho,heo⟩⟩

def sampling : K.Sampling := Classical.choice K.exists_sampling



def coinIndex (T n : ℕ) : Fin (T+2) := if h : n < T+2 then ⟨n,h⟩ else 0

def Sampling.program (R : K.Sampling) : NoiselessRegression.Learner d M T (Coins (T+1)) where
  initialChoice := fun z => R.initial (z 0)
  transition := fun n z a o => R.transition ((n,a),o) (z (coinIndex T n))
  output := fun n z a => R.output (n,a) (z (Fin.last (T+1)))

lemma Sampling.measurable_initialChoice (R : K.Sampling) :
    Measurable R.program.initialChoice := R.measurable_initial.comp (measurable_pi_apply 0)

lemma Sampling.measurable_program_transition (R : K.Sampling) (n : ℕ) :
    Measurable (fun p : (Coins (T+1) × State M) × (NoiselessRegression.Vector d × ℝ) =>
      R.program.transition n p.1.1 p.1.2 p.2) := by
  exact R.measurable_transition.comp
    (((measurable_const (a:=n)).prodMk measurable_fst.snd |>.prodMk measurable_snd).prodMk
      ((measurable_pi_apply (coinIndex T n)).comp measurable_fst.fst))

lemma Sampling.measurable_program_output (R : K.Sampling) :
    Measurable (fun p : Coins (T+1) × (ℕ × State M) =>
      R.program.output p.2.1 p.1 p.2.2) := by
  exact R.measurable_output.comp
    (measurable_snd.prodMk ((measurable_pi_apply (Fin.last (T+1))).comp measurable_fst))

end CompletedLearner

section BorelProgram
variable {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (L : NoiselessRegression.Learner d M T Ω)
  (hi : Measurable L.initialChoice)
  (ht : ∀ n, Measurable (fun p : (Ω × State M) × (NoiselessRegression.Vector d × ℝ) =>
    L.transition n p.1.1 p.1.2 p.2))
  (ho : Measurable (fun p : Ω × (ℕ × State M) => L.output p.2.1 p.1 p.2.2))

include hi ht in
lemma measurable_program_run (n : ℕ) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) := by
  induction n with
  | zero =>
    exact (measurable_of_countable (CompletedLearner.startStatus (M:=M))).comp
      (hi.comp measurable_snd.fst)
  | succ n ih =>
    let F : NoiselessRegression.Learner.RunStatus M × (UnitSphere d × (Ω × Samples d T)) →
        NoiselessRegression.Learner.RunStatus M := fun p =>
      match p.1 with
      | .inr done => .inr done
      | .inl a => if hn : n < T then
          CompletedLearner.choiceStatus (n+1)
            (L.transition (n+1) p.2.2.1 a
              (p.2.2.2 ⟨n,hn⟩, ⟪p.2.2.2 ⟨n,hn⟩,p.2.1.val⟫))
        else .inl a
    have hF : Measurable F := by
      apply measurable_from_prod_countable_right
      intro a
      cases a with
      | inr done => exact measurable_const
      | inl a =>
        by_cases hn : n < T
        · simp only [F, dite_eq_left hn]
          apply (measurable_of_countable (CompletedLearner.choiceStatus (M:=M) (n+1))).comp
          have hr : Measurable (fun z : UnitSphere d × (Ω × Samples d T) => z.2.2 ⟨n,hn⟩) :=
            (measurable_pi_apply _).comp measurable_snd.snd
          exact (ht (n+1)).comp
            ((measurable_snd.fst.prodMk measurable_const).prodMk
              (hr.prodMk (hr.inner measurable_fst.subtype_val)))
        · simpa only [F, dite_eq_right hn] using
            (measurable_const : Measurable (fun _ : UnitSphere d × (Ω × Samples d T) =>
              (Sum.inl a : NoiselessRegression.Learner.RunStatus M)))
    exact hF.comp (ih.prodMk measurable_id)

include hi ht ho in
lemma measurable_program_estimate :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2) := by
  exact ho.comp (measurable_snd.fst.prodMk
    ((measurable_of_countable (CompletedLearner.terminalStatus (M:=M) (T:=T))).comp
      (measurable_program_run L hi ht T)))

include hi ht ho in
lemma admissible_of_borel (ρ : Measure Ω) : L.Admissible ρ := by
  have he := measurable_program_estimate L hi ht ho
  refine ⟨hi.aemeasurable, ?_, ?_, ?_, he.aemeasurable⟩
  · intro n a
    exact ((ht n).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aemeasurable
  · intro n a
    exact (ho.comp (measurable_id.prodMk (measurable_const (a:=(n,a))))).aemeasurable
  · intro s
    exact (he.comp (measurable_const.prodMk measurable_id)).aemeasurable
end BorelProgram

namespace CompletedLearner
variable {d M T : ℕ} {K : CompletedLearner d M T}
lemma Sampling.admissible (R : K.Sampling) : R.program.Admissible (coinLaw (T+1)) :=
  admissible_of_borel R.program R.measurable_initialChoice R.measurable_program_transition
    R.measurable_program_output _
end CompletedLearner
end StreamKernel




end CurrentProjection

end

end OAI
