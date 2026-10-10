import OAI.Probability.GaussianReplacement.CompletedKernel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace CurrentProjection

namespace StreamKernel
open NoiselessRegression unitInterval





structure CompletedLearner (d M T : ℕ) where
  initial : Measure (Bool × State M)
  initial_probability : IsProbabilityMeasure initial
  transition : ℕ → State M → (NoiselessRegression.Vector d × ℝ) → Measure (Bool × State M)
  transition_probability : ∀ n a o, IsProbabilityMeasure (transition n a o)
  transition_completed : ∀ n a, AEMeasurable (transition n a) (observationReference d)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ n a, IsProbabilityMeasure (output n a)

instance runStatus_singletons (M : ℕ) :
    MeasurableSingletonClass (NoiselessRegression.Learner.RunStatus M) where
  measurableSet_singleton x := by
    rw [measurableSet_sum_iff]
    cases x with
    | inl a =>
      constructor
      · simp
      · have h : (Sum.inr : ℕ × State M → NoiselessRegression.Learner.RunStatus M) ⁻¹' {Sum.inl a} = ∅ := by
          ext z
          simp
        rw [h]
        exact MeasurableSet.empty
    | inr a =>
      constructor
      · simp
      · have h : (Sum.inr : ℕ × State M → NoiselessRegression.Learner.RunStatus M) ⁻¹' {Sum.inr a} = {a} := by
          ext z
          simp
        rw [h]
        exact measurableSet_singleton a

namespace CompletedLearner
variable {d M T : ℕ} (K : CompletedLearner d M T)


def startStatus (a : Bool × State M) : NoiselessRegression.Learner.RunStatus M :=
  if a.1 then Sum.inr (0,a.2) else Sum.inl a.2

def choiceStatus (n : ℕ) (a : Bool × State M) : NoiselessRegression.Learner.RunStatus M :=
  if a.1 then Sum.inr (n,a.2) else Sum.inl a.2


def nextLaw (s : UnitSphere d) (x : Samples d T) (n : ℕ) :
    NoiselessRegression.Learner.RunStatus M → Measure (NoiselessRegression.Learner.RunStatus M)
  | .inr done => Measure.dirac (.inr done)
  | .inl a => if hn : n < T then
      (K.transition (n+1) a (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).map (choiceStatus (n+1))
    else Measure.dirac (.inl a)



def runLaw (s : UnitSphere d) (x : Samples d T) :
    ℕ → Measure (NoiselessRegression.Learner.RunStatus M)
  | 0 => K.initial.map startStatus
  | n+1 => (runLaw s x n).bind (K.nextLaw s x n)

def terminalStatus : NoiselessRegression.Learner.RunStatus M → ℕ × State M
  | .inl a => (T,a)
  | .inr done => done


def estimateLaw (s : UnitSphere d) (x : Samples d T) : Measure (UnitSphere d) :=
  ((K.runLaw s x T).map (terminalStatus (T:=T))).bind
    (fun a => K.output a.1 a.2)



def uniformSuccess (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.estimateLaw z.1 z.2 {v | NoiselessRegression.Learner.angularError z.1 v ≤ ε}
      ∂(NoiselessRegression.uniformSphere d).prod (sampleLaw d T)



def borel : CompletedLearner d M T where
  initial := K.initial
  initial_probability := K.initial_probability
  transition := fun n a => borelKernel (K.transition n a) (K.transition_completed n a)
  transition_probability := fun _ _ _ => inferInstance
  transition_completed := fun n a =>
    (borelKernel (K.transition n a) (K.transition_completed n a)).measurable.aemeasurable
  output := K.output
  output_probability := K.output_probability

lemma borel_transition_ae (n : ℕ) (a : State M) :
    K.borel.transition n a =ᵐ[observationReference d] K.transition n a :=
  borelKernel_ae _ _ (K.transition_probability n a)


def transitionKernel : Kernel ((ℕ × State M) × (NoiselessRegression.Vector d × ℝ))
    (Bool × State M) :=
  ⟨fun p => K.borel.transition p.1.1 p.1.2 p.2,
    measurable_from_prod_countable_right fun a =>
      (borelKernel (K.transition a.1 a.2) (K.transition_completed a.1 a.2)).measurable⟩

instance transitionKernel_markov : IsMarkovKernel K.transitionKernel :=
  ⟨fun _ => K.borel.transition_probability _ _ _⟩

def outputKernel : Kernel (ℕ × State M) (UnitSphere d) :=
  ⟨fun a => K.output a.1 a.2, measurable_of_countable _⟩
instance outputKernel_markov : IsMarkovKernel K.outputKernel :=
  ⟨fun _ => K.output_probability _ _⟩

end CompletedLearner
end StreamKernel




end CurrentProjection

end

end OAI
