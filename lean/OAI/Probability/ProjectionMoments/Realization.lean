import OAI.Probability.ProjectionMoments.Kernels

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

structure Realizer (K : FiniteKernelLearner d M T) where
  transition : ℕ → State M → (Vector d × ℝ) → I → Bool × State M
  transition_measurable : ∀ t j, Measurable (Function.uncurry (transition t j))
  transition_law : ∀ t j obs, volume.map (transition t j obs) = K.transition t j obs
  output : ℕ → State M → I → UnitSphere d
  output_measurable : ∀ t j, Measurable (output t j)
  output_law : ∀ t j, volume.map (output t j) = K.output t j

lemma exists_realizer (K : FiniteKernelLearner d M T) (hK : K.BorelRules) : Nonempty K.Realizer := by
  classical
  let j₀ : State M := ⟨0,by simp⟩
  let : IsProbabilityMeasure (K.output 0 j₀) := K.output_probability 0 j₀
  let : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 j₀)
  have ht (t : ℕ) (j : State M) : ∃ f : (Vector d × ℝ) → I → Bool × State M,
      Measurable (Function.uncurry f) ∧ ∀ obs, volume.map (f obs) = K.transition t j obs := by
    let κ : Kernel (Vector d × ℝ) (Bool × State M) := ⟨K.transition t j,hK.transition t j⟩
    let : IsMarkovKernel κ := ⟨K.transition_probability t j⟩
    exact κ.exists_measurable_map_eq_unitInterval
  have ho (t : ℕ) (j : State M) : ∃ g : I → UnitSphere d, Measurable g ∧ volume.map g = K.output t j := by
    let : IsProbabilityMeasure (K.output t j) := K.output_probability t j
    exact (K.output t j).exists_measurable_map_eq
  choose f hf hfl using ht
  choose g hg hgl using ho
  exact ⟨⟨f,hf,hfl,g,hg,hgl⟩⟩

def tapeLaw (K : FiniteKernelLearner d M T) : Measure (Tape M T) :=
  K.initial.prod ((Measure.pi (fun _ => (volume : Measure I))).prod volume)

instance tapeLaw_probability (K : FiniteKernelLearner d M T) : IsProbabilityMeasure K.tapeLaw := by
  let := K.initial_probability
  unfold tapeLaw
  infer_instance

def Realizer.toLearner {K : FiniteKernelLearner d M T} (R : K.Realizer) : Learner d M T (Tape M T) where
  initialChoice := Prod.fst
  transition := fun t ω j obs => if ht : 0 < t ∧ t ≤ T then
    R.transition t j obs (ω.2.1 ⟨t-1,by omega⟩) else (false,j)
  output := fun t ω j => R.output t j ω.2.2

lemma Realizer.measurableRules {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    R.toLearner.MeasurableRules := by
  refine ⟨measurable_fst,fun t j => ?_,fun t j => (R.output_measurable t j).comp (by fun_prop)⟩
  dsimp [Realizer.toLearner]
  split_ifs with ht
  · exact (R.transition_measurable t j).comp (show Measurable (fun z : Tape M T × (Vector d × ℝ) =>
      (z.2,z.1.2.1 ⟨t-1,by omega⟩)) from by fun_prop)
  · exact measurable_const

def Realizer.taggedTransition {K : FiniteKernelLearner d M T} (R : K.Realizer) (t : ℕ) :
    TaggedState M T → (Vector d × ℝ) → I → TaggedState M T
  | .inr a, _, _ => .inr a
  | .inl j, obs, u => if ht : t ≤ T then destination t ht (R.transition t j obs u) else .inl j

lemma Realizer.tagged_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) : Measurable (R.taggedTransition t j obs) := by
  cases j with
  | inr a => exact measurable_const
  | inl j =>
    change Measurable (fun u => R.taggedTransition t (.inl j) obs u)
    simp only [Realizer.taggedTransition]
    split_ifs with ht
    · exact (measurable_of_finite (destination t ht)).comp (R.transition_measurable t j).of_uncurry_left
    · exact measurable_const

lemma Realizer.tagged_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) :
    volume.map (R.taggedTransition t j obs) = K.taggedKernel t j obs := by
  cases j with
  | inr a =>
    change volume.map (fun _ : I => Sum.inr a) = Measure.dirac (.inr a)
    simp [Measure.map_const]
  | inl j =>
    change volume.map (fun u => R.taggedTransition t (.inl j) obs u) = _
    simp only [Realizer.taggedTransition,taggedKernel]
    split_ifs with ht
    · rw [← R.transition_law,Measure.map_map (measurable_of_finite _)
        (R.transition_measurable t j).of_uncurry_left]
      rfl
    · simp [Measure.map_const]

def Realizer.terminalOutput {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    TaggedState M T → I → UnitSphere d
  | .inl j => R.output T j
  | .inr (t,j) => R.output t j

lemma Realizer.terminalOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalOutput j) := by
  cases j with
  | inl j => exact R.output_measurable T j
  | inr a => exact R.output_measurable a.1 a.2

lemma Realizer.terminalOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalOutput j) = K.terminalOutput j := by
  cases j with
  | inl j => exact R.output_law T j
  | inr a => exact R.output_law a.1 a.2

def experimentLaw (K : FiniteKernelLearner d M T) (obs : Fin T → (Vector d × ℝ)) : Measure (UnitSphere d) :=
  K.initial.bind (fun a => (kernelRun K.taggedKernel T (taggedStart a) obs).bind K.terminalOutput)

lemma Realizer.run_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) {n : ℕ} (hn : n ≤ T) :
    R.toLearner.run s ω x n = decodeTagged
      (coinRun R.taggedTransition n (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i))) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [Learner.run,ih (by omega)]
    have hp := fin_prefix_snoc hn (fun i => (x i,⟪s.val,x i⟫))
    rw [hp,fin_prefix_snoc hn ω.2.1,coinRun,Fin.init_snoc,Fin.init_snoc,Fin.snoc_last,Fin.snoc_last]
    generalize coinRun R.taggedTransition n (taggedStart ω.1)
      (fun i => (x (Fin.castLE (by omega : n ≤ T) i),⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫))
      (fun i => ω.2.1 (Fin.castLE (by omega : n ≤ T) i)) = j
    cases j with
    | inr a => rfl
    | inl j =>
      simp only [decodeTagged,Realizer.taggedTransition,Realizer.toLearner,
        dite_eq_left (by omega : n < T),dite_eq_left (by omega : 0 < n+1 ∧ n+1 ≤ T),
        dite_eq_left (by omega : n+1 ≤ T),destination,real_inner_comm,Nat.add_sub_cancel]
      split_ifs <;> rfl

lemma Realizer.estimate_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.estimate s ω x = R.terminalOutput
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) ω.2.2 := by
  unfold Learner.estimate Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

end FiniteKernelLearner

lemma map_finite_prod_eq_bind {A B C : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite ν] {f : A × B → C} (hf : Measurable f) :
    (μ.prod ν).map f = μ.bind (fun a => ν.map (fun b => f (a,b))) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf,lintegral_prod (fun z => g (f z)) (hg.comp hf).aemeasurable,
    Measure.lintegral_bind (measurable_of_finite _).aemeasurable hg.aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_map hg (hf.comp (measurable_const.prodMk measurable_id))).symm

lemma coinRun_output_law {J O Y : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] [MeasurableSpace O] [MeasurableSpace Y]
    {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    {g : J → I → Y} {Q : J → Measure Y} (hg : ∀ j, Measurable (g j))
    (hQ : ∀ j, volume.map (g j) = Q j) (n : ℕ) (j : J) (obs : Fin n → O) :
    ((Measure.pi (fun _ => (volume : Measure I))).prod volume).map
      (fun z => g (coinRun F n j obs z.1) z.2) = (kernelRun P n j obs).bind Q := by
  have hm : Measurable (fun z : (Fin n → I) × I => g (coinRun F n j obs z.1) z.2) :=
    measurable_select (h := fun a (z : (Fin n → I) × I) => g a z.2)
      (fun a => (hg a).comp measurable_snd) ((measurable_coinRun hF n j obs).comp measurable_fst)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm,lintegral_prod (fun z => f (g (coinRun F n j obs z.1) z.2)) (hf.comp hm).aemeasurable]
  have ho (a : J) : (∫⁻ u, f (g a u) ∂volume) = ∫⁻ y, f y ∂Q a := by
    rw [← hQ]
    exact (lintegral_map hf (hg a)).symm
  simp_rw [ho]
  rw [lintegral_coinRun hF hP n j obs (fun a => ∫⁻ y, f y ∂Q a)]
  exact (Measure.lintegral_bind (measurable_of_finite _).aemeasurable hf.aemeasurable).symm

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

def Realizer.terminalJointOutput {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) (u : I) : Result d M := (terminalTag j,R.terminalOutput j u)

lemma Realizer.terminalJointOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalJointOutput j) :=
  measurable_const.prodMk (R.terminalOutput_measurable j)

lemma Realizer.terminalJointOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalJointOutput j) = K.terminalJointOutput j := by
  rw [FiniteKernelLearner.terminalJointOutput,← R.terminalOutput_law,
    Measure.map_map (by fun_prop) (R.terminalOutput_measurable j)]
  rfl

lemma Realizer.terminal_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.terminal s ω x = terminalTag
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) := by
  unfold Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

theorem Realizer.conditional_joint_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (x : Samples d T) :
    K.tapeLaw.map (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) := by
  have hm : Measurable (fun ω : Tape M T =>
      (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) :=
    ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (s,(ω,x))) from by fun_prop)
  unfold tapeLaw jointExperimentLaw
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : IsFiniteMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : SigmaFinite ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := IsFiniteMeasure.toSigmaFinite _
  rw [map_finite_prod_eq_bind K.initial
    ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod (volume : Measure I)) hm]
  congr 1
  funext a
  have he : (fun z : (Fin T → I) × I =>
      (R.toLearner.terminal s (a,z) x,R.toLearner.estimate s (a,z) x)) =
      (fun z => R.terminalJointOutput
        (coinRun R.taggedTransition T (taggedStart a) (fun i => (x i,⟪s.val,x i⟫)) z.1) z.2) := by
    funext z
    rw [R.terminal_eq_coinRun,R.estimate_eq_coinRun]
    rfl
  rw [he]
  exact coinRun_output_law R.tagged_measurable R.tagged_law R.terminalJointOutput_measurable
    R.terminalJointOutput_law T (taggedStart a) _

end FiniteKernelLearner
end NoiselessRegression

end

end OAI
