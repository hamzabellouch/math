import Mathlib

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace Classical

noncomputable section

namespace PosteriorReplicas

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Rows (d k : ℕ) := Fin k → Vec d
abbrev Labels (k : ℕ) := Fin k → ℝ
abbrev Data (d k : ℕ) := Rows d k × Labels k
abbrev Tuple (d m : ℕ) := Fin (m + 1) → Vec d

def sphereLaw (d : ℕ) : Measure (Vec d) :=
  let σ := (volume : Measure (Vec d)).toSphere
  ((σ univ)⁻¹ • σ).map Subtype.val

def gaussianRows (d k : ℕ) : Measure (Rows d k) :=
  Measure.pi fun _ => stdGaussian (Vec d)

instance (d k : ℕ) : IsProbabilityMeasure (gaussianRows d k) := by
  unfold gaussianRows
  infer_instance

def labels {d k : ℕ} (A : Rows d k) (s : Vec d) : Labels k :=
  fun i => ⟪A i, s⟫

lemma measurable_labels {d k : ℕ} :
    Measurable (fun z : Rows d k × Vec d => labels z.1 z.2) := by
  unfold labels
  fun_prop

def messageKernel {d k N : ℕ} (κ : Kernel (Data d k) (Fin N)) :
    Kernel (Vec d × Rows d k) (Fin N) :=
  κ.comap (fun z => (z.2, labels z.2 z.1)) (by
    unfold labels
    fun_prop)

instance {d k N : ℕ} (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsMarkovKernel (messageKernel κ) := by
  unfold messageKernel
  infer_instance

def signalMessageLaw {d k N : ℕ} (p : Measure (Vec d))
    (κ : Kernel (Data d k) (Fin N)) : Measure (Vec d × Fin N) :=
  ((p.prod (gaussianRows d k)) ⊗ₘ messageKernel κ).map
    (fun z => (z.1.1, z.2))

instance {d k N : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (signalMessageLaw p κ) := by
  unfold signalMessageLaw
  infer_instance

def sideLaw {d N : ℕ} (ℓ : ℕ) (q : Measure (Vec d × Fin N)) :
    Measure (Data d ℓ × (Vec d × Fin N)) :=
  ((gaussianRows d ℓ).prod q).map
    (fun z => ((z.1, labels z.1 z.2.1), z.2))

instance {d N : ℕ} (ℓ : ℕ) (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (sideLaw ℓ q) := by
  unfold sideLaw
  infer_instance

def messageEntropy {d N : ℕ} (q : Measure (Vec d × Fin N)) : ℝ :=
  ∑ w : Fin N, -(q.snd.real {w}) * Real.log (q.snd.real {w})

def conditionalInformation {d ℓ N : ℕ} [NeZero N]
    (μ : Measure (Data d ℓ × (Vec d × Fin N))) [IsFiniteMeasure μ] : ℝ≥0∞ :=
  klDiv μ (μ.fst ⊗ₘ (μ.condKernel.fst ×ₖ μ.condKernel.snd))

def GaussianReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    let k := 2 * (d / 16)
    let t := k + 1
    let ℓ := 4 * k
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (L : ℝ),
      Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ L) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw ℓ (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / (t : ℝ) +
            C * (d : ℝ) + C * Real.log (2 + Real.log L))

inductive BaseLaw where
  | spherical
  | gaussian
  deriving DecidableEq

def BaseLaw.measure (base : BaseLaw) (d : ℕ) : Measure (Vec d) :=
  match base with
  | .spherical => sphereLaw d
  | .gaussian => stdGaussian (Vec d)

def rowGram {d k : ℕ} (A : Rows d k) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ⟪A i, A j⟫

def liftLabel {d k : ℕ} (A : Rows d k) (y : Labels k) : Vec d :=
  ∑ i, ((rowGram A)⁻¹ *ᵥ y) i • A i

def kernelComponent {d k : ℕ} (A : Rows d k) (x : Vec d) : Vec d :=
  x - liftLabel A (labels A x)

def baseFiber {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    Measure (Vec d) :=
  match base with
  | .gaussian => (stdGaussian (Vec d)).map
      (fun x => liftLabel A y + kernelComponent A x)
  | .spherical => (stdGaussian (Vec d)).map
      (fun x => liftLabel A y +
        (Real.sqrt (1 - ‖liftLabel A y‖ ^ 2) / ‖kernelComponent A x‖) •
          kernelComponent A x)

def baseDensity {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  if LinearIndependent ℝ A then
    match base with
    | .gaussian => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(k : ℝ) / 2) *
          Real.exp (-‖liftLabel A y‖ ^ 2 / 2) / Real.sqrt (rowGram A).det)
    | .spherical => if ‖liftLabel A y‖ < 1 then ENNReal.ofReal
        (Real.Gamma ((d : ℝ) / 2) /
          (Real.pi ^ ((k : ℝ) / 2) * Real.Gamma (((d : ℝ) - k) / 2)) *
          (1 - ‖liftLabel A y‖ ^ 2) ^ (((d : ℝ) - k - 2) / 2) /
          Real.sqrt (rowGram A).det) else 0
  else 0

def tiltMass {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  ∫⁻ x, f x ∂baseFiber base A y

def projectedDensity {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  baseDensity base A y * tiltMass base f A y

def tiltedFiber {d k : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (A : Rows d k) (y : Labels k) : Measure (Vec d) :=
  if tiltMass base f A y = 0 then Measure.dirac 0
  else (tiltMass base f A y)⁻¹ • (baseFiber base A y).withDensity f

def differences {d m : ℕ} (u : Tuple d m) : Fin m → Vec d :=
  fun i => u i.succ - u 0

def differenceSpan {d m : ℕ} (u : Tuple d m) : Submodule ℝ (Vec d) :=
  Submodule.span ℝ (Set.range (differences u))

def affineVolume {d m : ℕ} (u : Tuple d m) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (differences u)).det

def constrainedRows {d m : ℕ} (k : ℕ) (u : Tuple d m) : Measure (Rows d k) :=
  (gaussianRows d k).map
    (fun A i => (differenceSpan u)ᗮ.starProjection (A i))

def equalLabelLeft {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (H : Rows d k × Labels k × Tuple d m → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ A, ∫⁻ y, (projectedDensity base f A y) ^ (m + 1) *
    ∫⁻ u, H (A, y, u) ∂Measure.pi (fun _ : Fin (m + 1) => tiltedFiber base f A y)
      ∂volume ∂gaussianRows d k

def equalLabelRight {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    (H : Rows d k × Labels k × Tuple d m → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(k * m : ℝ) / 2)) *
    ∫⁻ u, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
      ∫⁻ A, H (A, labels A (u 0), u) ∂constrainedRows k u
      ∂Measure.pi (fun _ : Fin (m + 1) => (base.measure d).withDensity f)

def EqualLabelMeasureIdentity : Prop :=
  ∀ (d k m : ℕ), 1 ≤ k → 1 ≤ m → k + m ≤ d - 2 →
    ∀ (base : BaseLaw) (f : Vec d → ℝ≥0∞), Measurable f →
      (∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ x, f x ≤ L) →
      equalLabelLeft (k := k) (m := m) base f (fun _ => 1) < ∞ ∧
      ∀ H : Rows d k × Labels k × Tuple d m → ℝ≥0∞,
        Measurable H → equalLabelLeft base f H = equalLabelRight base f H

def DistanceReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (b : ℝ),
      0 ≤ b → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp b) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d (d / 16)) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw (d / 2) (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / ((d / 8 : ℕ) : ℝ) +
            C * ((d : ℝ) + b / (d : ℝ)))

def SyntheticReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 16 ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (L : ℝ),
      1 ≤ L → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ L) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (z : Data d (d / 8) → Fin N) (hz : Measurable z),
        conditionalInformation
          (sideLaw (d / 2) (signalMessageLaw p (Kernel.deterministic z hz))) ≤
          ENNReal.ofReal (Real.log (N : ℝ) / ((d / 8 : ℕ) : ℝ) +
            C * ((d : ℝ) + Real.log (1 + Real.log L)))

def IncidenceReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    ∀ (p : Measure (Vec d)) [IsProbabilityMeasure p]
      (f : Vec d → ℝ) (F : ℝ),
      1 ≤ F → Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ F) →
      p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ (N : ℕ) [NeZero N] (κ : Kernel (Data d (d / 16)) (Fin N)) [IsMarkovKernel κ],
        conditionalInformation (sideLaw (d / 4) (signalMessageLaw p κ)) ≤
          ENNReal.ofReal (Real.log (N : ℝ) / ((d / 16 : ℕ) : ℝ) +
            C * (d : ℝ) + C * Real.log (1 + Real.log F))

def labelNorm {k : ℕ} (y : Labels k) : ℝ := ‖WithLp.toLp 2 y‖

def ballDensityVersion {d k : ℕ} (ν : Measure (Vec d))
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ =>
    ((volume : Measure (Labels k)) {v | labelNorm v < (n + 1 : ℝ)⁻¹})⁻¹ *
      ν {x | labelNorm (labels A x - y) < (n + 1 : ℝ)⁻¹}) Filter.atTop

def gaussianDensityVersion {d k : ℕ} (ν : Measure (Vec d))
    (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  Filter.liminf (fun n : ℕ => ∫⁻ x,
    ENNReal.ofReal ((2 * Real.pi * ((n + 1 : ℝ)⁻¹)^2) ^ (-(k : ℝ) / 2) *
      Real.exp (-(labelNorm (labels A x - y))^2 / (2 * ((n + 1 : ℝ)⁻¹)^2))) ∂ν)
    Filter.atTop

def EqualLabelVersions : Prop :=
  ∀ (d k m : ℕ), 1 ≤ k → 1 ≤ m → k + m ≤ d - 2 →
    ∀ (base : BaseLaw) (f : Vec d → ℝ≥0∞), Measurable f →
      (∃ L : ℝ≥0∞, L ≠ ∞ ∧ ∀ x, f x ≤ L) →
      let ν := (base.measure d).withDensity f
      (Measurable (fun z : Rows d k × Labels k => projectedDensity base f z.1 z.2)) ∧
      (Measurable (fun z : Rows d k × Labels k => ballDensityVersion ν z.1 z.2)) ∧
      (Measurable (fun z : Rows d k × Labels k => gaussianDensityVersion ν z.1 z.2)) ∧
      (∀ A : Rows d k, LinearIndependent ℝ A →
        ν.map (labels A) = volume.withDensity (projectedDensity base f A) ∧
        projectedDensity base f A =ᵐ[volume] ballDensityVersion ν A ∧
        projectedDensity base f A =ᵐ[volume] gaussianDensityVersion ν A) ∧
      (∀ᵐ u ∂Measure.pi (fun _ : Fin (m + 1) => ν),
        LinearIndependent ℝ (differences u) ∧
        ∀ᵐ A ∂constrainedRows k u,
          LinearIndependent ℝ A ∧
          (∀ i, labels A (u i) = labels A (u 0)) ∧
          (base = .spherical → ‖liftLabel A (labels A (u 0))‖ < 1) ∧
          0 < projectedDensity base f A (labels A (u 0)) ∧
          projectedDensity base f A (labels A (u 0)) ≠ ∞ ∧
          projectedDensity base f A (labels A (u 0)) =
            ballDensityVersion ν A (labels A (u 0)) ∧
          projectedDensity base f A (labels A (u 0)) =
            gaussianDensityVersion ν A (labels A (u 0)))

def haarRows (d ℓ : ℕ) : Measure (Rows d ℓ) :=
  (gaussianRows d ℓ).map (InnerProductSpace.gramSchmidtNormed ℝ)

def cmi {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (μ : Measure (Z × (X × Y))) [IsFiniteMeasure μ] : ℝ≥0∞ :=
  klDiv μ (μ.fst ⊗ₘ (μ.condKernel.fst ×ₖ μ.condKernel.snd))

def finiteEntropy {J : Type*} [Fintype J] [MeasurableSpace J] (μ : Measure J) : ℝ :=
  ∑ j, - μ.real {j} * Real.log (μ.real {j})

def stateMessageKernel {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) :
    Kernel ((Vec d × Fin V) × Rows d k) (Fin W) :=
  κ.comap (fun z => (z.1.2, (z.2, labels z.2 z.1.1))) (by unfold labels; fun_prop)

instance {d k V W : ℕ} (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsMarkovKernel (stateMessageKernel κ) := by
  unfold stateMessageKernel
  infer_instance

def stateMessageLaw {d k V W : ℕ} (q : Measure (Vec d × Fin V))
    (κ : Kernel (Fin V × Data d k) (Fin W)) : Measure ((Vec d × Fin V) × Fin W) :=
  (((q.prod (gaussianRows d k)) ⊗ₘ stateMessageKernel κ).map
    (fun z => (z.1.1, z.2)))

instance {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (stateMessageLaw q κ) := by
  unfold stateMessageLaw
  infer_instance

def stateHaarSideLaw {d V W : ℕ} (ℓ : ℕ)
    (q : Measure ((Vec d × Fin V) × Fin W)) :
    Measure ((Fin V × Data d ℓ) × (Vec d × Fin W)) :=
  ((haarRows d ℓ).prod q).map
    (fun z => ((z.2.1.2, (z.1, labels z.1 z.2.1.1)), (z.2.1.1, z.2.2)))

instance {d V W : ℕ} (ℓ : ℕ)
    (q : Measure ((Vec d × Fin V) × Fin W)) [IsFiniteMeasure q] :
    IsFiniteMeasure (stateHaarSideLaw ℓ q) := by
  unfold stateHaarSideLaw haarRows
  infer_instance

def terminalConditionalEntropy {d V W : ℕ}
    (q : Measure ((Vec d × Fin V) × Fin W)) : ℝ :=
  finiteEntropy (q.map (fun z => (z.1.2, z.2))) - finiteEntropy (q.map (fun z => z.1.2))

def HaarReplicaBlock : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 64 ≤ d →
    ∀ (V W : ℕ) [NeZero V] [NeZero W]
      (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q],
      q.fst = sphereLaw d →
      ∀ (κ : Kernel (Fin V × Data d (d / 16)) (Fin W)) [IsMarkovKernel κ],
        cmi (stateHaarSideLaw (d / 4) (stateMessageLaw q κ)) ≤
          ENNReal.ofReal (terminalConditionalEntropy (stateMessageLaw q κ) /
            ((d / 16 + 1 : ℕ) : ℝ) + C * (d : ℝ) +
            Real.log (1 + C * (d : ℝ) + finiteEntropy q.snd) +
            C * (finiteEntropy q.snd + Real.log (d : ℝ)) / (d : ℝ)^2)

end PosteriorReplicas
end
end

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace PosteriorRegression

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev UnitSphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2 ^ M)
abbrev Samples (d T : ℕ) := Fin T → Vector d

def uniformSphere (d : ℕ) : Measure (UnitSphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def sampleLaw (d T : ℕ) : Measure (Samples d T) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def observationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

namespace Learner

abbrev RunStatus (M : ℕ) := Sum (State M) (ℕ × State M)

def angularError {d : ℕ} (s ŝ : UnitSphere d) : ℝ :=
  Real.arccos ⟪ŝ.val, s.val⟫

end Learner

end PosteriorRegression

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace Classical

noncomputable section

namespace PosteriorRegression
abbrev CompletedObservation (d : ℕ) := NullMeasurableSpace (Vector d × ℝ) (observationReference d)
abbrev Destination (M : ℕ) := Bool × State M

structure CompletedKernelLearner (d M : ℕ) where
  initial : Measure (Destination M)
  initial_probability : IsProbabilityMeasure initial
  transition : ℕ → State M → Kernel (CompletedObservation d) (Destination M)
  transition_markov : ∀ t a, IsMarkovKernel (transition t a)
  output : ℕ → State M → Measure (UnitSphere d)
  output_probability : ∀ t a, IsProbabilityMeasure (output t a)

attribute [instance] CompletedKernelLearner.initial_probability
  CompletedKernelLearner.transition_markov CompletedKernelLearner.output_probability

namespace CompletedKernelLearner
open Learner
def destStatus {M : ℕ} (n : ℕ) (v : Destination M) : RunStatus M :=
  if v.1 then Sum.inr (n,v.2) else Sum.inl v.2

def finishState {M : ℕ} (T : ℕ) : RunStatus M → ℕ × State M
  | .inl a => (T,a)
  | .inr done => done

def stepMeasure {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) : RunStatus M → Measure (RunStatus M)
  | .inr done => Measure.dirac (.inr done)
  | .inl a => (K.transition (i.val+1) a (x i,⟪x i,s.val⟫)).map (destStatus (i.val+1))

def runMeasure {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : ℕ → Measure (RunStatus M)
  | 0 => K.initial.map (destStatus 0)
  | n+1 => if hn : n<T then (K.runMeasure s x n).bind (K.stepMeasure s x ⟨n,hn⟩)
      else K.runMeasure s x n

def terminalLaw {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : Measure (ℕ × State M) :=
  (K.runMeasure s x T).map (finishState T)

def estimateLaw {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : Measure (UnitSphere d) :=
  (K.terminalLaw s x).bind (fun a => K.output a.1 a.2)

end CompletedKernelLearner

structure JointKernelExperiment (d M T : ℕ) (Ω : Type u) [MeasurableSpace Ω]
    (ρ : Measure Ω) where
  rules : Ω → CompletedKernelLearner d M
  outputKernel : Kernel (Ω × (UnitSphere d × Samples d T)) (UnitSphere d)
  output_markov : IsMarkovKernel outputKernel
  conditional_output : ∀ᵐ ω ∂ρ, ∀ᵐ z ∂((uniformSphere d).prod (sampleLaw d T)),
    outputKernel (ω,z) = (rules ω).estimateLaw z.1 z.2

attribute [instance] JointKernelExperiment.output_markov

namespace JointKernelExperiment
open Learner
def law {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω] {ρ : Measure Ω}
    (E : JointKernelExperiment d M T Ω ρ) : Measure ((Ω × (UnitSphere d × Samples d T)) × UnitSphere d) :=
  (ρ.prod ((uniformSphere d).prod (sampleLaw d T))) ⊗ₘ E.outputKernel

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω] {ρ : Measure Ω}
    (E : JointKernelExperiment d M T Ω ρ) (ε : ℝ) : ℝ≥0∞ :=
  E.law {z | angularError z.1.2.1 z.2 ≤ ε}

end JointKernelExperiment

def KernelSubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ)^2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0<ε → ε≤1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ E : JointKernelExperiment d (M d) T Ω ρ,
    (2/3 : ℝ≥0∞) ≤ E.uniformSuccess ε →
    c * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ)

end PosteriorRegression

namespace PosteriorReplicas

end PosteriorReplicas
end
end

namespace PosteriorReplicas

universe u

theorem source_main : EqualLabelMeasureIdentity ∧ EqualLabelVersions ∧
    GaussianReplicaBlock ∧ DistanceReplicaBlock ∧ HaarReplicaBlock ∧
    SyntheticReplicaBlock ∧ IncidenceReplicaBlock ∧
    PosteriorRegression.KernelSubquadraticMemory.{u} := by
  sorry

end PosteriorReplicas

end OAI
