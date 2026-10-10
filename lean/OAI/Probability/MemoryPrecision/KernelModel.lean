import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1
abbrev State (M : ℕ) := Fin (2^M)
abbrev Action (M : ℕ) := Bool × State M
abbrev Observations (d k : ℕ) := Fin k → (Vector d × ℝ)
abbrev Rows (d k : ℕ) := Fin k → Vector d

def UniformSphere (d : ℕ) : Measure (Sphere d) :=
  let euclideanGroup : NormedAddCommGroup (Vector d) :=
    PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ)
  let euclideanInner := PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)
  let σ := @Measure.toSphere (Vector d) euclideanGroup
    (@InnerProductSpace.toNormedSpace ℝ (Vector d) _
      euclideanGroup.toSeminormedAddCommGroup euclideanInner) inferInstance
    (@volume (Vector d) (@measureSpaceOfInnerProductSpace (Vector d)
      euclideanGroup euclideanInner inferInstance inferInstance inferInstance))
  (σ Set.univ)⁻¹ • σ

def RowLaw (d k : ℕ) : @Measure (Rows d k)
    (@MeasurableSpace.pi (Fin k) (fun _ => Vector d)
      (fun _ => @WithLp.measurableSpace
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (Fin d → ℝ) inferInstance)) :=
  let euclideanMeasurable := @WithLp.measurableSpace
    (@OfNat.ofNat ℝ≥0∞ 2
      (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
    (Fin d → ℝ) inferInstance
  @Measure.pi (Fin k) (fun _ => Vector d) inferInstance (fun _ => euclideanMeasurable)
    (fun _ => @stdGaussian (Vector d)
    (PiLp.normedAddCommGroup
      (@OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
      (fun _ : Fin d => ℝ))
    (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)) inferInstance euclideanMeasurable)
def ObservationReference (d : ℕ) : Measure (Vector d × ℝ) :=
  (stdGaussian (Vector d)).prod volume

structure Policy (d M T : ℕ) where
  initial : Action M → ℝ≥0∞
  initial_sum : ∑ a, initial a = 1
  transition : ℕ → State M → (Vector d × ℝ) → Action M → ℝ≥0∞
  transition_sum : ∀ t j obs, ∑ a, transition t j obs a = 1
  output : ℕ → State M → Measure (Sphere d)
  output_probability : ∀ t j, IsProbabilityMeasure (output t j)

namespace Policy
instance {d M T : ℕ} (K : Policy d M T) (t : ℕ) (j : State M) :
    IsProbabilityMeasure (K.output t j) := K.output_probability t j

def Completed {d M T : ℕ} (K : Policy d M T) : Prop :=
  ∀ t j a, AEMeasurable (fun obs => K.transition t j obs a) (ObservationReference d)
def Borel {d M T : ℕ} (K : Policy d M T) : Prop :=
  ∀ t j a, Measurable (fun obs => K.transition t j obs a)

def eval {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (n : ℕ) :
    (k : ℕ) → State M → X → Observations d k → ℝ≥0∞
  | 0, j, s, _ => w n j s
  | k+1, j, s, obs => ∑ a : Action M, K.transition (n+1) j (obs 0) a *
      if a.1 then w (n+1) a.2 s else K.eval w (n+1) k a.2 s (Fin.tail obs)

def pathValue {d M T : ℕ} {X : Type*} (K : Policy d M T)
    (w : ℕ → State M → X → ℝ≥0∞) (s : X) (obs : Observations d T) : ℝ≥0∞ :=
  ∑ a : Action M, K.initial a * if a.1 then w 0 a.2 s else K.eval w 0 T a.2 s obs

def records {d T : ℕ} (s : Sphere d) (A : Rows d T) : Observations d T :=
  fun index => (A index, @inner ℝ (EuclideanSpace ℝ (Fin d))
    (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
      (PiLp.seminormedAddCommGroup
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
        (fun _ : Fin d => ℝ))
      (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ))) s.val (A index))

def outputTest {d M T : ℕ} (K : Policy d M T) (f : Sphere d × Sphere d → ℝ≥0∞)
    (t : ℕ) (j : State M) (s : Sphere d) : ℝ≥0∞ :=
  ∫⁻ v, f (s,v) ∂K.output t j

def angleTest {d : ℕ} (ε : ℝ)
    (point : MemoryPrecision.Kernel.Sphere d × MemoryPrecision.Kernel.Sphere d) : ℝ≥0∞ :=
  @ite ℝ≥0∞ (Real.arccos (@inner ℝ (EuclideanSpace ℝ (Fin d))
      (@InnerProductSpace.toInner ℝ (EuclideanSpace ℝ (Fin d)) _
        (PiLp.seminormedAddCommGroup
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance))
          (fun _ : Fin d => ℝ))
        (PiLp.innerProductSpace (𝕜 := ℝ) (fun _ : Fin d => ℝ)))
      point.2.val point.1.val) ≤ ε) (Classical.propDecidable _) 1 0

def chordTest {d : ℕ} (ε : ℝ) (x : Sphere d × Sphere d) : ℝ≥0∞ :=
  {x : Sphere d × Sphere d | dist x.2.val x.1.val ≤ ε}.indicator (fun _ => 1) x

def experiment {d M T : ℕ} {Ω : Type u} (K : Ω → Policy d M T)
    (f : Sphere d × Sphere d → ℝ≥0∞) (z : Sphere d × (Ω × Rows d T)) : ℝ≥0∞ :=
  (K z.2.1).pathValue ((K z.2.1).outputTest f) z.1 (records z.1 z.2.2)

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) : Prop where
  completed : ∀ᵐ ω ∂ρ, (K ω).Completed
  experiment : ∀ f : Sphere d × Sphere d → ℝ≥0∞, Measurable f →
    (∀ x, f x ≤ 1) → AEMeasurable (experiment K f) (π.prod (ρ.prod (RowLaw d T)))

def Success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (angleTest ε) z ∂π.prod (ρ.prod (RowLaw d T))
def ChordSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (K : Ω → Policy d M T) (ρ : Measure Ω) (π : Measure (Sphere d)) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, experiment K (chordTest ε) z ∂π.prod (ρ.prod (RowLaw d T))
end Policy
end MemoryPrecision.Kernel


end

end OAI
