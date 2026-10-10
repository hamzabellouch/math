import Mathlib.Probability.UniformOn

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Balanced.Slots

universe u v

variable {ι : Type u} (V : ι → Type v)

abbrev Assignment := (i : ι) → V i

def law [Fintype ι] [∀ i, Fintype (V i)] [∀ i, MeasurableSpace (V i)] :
    Measure (Assignment V) :=
  Measure.pi (fun i => uniformOn (Set.univ : Set (V i)))

def cylinder (J : Finset ι) (a : Assignment V) : Set (Assignment V) :=
  {ω | ∀ i ∈ J, ω i = a i}

def DependsOn (J : Finset ι) (A : Set (Assignment V)) : Prop :=
  ∀ ω ω', (∀ i ∈ J, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)

def pairEvent (i j : ι) (a : V i) (b : V j) : Set (Assignment V) :=
  {ω | ω i = a ∧ ω j = b}

end Balanced.Slots

end

end OAI
