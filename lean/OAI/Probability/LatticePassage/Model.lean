import OAI.Probability.LatticePassage.Paths
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.ProductMeasure
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Filter Topology

abbrev Vertex := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def lattice : SimpleGraph Vertex where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨by intros x y h; simpa only [abs_sub_comm] using h⟩
  loopless := ⟨by intro x; simp⟩

abbrev Edge := lattice.edgeSet
abbrev Environment := Weights lattice

noncomputable instance expOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def environmentLaw : Measure Environment :=
  Measure.infinitePi (fun _ : Edge => expMeasure 1)

def embed (x : Vertex) : Plane := ((x.1 : ℝ), (x.2 : ℝ))

def scaleVertex (n : ℕ) (x : Vertex) : Vertex := ((n : ℤ) * x.1, (n : ℤ) * x.2)

structure TimeNorm where
  seminorm : Seminorm ℝ Plane
  definite : ∀ x, seminorm x = 0 → x = 0

def HasTimeConstant (μ : TimeNorm) : Prop :=
  ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex,
    Tendsto (fun n : ℕ => passageTime ω (0, 0) (scaleVertex n x) / (n : ℝ))
      atTop (𝓝 (μ.seminorm (embed x)))

def StrictlyConvexUnitSphere (μ : TimeNorm) : Prop :=
  ∀ x y : Plane, μ.seminorm x = 1 → μ.seminorm y = 1 → x ≠ y →
    ∀ t : ℝ, 0 < t → t < 1 → μ.seminorm ((1 - t) • x + t • y) < 1

def StrictlyConvexLimitShape (μ : TimeNorm) : Prop :=
  ∀ x y : Plane, x ∈ frontier {z | μ.seminorm z ≤ 1} →
    y ∈ frontier {z | μ.seminorm z ≤ 1} → x ≠ y →
    ∀ t : ℝ, 0 < t → t < 1 → μ.seminorm ((1 - t) • x + t • y) < 1

def MainTarget : Prop := (∃ μ : TimeNorm, HasTimeConstant μ) ∧
  ∀ μ : TimeNorm, HasTimeConstant μ → StrictlyConvexLimitShape μ

end CompanionFPP

end OAI
