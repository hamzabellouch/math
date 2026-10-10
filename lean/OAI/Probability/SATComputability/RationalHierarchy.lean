import OAI.Probability.SATComputability.RationalWeights
import OAI.Probability.DilutedSpin.FiniteHierarchyDense

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory Set Filter TopologicalSpace
open scoped Topology BigOperators NNReal

noncomputable def RationalWeights.toAtomic {ι : Type*} [Fintype ι]
    (w : RationalWeights ι) : AtomicWeights ι :=
  ⟨fun i => ⟨w.val i, by exact_mod_cast w.property.1 i⟩, by
    exact NNReal.coe_injective ((NNReal.coe_sum Finset.univ
      (fun i => (⟨(w.val i : ℝ), by exact_mod_cast w.property.1 i⟩ : ℝ≥0))).trans
        (by
          change (∑ i, (w.val i : ℝ)) = 1
          exact_mod_cast w.property.2))⟩

theorem rationalWeights_atomic_dense {ι : Type*} [Fintype ι] :
    DenseRange (RationalWeights.toAtomic (ι := ι)) := by
  intro w
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let P : FiniteLaw ι := ⟨fun i => w.val i, fun i => (w.val i).property, by
    simpa using congrArg (fun q : ℝ≥0 => (q : ℝ)) w.property⟩
  obtain ⟨q, hq⟩ := exists_rational_weights_near P hε
  refine ⟨q.toAtomic, ⟨q, rfl⟩, ?_⟩
  rw [dist_comm]
  change dist (fun i => (q.toAtomic.val i)) w.val < ε
  apply (dist_pi_lt_iff hε).mpr
  intro i
  change |(q.val i : ℝ) - (w.val i : ℝ)| < ε
  exact hq i

def RationalTree : ℕ → Type
  | 0 => ℚ
  | r+1 => Σ n : ℕ, RationalWeights (Fin n) × (Fin n → RationalTree r)

instance rationalWeightsEncodable (n : ℕ) : Encodable (RationalWeights (Fin n)) := by
  unfold RationalWeights
  infer_instance

@[instance_reducible] def rationalTreeEncoding : (r : ℕ) → Encodable (RationalTree r)
  | 0 => Rat.instEncodable
  | r+1 => by
    letI := rationalTreeEncoding r
    exact inferInstanceAs (Encodable (Σ n : ℕ,
      RationalWeights (Fin n) × (Fin n → RationalTree r)))

instance rationalTreeEncodable (r : ℕ) : Encodable (RationalTree r) := rationalTreeEncoding r

local instance rationalHierarchyMeasurableSpace (space : TopCat) : MeasurableSpace space :=
  borel space
local instance rationalHierarchyBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

noncomputable def rationalTreeValue : (r : ℕ) → RationalTree r → Hierarchy r
  | 0, x => Rat.cast (K := ℝ) x
  | r+1, ⟨_, q, x⟩ => atomicProbability (fun i => rationalTreeValue r (x i)) q.toAtomic

theorem rationalTreeValue_finite (r : ℕ) (x : RationalTree r) :
    FiniteHierarchy r (rationalTreeValue r x) := by
  induction r with
  | zero => trivial
  | succ r ih =>
    obtain ⟨n, q, x⟩ := x
    exact ⟨n, fun i => rationalTreeValue r (x i), q.toAtomic,
      fun i => ih (x i), rfl⟩

theorem rationalTreeValue_dense (r : ℕ) : DenseRange (rationalTreeValue r) := by
  induction r with
  | zero =>
    change DenseRange (fun x : ℚ => (x : ℝ))
    exact Rat.denseRange_cast
  | succ r ih =>
    let : MetrizableSpace (Hierarchy r) := (hierarchy_properties r).1
    let : MetricSpace (Hierarchy r) := metrizableSpaceMetric (Hierarchy r)
    let : SeparableSpace (Hierarchy r) := (hierarchy_properties r).2
    let S := range (rationalTreeValue (r+1))
    let T := {μ : ProbabilityMeasure (Hierarchy r) | ∃ (n : ℕ)
      (x : Fin n → Hierarchy r) (w : AtomicWeights (Fin n)),
      (∀ i, x i ∈ range (rationalTreeValue r)) ∧ μ = atomicProbability x w}
    have hd : Dense T := finite_atomic_dense (range (rationalTreeValue r)) ih
    have hs : T ⊆ closure S := by
      rintro μ ⟨n, x, w, hx, rfl⟩
      choose y hy using hx
      have hnear := mem_closure_image (continuous_atomicProbability x).continuousAt
        (rationalWeights_atomic_dense w)
      apply (closure_mono (show atomicProbability x '' range RationalWeights.toAtomic ⊆ S from ?_)) hnear
      rintro μ ⟨q, ⟨q', rfl⟩, rfl⟩
      refine ⟨⟨n, q', y⟩, ?_⟩
      change atomicProbability (fun i => rationalTreeValue r (y i)) q'.toAtomic = _
      congr 1
      exact funext hy
    intro μ
    have h := (closure_mono hs) (hd μ)
    change μ ∈ closure (closure S) at h
    rw [closure_closure] at h
    exact h

end FixedClauseThreshold.Computability

end OAI
