import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferChildNode

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferRootLaw {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    SupportedPairMeasures (PairAtHeight (realPosition (step e)) (a+1)) :=
  ⟨Measure.dirac (pairRestore e f ⌈R₀⌉₊ x), by
    apply ae_iff.mp
    rw [ae_dirac_iff (Set.to_countable _).measurableSet]
    exact pairRestore_height e f hef ⌈R₀⌉₊ a x hx⟩

noncomputable def bufferRootNode {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a) :
    AdaptedBufferNode e where
  level := a+1
  radius := R₀
  law := fun _ => bufferRootLaw e f hef R₀ a x hx
  law_rows := measurable_const
  active := Set.univ
  active_rows := MeasurableSet.univ

lemma bufferRootNode_valid {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (κ : ℝ≥0) :
    BufferNodeValid e f (signedCoordinate f (x.2-x.1)) κ (bufferRootNode e f hef R₀ a x hx) := by
  intro ω _ _
  have hp : IsProbabilityMeasure (Measure.dirac (pairRestore e f ⌈R₀⌉₊ x)) := inferInstance
  have hg : ∀ᵐ y ∂Measure.dirac (pairRestore e f ⌈R₀⌉₊ x),
      signedCoordinate f (x.2-x.1)+R₀ ≤ signedCoordinate f (y.2-y.1) := by
    rw [ae_dirac_iff (Set.to_countable _).measurableSet,pairRestore_gap]
    linarith [Nat.le_ceil R₀]
  exact ⟨hp,hg⟩

lemma bufferRootNode_retained {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (R₀ a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (ω : Environment d) {κ : ℝ≥0} (hκ : ∀ y u, κ ≤ (ω y).1 u) :
    (κ : ℝ≥0∞)^(⌈R₀⌉₊+2) • ((bufferRootNode e f hef R₀ a x hx).law ω).val ≤
      rawPairEndpointLaw (realPosition (step e)) 1 ω x :=
  rawPairEndpointLaw_restoration e f hef ⌈R₀⌉₊ ω x hκ
end DirectionalTransience

end

end

end OAI
