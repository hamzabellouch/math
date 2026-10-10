import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyTraceIntegral
import OAI.Probability.SKBarriers.Hierarchy.BlockAxis

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SegmentTrace
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySegment_trace_integral (n a N : ℕ) (haN : a+N ≤ n) (hN : 0 < N)
    (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin n, a+N ≤ i.val → p ≤ m i)
    (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s (i : Fin N), U s (coordinateAxis n ⟨a+i,by omega⟩) = scale*v s i) :
    (∫ z, hierarchyTraceSquare n m U v ⟨a,by omega⟩ z
      ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap n m U (fun i s => v s i) ⟨a+N,by omega⟩-
      hierarchyMeanOverlap n m U (fun i s => v s i) ⟨a,by omega⟩+
      1/((N : ℝ)*scale^2*p^2) := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le haN
  rw [Nat.add_assoc] at hd
  subst n
  apply hierarchyBlock_trace_integral a N d hN m U p scale hp ha hl hb
    (fun i => hm ⟨a+N+i,by omega⟩ (by simp))
    (fun i => hmu ⟨a+N+i,by omega⟩)
    (fun i j hij => hmono (by change a+N+i.val ≤ a+N+j.val; omega)) v hvb
  intro s i
  rw [parameterBlocks_noise_axis]
  exact hv s i
end SegmentTrace
end SK.Analytic

end
end

end

end OAI
