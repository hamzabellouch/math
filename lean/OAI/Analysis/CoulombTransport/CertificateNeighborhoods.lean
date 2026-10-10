import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uIndex uX uY

noncomputable section

open Set Filter Metric
open scoped ENNReal

namespace Problem356

/-- Finitely many eventual properties hold simultaneously on balls with one
common positive radius around their respective centers. -/
theorem finite_eventual_neighborhoods {ι : Type uIndex} {X : Type uX} [PseudoMetricSpace X]
    (s : Finset ι) (p : ι → X) (P : ι → X → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in nhds (p i), P i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → P i x := by
  classical
  have hone : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧
      ∀ x, dist x (p i) < r → P i x := by
    intro i hi
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hP i hi)
    exact ⟨r, hr, fun x hx => h hx⟩
  clear hP
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s his ih =>
      obtain ⟨r, hr, hri⟩ := hone i (Finset.mem_insert_self i s)
      obtain ⟨q, hq, hqs⟩ := ih (fun j hj => hone j (Finset.mem_insert_of_mem hj))
      refine ⟨min r q, lt_min hr hq, ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hri x (lt_of_lt_of_le hx (min_le_left _ _))
      · exact hqs j hj x (lt_of_lt_of_le hx (min_le_right _ _))

/-- Triple-coordinate ball version of finite eventual shrinking. -/
theorem finite_eventual_triple_neighborhoods {ι : Type uIndex}
    (s : Finset ι) (p : ι → Triple) (P : ι → Triple → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ t in nhds (p i), P i t) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x y z : E3,
      x ∈ ball (p i).1 r → y ∈ ball (p i).2.1 r →
      z ∈ ball (p i).2.2 r → P i (x, (y, z)) := by
  obtain ⟨r, hr, h⟩ := finite_eventual_neighborhoods s p P hP
  refine ⟨r, hr, ?_⟩
  intro i hi x y z hx hy hz
  apply h i hi (x, (y, z))
  simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hx (And.intro hy hz)

/-- Finitely many strict inequalities at their respective centers persist on
one common positive-radius neighborhood. This is the finite shrinking step
for the bad, distinct-center component types in the certificate. -/
theorem finite_strict_neighborhoods {ι : Type uIndex} {X : Type uX} {Y : Type uY} [PseudoMetricSpace X]
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y]
    (s : Finset ι) (p : ι → X) (f g : ι → X → Y)
    (hf : ∀ i ∈ s, ContinuousAt (f i) (p i))
    (hg : ∀ i ∈ s, ContinuousAt (g i) (p i))
    (hgap : ∀ i ∈ s, f i (p i) < g i (p i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → f i x < g i x := by
  exact finite_eventual_neighborhoods s p (fun i x => f i x < g i x)
    (fun i hi => (hf i hi).eventually_lt (hg i hi) (hgap i hi))

/-- Product-space version of finite shrinking, expressed by separate ball
conditions on all three coordinates. -/
theorem finite_strict_triple_neighborhoods {ι : Type uIndex} {Y : Type uY}
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y]
    (s : Finset ι) (p : ι → Triple) (f g : ι → Triple → Y)
    (hf : ∀ i ∈ s, ContinuousAt (f i) (p i))
    (hg : ∀ i ∈ s, ContinuousAt (g i) (p i))
    (hgap : ∀ i ∈ s, f i (p i) < g i (p i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x y z : E3,
      x ∈ ball (p i).1 r → y ∈ ball (p i).2.1 r →
      z ∈ ball (p i).2.2 r → f i (x, (y, z)) < g i (x, (y, z)) := by
  obtain ⟨r, hr, h⟩ := finite_strict_neighborhoods s p f g hf hg hgap
  refine ⟨r, hr, ?_⟩
  intro i hi x y z hx hy hz
  apply h i hi (x, (y, z))
  simpa only [Prod.dist_eq, max_lt_iff, Metric.mem_ball] using And.intro hx (And.intro hy hz)

end Problem356

end

end OAI
