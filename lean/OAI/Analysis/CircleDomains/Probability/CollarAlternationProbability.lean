import OAI.Analysis.CircleDomains.Selection.AlternatingTailCrossing
import OAI.Analysis.CircleDomains.Selection.FourSampleBound

namespace OAI

/-! Four positive-mass collar arcs force a quantitative lower bound for
meetings of the two independent original path laws. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X A B : Type*} [MetricSpace X] [MeasurableSpace A] [MeasurableSpace B]

theorem collar_alternation_probability (hcross : UnitDiskAlternatingContinua)
    (V : Set X) (hV : IsOpen V) (f : X → ℂ)
    (hf : ContinuousOn f (closure V)) (hfinj : InjOn f (closure V))
    (hfdisk : MapsTo f (closure V) (Metric.closedBall 0 1))
    (χ : X → UnitAddCircle)
    (hχ : ∀ x ∈ frontier V, f x = standardCirclePoint (χ x))
    (P : ProbabilityMeasure A) (Q : ProbabilityMeasure B)
    (a : A → C(PathTime, X)) (b : B → C(PathTime, X))
    (p q : X) (hp : p ∈ V) (hq : q ∈ V)
    (ha : ∀ᵐ z ∂(P : Measure A), a z ⊥ ∉ V ∧ a z ⊤ = p)
    (hb : ∀ᵐ z ∂(Q : Measure B), b z ⊥ ∉ V ∧ b z ⊤ = q)
    (l u : Fin 4 → ℚ) (horder : ∀ i j, i < j → u i < l j)
    (ha0 : (1 / 10 : ℝ≥0∞) ≤ (P : Measure A)
      {z | χ (a z (lastEntryTime (a z) V)) ∈ rationalCircleArc (l 0) (u 0)})
    (ha2 : (1 / 10 : ℝ≥0∞) ≤ (P : Measure A)
      {z | χ (a z (lastEntryTime (a z) V)) ∈ rationalCircleArc (l 2) (u 2)})
    (hb1 : (1 / 10 : ℝ≥0∞) ≤ (Q : Measure B)
      {z | χ (b z (lastEntryTime (b z) V)) ∈ rationalCircleArc (l 1) (u 1)})
    (hb3 : (1 / 10 : ℝ≥0∞) ≤ (Q : Measure B)
      {z | χ (b z (lastEntryTime (b z) V)) ∈ rationalCircleArc (l 3) (u 3)}) :
    (1 / 10 : ℝ≥0∞) ^ 4 ≤ 4 * ((P : Measure A).prod (Q : Measure B))
      {z | ∃ x ∈ V, x ∈ range (a z.1) ∧ x ∈ range (b z.2)} := by
  let E (i : Fin 4) (γ : C(PathTime, X)) :=
    χ (γ (lastEntryTime γ V)) ∈ rationalCircleArc (l i) (u i)
  let R : Set (A × B) := {z | ∃ x ∈ V, x ∈ range (a z.1) ∧ x ∈ range (b z.2)}
  let M := ((P : Measure A).prod (P : Measure A)).prod ((Q : Measure B).prod (Q : Measure B))
  have hA (i : Fin 2) : ∀ᵐ z ∂M,
      a (pairSample i z.1) ⊥ ∉ V ∧ a (pairSample i z.1) ⊤ = p :=
    ((measurePreserving_pairSample (P : Measure A) i).comp
      measurePreserving_fst).quasiMeasurePreserving.ae ha
  have hB (i : Fin 2) : ∀ᵐ z ∂M,
      b (pairSample i z.2) ⊥ ∉ V ∧ b (pairSample i z.2) ⊤ = q :=
    ((measurePreserving_pairSample (Q : Measure B) i).comp
      measurePreserving_snd).quasiMeasurePreserving.ae hb
  apply four_sample_meeting_constraint (P : Measure A) (Q : Measure B)
    {z | E 0 (a z)} {z | E 2 (a z)} {z | E 1 (b z)} {z | E 3 (b z)} R
    (1 / 10) (((P : Measure A).prod (Q : Measure B)) R) ha0 ha2 hb1 hb3 _ le_rfl
  filter_upwards [hA 0, hA 1, hB 0, hB 1] with z hA0 hA1 hB0 hB1 hz
  simp only [pairSample, Fin.isValue, ite_true, one_ne_zero, ite_false] at hA0 hA1 hB0 hB1
  let γ : Fin 4 → C(PathTime, X) := ![a z.1.1, b z.2.1, a z.1.2, b z.2.2]
  have hγstart : ∀ i, γ i ⊥ ∉ V := by
    intro i
    fin_cases i
    · exact hA0.1
    · exact hB0.1
    · exact hA1.1
    · exact hB1.1
  have hγend : ∀ i, γ i ⊤ ∈ V := by
    intro i
    fin_cases i
    · exact hA0.2 ▸ hp
    · exact hB0.2 ▸ hq
    · exact hA1.2 ▸ hp
    · exact hB1.2 ▸ hq
  let θ : Fin 4 → UnitAddCircle := fun i => χ (γ i (lastEntryTime (γ i) V))
  have hθarc : ∀ i, θ i ∈ rationalCircleArc (l i) (u i) := by
    intro i
    fin_cases i
    · exact hz.1.1
    · exact hz.2.1
    · exact hz.1.2
    · exact hz.2.2
  have hθorder : StrictMono (unitCircleCut ∘ θ) := by
    intro i j hij
    have hi := (hθarc i).2
    have hj := (hθarc j).1
    have hmid : (u i : ℝ) < (l j : ℝ) := by exact_mod_cast horder i j hij
    exact hi.trans (hmid.trans hj)
  obtain ⟨x, hxV, hxA, hxB⟩ := alternating_lastEntry_tails_intersect hcross V hV f
    hf hfinj hfdisk γ hγstart hγend (hA0.2.trans hA1.2.symm)
    (hB0.2.trans hB1.2.symm) θ hθorder
    (fun i => hχ _ (lastEntry_frontier (γ i) hV (hγstart i) (hγend i)))
  have htail (γ : C(PathTime, X)) : lastEntryTail γ V ⊆ range γ := image_subset_range _ _
  rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
  · exact ⟨0, 0, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨0, 1, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨1, 0, x, hxV, htail _ hxA, htail _ hxB⟩
  · exact ⟨1, 1, x, hxV, htail _ hxA, htail _ hxB⟩

end CircleDomainRigidity

end

end OAI
