import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitSeparation
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingHorosphere

namespace OAI

/-!
# Horospherical support and leaf separation

The horospherical support property of EKL (2006), Lemma 4.4(1), together
with separation along a root orbit gives Lemma 4.4(2). The support
property follows from the root product theorem, Proposition 8.3 of
Einsiedler--Katok (2003).
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_horospherical_leaf_separation_of_root_support
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) μ]
    (hnot : ¬ ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0)
    (hsupport : ∀ x ∉ N, ∀ h : G (d + 1), RootHorosphereShape i j h →
      rightAction x h ∉ N → ∃ t : ℝ,
        rightAction x h = rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧ ∀ x ∉ M,
      ∀ h : G (d + 1), RootHorosphereShape i j h → rightAction x h ∉ M →
        intrinsicRootLeaf hij μ x = intrinsicRootLeaf hij μ (rightAction x h) →
        rightAction x h = x := by
  obtain ⟨E, hE, hEzero, hsep⟩ := exists_nullset_root_orbit_leaf_separation d hij μ hnot
  refine ⟨N ∪ E, hN.union hE, measure_union_null hNzero hEzero, ?_⟩
  intro x hx h hshape hy heq
  have hxN : x ∉ N := fun he => hx (Or.inl he)
  have hxE : x ∉ E := fun he => hx (Or.inr he)
  have hyN : rightAction x h ∉ N := fun he => hy (Or.inl he)
  have hyE : rightAction x h ∉ E := fun he => hy (Or.inr he)
  obtain ⟨t, ht⟩ := hsupport x hxN h hshape hyN
  have hzero := hsep x hxE t (by rwa [← ht]) (by rwa [← ht])
  simpa [hzero] using ht

end DukePrimeDegree

end

end OAI
