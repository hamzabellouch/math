import OAI.NumberTheory.DukePrimeDegree.Dynamics.StrongReturnExclusion
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ExceptionalReturns

namespace OAI

/-!
# Exclusion of exceptional neutral return sets

A measurable set on which all sufficiently small neutral return lifts
centralize one root has measure zero. The recurrence strengthening makes
these lifts centralize both roots on each quotient chart; the neutral
ergodic decomposition then contradicts the arithmetic orbit obstruction.
This combines the needed directions of EKL (2006), Lemma 4.2,
Proposition 4.3, and Theorem 5.1, without assuming those results.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exceptional_neutral_return_set_null
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hexceptional : ∀ x ∈ K,
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ singleRootCentralizer hij) : μ K = 0 := by
  choose U hUo hxU R hR hinj using (local_uniform_chart_injective (n := d + 1))
  obtain ⟨S, hSc, hcover⟩ := countable_cover_nhds (fun x => (hUo x).mem_nhds (hxU x))
  have hchart (a : X (d + 1)) : μ (K ∩ U a) = 0 := by
    let q := min r (R a / 2)
    have hq : 0 < q := lt_min hr (half_pos (hR a))
    have hqR : q < R a := lt_of_le_of_lt (min_le_right _ _) (by linarith [hR a])
    have hstrong := ae_strong_returns_on_chart d hij μ hA (rootPairCentralizer hij)
      (fun b => (mem_singleRootCentralizer hij b.val).mpr
        ((mem_rootPairCentralizer hij b.val).mp b.property).1)
      (fun b t => rootPairCentralizer_commutes_contraction hij b.val b.property t)
      q (R a) hq.le hqR (U a) (hUo a).measurableSet (hinj a)
    apply strong_neutral_return_set_null_of_ae d hd hij μ hA
      (K ∩ U a) (hK.inter (hUo a).measurableSet) q hq
    filter_upwards [hstrong] with x hx
    intro hxK ell hell hn hyK g hg heq
    have hgr : g ∈ matrixBall (d + 1) r := fun b c =>
      lt_of_lt_of_le (hg b c) (min_le_left _ _)
    have hgC := hexceptional x hxK.1 ell hell hn hyK.1 g hgr heq
    exact hx hxK.2
      ⟨diagonalOneParameter ell hell 1, diagonal_mem_rootPairCentralizer hij ell hell hn 1⟩
      g hg hgC heq
  apply measure_mono_null (show K ⊆ ⋃ a ∈ S, K ∩ U a by
    intro x hx
    have hxcover : x ∈ ⋃ a ∈ S, U a := by rw [hcover]; trivial
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxcover
    exact mem_iUnion₂.mpr ⟨a, ha, hx, hxa⟩)
  exact (measure_biUnion_null_iff hSc).mpr fun a _ => hchart a

end DukePrimeDegree

end

end OAI
