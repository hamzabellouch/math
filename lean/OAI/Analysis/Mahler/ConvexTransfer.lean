import OAI.Analysis.Mahler.ConvexGeometry

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Continuity from above applies to the actual decreasing strip bodies. -/
theorem tendsto_volume_approximation {K : Set (I → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hzero : (0 : I → ℝ) ∈ K) (hsym : ∀ x ∈ K, -x ∈ K)
    {c : ℝ} (hc : 0 < c) (hcK : ∀ i, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    Tendsto (fun N => (volume (stripBody (approximationRows c (fun j => (a j).val) N))).toReal)
      atTop (𝓝 (volume K).toReal) := by
  have hlim := tendsto_measure_iInter_atTop (μ := (volume : Measure (I → ℝ)))
    (fun N => (isClosed_stripBody (approximationRows c (fun j => (a j).val) N)).measurableSet.nullMeasurableSet)
    (approximation_antitone c (fun j => (a j).val))
    ⟨0, (isCompact_approximation hc (fun j => (a j).val) 0).measure_ne_top⟩
  rw [iInter_approximation hconv hK.isClosed hzero hsym c hcK a ha] at hlim
  exact (ENNReal.tendsto_toReal hK.measure_ne_top).comp hlim

theorem arbitrary_body_bound_of_finite_strips {K : Set (I → ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) (C : ℝ)
    (hfinite : ∀ N (A : (I ⊕ Fin N) → I → ℝ), Function.Injective (measurement A) →
      C ≤ (volume (stripBody A)).toReal * (volume (coordinatePolar (stripBody A))).toReal) :
    C ≤ (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  have hz := zero_mem_interior_of_symmetric hconv hsym hint
  have hpol := isCompact_coordinatePolar hsym hz
  obtain ⟨c, hc, hcK⟩ := exists_coordinate_rows hK
  let : Nonempty (coordinatePolar K) := ⟨⟨0, zero_mem_coordinatePolar K⟩⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (coordinatePolar K)
  have hlim := tendsto_volume_approximation hK hconv (interior_subset hz) hsym hc hcK a ha
  apply ge_of_tendsto (hlim.mul_const (volume (coordinatePolar K)).toReal)
  apply Eventually.of_forall
  intro N
  have hsub := subset_approximation hsym c hcK a N
  have hmono : (volume (coordinatePolar (stripBody (approximationRows c (fun j => (a j).val) N)))).toReal
      ≤ (volume (coordinatePolar K)).toReal :=
    ENNReal.toReal_mono hpol.measure_ne_top (measure_mono (coordinatePolar_antitone hsub))
  exact (hfinite N _ (approximationRows_injective c hc.ne' _ N)).trans
    (mul_le_mul_of_nonneg_left hmono ENNReal.toReal_nonneg)

end SymmetricMahler

end OAI
