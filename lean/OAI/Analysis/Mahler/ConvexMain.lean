import OAI.Analysis.Mahler.ConvexSequence

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {n : ℕ} {K : Set (Fin n → ℝ)}

lemma measurement_prefix_injective (c : ℝ) (hc : c ≠ 0)
    (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K) (a : ℕ → coordinatePolar K)
    (N : ℕ) :
    Function.Injective (measurement (fun j : Fin (n+N) => (prependPolarBasis c hcK a j).val)) := by
  intro x y h
  ext i
  have hi := congrFun h ⟨i.val, by omega⟩
  have hi' : c*x i = c*y i := by
    simpa [measurement, prependPolarBasis, i.isLt, Pi.single_apply] using hi
  exact mul_left_cancel₀ hc hi'

/-- An approximation certificate for an arbitrary symmetric convex body.
The sequence and every geometric and measure property are
constructed from exactly the body hypotheses; no approximation premise remains.
Each prefix has N+n rows and contains the
independent first n rows. -/
theorem exists_finite_strip_approximation (_hn : 1 ≤ n) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ∃ a : ℕ → coordinatePolar K,
      DenseRange a ∧
      LinearIndependent ℝ (fun i : Fin n => (a i).val) ∧
      (∀ N, Function.Injective (measurement (fun j : Fin (n+N) => (a j).val))) ∧
      (∀ N, IsCompact (stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        Convex ℝ (stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        (∀ x ∈ stripBody (fun j : Fin (n+N) => (a j).val),
          -x ∈ stripBody (fun j : Fin (n+N) => (a j).val)) ∧
        (interior (stripBody (fun j : Fin (n+N) => (a j).val))).Nonempty) ∧
      Antitone (fun N => stripBody (fun j : Fin (n+N) => (a j).val)) ∧
      (∀ N, K ⊆ stripBody (fun j : Fin (n+N) => (a j).val)) ∧
      (⋂ N, stripBody (fun j : Fin (n+N) => (a j).val)) = K ∧
      Tendsto (fun N => (volume (stripBody (fun j : Fin (n+N) => (a j).val))).toReal)
        atTop (𝓝 (volume K).toReal) ∧
      (∀ N, coordinatePolar (stripBody (fun j : Fin (n+N) => (a j).val)) ⊆ coordinatePolar K) := by
  have hz := zero_mem_interior_of_symmetric hconv hsym hint
  obtain ⟨c, hc, hcK⟩ := exists_coordinate_rows hK
  let : Nonempty (coordinatePolar K) := ⟨⟨0, zero_mem_coordinatePolar K⟩⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (coordinatePolar K)
  refine ⟨prependPolarBasis c hcK a, denseRange_prependPolarBasis c hcK a ha,
    linearIndependent_prependPolarBasis c hc.ne' hcK a,
    measurement_prefix_injective c hc.ne' hcK a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    rw [prefix_stripBody_eq]
    refine ⟨isCompact_approximation hc _ N, convex_stripBody _, symmetric_stripBody _, ?_⟩
    exact hint.mono (interior_mono (subset_approximation hsym c hcK a N))
  · simpa only [prefix_stripBody_eq] using approximation_antitone c (fun j => (a j).val)
  · intro N
    rw [prefix_stripBody_eq]
    exact subset_approximation hsym c hcK a N
  · simp only [prefix_stripBody_eq]
    exact iInter_approximation hconv hK.isClosed (interior_subset hz) hsym c hcK a ha
  · simp only [prefix_stripBody_eq]
    exact tendsto_volume_approximation hK hconv (interior_subset hz) hsym hc hcK a ha
  · intro N
    rw [prefix_stripBody_eq]
    exact coordinatePolar_antitone (subset_approximation hsym c hcK a N)

end SymmetricMahler

end OAI
