import OAI.Probability.InvariantIsing.Spectral.SpectralPartitionIndex

namespace OAI

/-! A finite ball cover yields a measurable partition, including a
zero-mass residual cell outside the covered spectral support. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical Function

namespace InvariantIsing

def spectralBallCell {n : ℕ} (B : Fin n → Set ℝ) : Option (Fin n) → Set ℝ
  | none => (⋃ i, B i)ᶜ
  | some i => disjointed B i

lemma spectralBallCell_cover {n : ℕ} (B : Fin n → Set ℝ) (x : ℝ) :
    ∃ i, x∈spectralBallCell B i := by
  by_cases hx : x∈⋃ i, B i
  · rw [← iUnion_disjointed] at hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨some i,hi⟩
  · exact ⟨none,hx⟩

lemma spectralBallCell_disjoint {n : ℕ} (B : Fin n → Set ℝ) :
    Pairwise (Disjoint on spectralBallCell B) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hx (mem_iUnion.mpr ⟨j,disjointed_subset B j hy⟩)
  | some i =>
    cases j with
    | none =>
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hy (mem_iUnion.mpr ⟨i,disjointed_subset B i hx⟩)
    | some j => exact disjoint_disjointed B (fun h => hij (congrArg some h))

lemma spectralBallCell_measurable {n : ℕ} (B : Fin n → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (i : Option (Fin n)) :
    MeasurableSet (spectralBallCell B i) := by
  cases i with
  | none => exact (MeasurableSet.iUnion hB).compl
  | some i =>
    rw [spectralBallCell,disjointed_apply,Finset.sup_eq_iSup]
    exact (hB i).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hB j)

lemma spectralBallCell_null_boundary {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (hB : ∀ i, μ (frontier (B i))=0) (i : Option (Fin n)) :
    μ (frontier (spectralBallCell B i))=0 := by
  cases i with
  | none =>
    change μ (frontier (⋃ i, B i)ᶜ)=0
    rw [frontier_compl]
    simpa only [Finset.mem_univ,iUnion_true] using
      null_frontier_finsetUnion μ Finset.univ B (fun i _ => hB i)
  | some i => exact null_frontier_disjointed μ B hB i

lemma spectralBallCell_residual_null {n : ℕ} (μ : Measure ℝ) (B : Fin n → Set ℝ)
    (K : Set ℝ) (hμ : μ Kᶜ=0) (hcover : K ⊆ ⋃ i, B i) :
    μ (spectralBallCell B none)=0 :=
  measure_mono_null (compl_subset_compl.mpr hcover) hμ

end InvariantIsing

end

end OAI
