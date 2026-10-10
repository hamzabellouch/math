import OAI.Analysis.Mahler.ConvexCompletion
import Mathlib.LinearAlgebra.StdBasis

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {n : ℕ} {K : Set (Fin n → ℝ)}

def prependPolarBasis (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (j : ℕ) : coordinatePolar K :=
  if h : j < n then ⟨Pi.single ⟨j, h⟩ c, hcK ⟨j, h⟩⟩ else a (j-n)

lemma prependPolarBasis_first (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (i : Fin n) :
    (prependPolarBasis c hcK a i).val = Pi.single i c := by
  simp [prependPolarBasis, i.isLt]

lemma prependPolarBasis_tail (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (j : ℕ) :
    prependPolarBasis c hcK a (n+j) = a j := by
  simp [prependPolarBasis, show ¬n+j < n by omega]

lemma denseRange_prependPolarBasis (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (ha : DenseRange a) :
    DenseRange (prependPolarBasis c hcK a) := by
  apply ha.mono
  rintro p ⟨j, rfl⟩
  exact ⟨n+j, prependPolarBasis_tail c hcK a j⟩

/-- The first n terms of the sequence are linearly independent. -/
lemma linearIndependent_prependPolarBasis (c : ℝ) (hc : c ≠ 0)
    (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K) (a : ℕ → coordinatePolar K) :
    LinearIndependent ℝ (fun i : Fin n => (prependPolarBasis c hcK a i).val) := by
  simp only [prependPolarBasis_first]
  exact Pi.linearIndependent_single_of_ne_zero (fun _ => hc)

/-- The literal first n+N rows describe exactly the previously constructed compact approximants. -/
lemma prefix_stripBody_eq (c : ℝ) (hcK : ∀ i : Fin n, Pi.single i c ∈ coordinatePolar K)
    (a : ℕ → coordinatePolar K) (N : ℕ) :
    stripBody (fun j : Fin (n+N) => (prependPolarBasis c hcK a j).val) =
      stripBody (approximationRows c (fun j => (a j).val) N) := by
  ext x
  rw [stripBody_approximationRows_mem]
  constructor
  · intro hx
    constructor
    · intro i
      have h := hx ⟨i.val, by omega⟩
      change |∑ k, (prependPolarBasis c hcK a i.val).val k * x k| ≤ 1 at h
      simpa [prependPolarBasis_first, Pi.single_apply] using h
    · intro j hj
      have h := hx ⟨n+j, by omega⟩
      simpa only [measurement, prependPolarBasis_tail] using h
  · rintro ⟨hb, hs⟩ j
    by_cases hj : j.val < n
    · change |∑ k, (prependPolarBasis c hcK a j.val).val k*x k| ≤ 1
      simpa [prependPolarBasis, hj, Pi.single_apply] using hb ⟨j.val, hj⟩
    · have hnj : n ≤ j.val := by omega
      have he : j.val = n + (j.val-n) := by omega
      change |∑ k, (prependPolarBasis c hcK a j.val).val k*x k| ≤ 1
      rw [he, prependPolarBasis_tail]
      exact hs (j.val-n) (by omega)

/-- Dense sequence with independent first rows exists for every compact set;
no unproved polar-body theorem or density premise is supplied. -/
theorem exists_dense_polar_sequence (hK : IsCompact K) :
    ∃ a : ℕ → coordinatePolar K, DenseRange a ∧
      LinearIndependent ℝ (fun i : Fin n => (a i).val) := by
  obtain ⟨c, hc, hcK⟩ := exists_coordinate_rows hK
  let : Nonempty (coordinatePolar K) := ⟨⟨0, zero_mem_coordinatePolar K⟩⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (coordinatePolar K)
  exact ⟨prependPolarBasis c hcK a, denseRange_prependPolarBasis c hcK a ha,
    linearIndependent_prependPolarBasis c hc.ne' hcK a⟩

end SymmetricMahler

end OAI
