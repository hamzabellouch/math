import Mathlib
import OAI.Combinatorics.KMedian.Probability.PushforwardLaw
import OAI.Combinatorics.KMedian.Sparse.SparseRescaledInner

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

def encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m) :
    Fin m → Finset (Fin n) :=
  fun j => univ.filter (fun i => G j i = SparseGridRounding.base (fun i => q i j) i + 1)

def decode (q : Fin n → Fin m → ℚ) (ξ : Fin m → Finset (Fin n)) :
    SparseCounts.Table n m :=
  fun j i => SparseGridRounding.base (fun i => q i j) i + if i ∈ ξ j then 1 else 0

theorem decode_encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m)
    (hG : ∀ j i, G j i = SparseGridRounding.base (fun i => q i j) i ∨
      G j i = SparseGridRounding.base (fun i => q i j) i + 1) :
    decode q (encode q G) = G := by
  funext j i
  rcases hG j i with h | h <;> simp [decode, encode, h]

noncomputable def law (q : Fin n → Fin m → ℚ) : FiniteLaw (Fin m → Finset (Fin n)) :=
  (SparseBundles.law q).realIndex.map
    (fun a => encode q (SparseBundles.law q).states[a.val])

theorem expectation (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (v : SparseCounts.Table n m → ℝ) :
    (law q).expect (fun ξ => v (decode q ξ)) =
      (SparseBundles.law q).realIndex.expect (fun a => v (SparseBundles.law q).states[a.val]) := by
  rw [law, FiniteLaw.expect_map]
  congr 1
  funext a
  rw [decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)]

theorem support (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (ξ : Fin m → Finset (Fin n)) (hξ : 0 < (law q).weight ξ) :
    ∃ a : Fin (SparseBundles.law q).length,
      0 < (SparseBundles.law q).realIndex.weight a ∧
      decode q ξ = (SparseBundles.law q).states[a.val] := by
  obtain ⟨a, ha, rfl⟩ := FiniteLaw.support_map _ _ ξ hξ
  exact ⟨a, ha, decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)⟩

theorem mean (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ)) = (q i j : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact ((SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ))).trans
    (congrArg (fun x : ℚ => (x : ℝ)) (SparseBundles.single q K (fun i j => (hq i j).1) hs i j))

theorem pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i h : Fin n) (j k : Fin m) (hh : i ≠ h ∨ j ≠ k) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ) * (decode q ξ k h : ℝ)) ≤
      (q i j : ℝ) * (q h k : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ) * (G k h : ℝ))]
  have he := (SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ) * (G k h : ℚ))
  simp only [Rat.cast_mul, Rat.cast_natCast] at he
  rw [he, ← Rat.cast_mul]
  apply Rat.cast_le.mpr
  by_cases hjk : j = k
  · subst k
    exact SparseBundles.same_pair q K (fun i j => (hq i j).1) hs i h j
      (hh.resolve_right (not_not.mpr rfl))
  · exact (SparseBundles.cross_pair q K (fun i j => (hq i j).1) hs i h j k hjk).le

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).variance (fun ξ => (decode q ξ j i : ℝ)) ≤ (q i j : ℝ) := by
  have hv := SparseBundles.variance q K L hq hs i j
  rw [FiniteLaw.variance_eq] at hv ⊢
  rw [expectation q K L hq hs (fun G => (G j i : ℝ)^2),
    expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact hv

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

noncomputable def encodedLaw (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) : FiniteLaw (Fin t → Finset (Fin n)) :=
  SparseBundleEncoding.law (piece P y p K)

def encodedCount (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (ξ : Fin t → Finset (Fin n)) (a : Fin t × Fin n) : ℕ :=
  SparseBundleEncoding.decode (piece P y p K) ξ a.1 a.2

theorem encoded_pieces (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (ξ : Fin t → Finset (Fin n))
    (hξ : 0 < (encodedLaw P y p K).weight ξ) : ∀ j,
      (∑ i, encodedCount P y p K ξ (j,i)) = K j ∧
      (∀ i, encodedCount P y p K ξ (j,i) ≤ Δ) ∧
      (∀ i, i ∉ P j → encodedCount P y p K ξ (j,i) = 0) := by
  obtain ⟨a, _, ha⟩ := SparseBundleEncoding.support (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) ξ hξ
  simp only [encodedCount, ha]
  exact invariants P y p K Δ hy hp hm hK a

theorem cast_scaled_piece (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (g : ℝ) (i : Fin n) (j : Fin t) :
    g * (piece P y p K i j : ℝ) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  simp only [piece, apply_ite, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zero]
  split_ifs <;> ring

theorem encoded_mean (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (j : Fin t) (i : Fin n) :
    (encodedLaw P y p K).expect (fun ξ => g * (encodedCount P y p K ξ (j,i) : ℝ)) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  rw [FiniteLaw.expect_mul]
  have h := SparseBundleEncoding.mean (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) i j
  change (encodedLaw P y p K).expect (fun ξ => (encodedCount P y p K ξ (j,i) : ℝ)) = _ at h
  rw [h, cast_scaled_piece]

theorem encoded_pair (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a b : Fin t × Fin n) (hab : a ≠ b) :
    (encodedLaw P y p K).expect (fun ξ =>
      (g * (encodedCount P y p K ξ a : ℝ)) * (g * (encodedCount P y p K ξ b : ℝ))) ≤
      (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) *
      (if b.2 ∈ P b.1 then (g * (K b.1 : ℝ)) * (y b.2 : ℝ) / (p b.1 : ℝ) else 0) := by
  have hne : a.2 ≠ b.2 ∨ a.1 ≠ b.1 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext h.2 h.1)
  have hh := SparseBundleEncoding.pair (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 b.2 a.1 b.1 hne
  have hf : ∀ x y : ℝ, (g*x)*(g*y) = g^2*(x*y) := by intros; ring
  rw [← cast_scaled_piece, ← cast_scaled_piece, hf]
  simp only [hf, FiniteLaw.expect_mul]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg g)

theorem encoded_variance (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a : Fin t × Fin n) :
    (encodedLaw P y p K).variance (fun ξ => g * (encodedCount P y p K ξ a : ℝ)) ≤
      g * (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) := by
  have hh := SparseBundleEncoding.variance (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 a.1
  change (encodedLaw P y p K).variance (fun ξ => (encodedCount P y p K ξ a : ℝ)) ≤ _ at hh
  rw [← cast_scaled_piece, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg g)

end MetricKMedian.SparseRescaledInner
end

end OAI
