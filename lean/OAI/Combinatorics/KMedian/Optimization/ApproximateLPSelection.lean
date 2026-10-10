import Mathlib
import OAI.Combinatorics.KMedian.Optimization.IntegralFractionalComparison
import OAI.Combinatorics.KMedian.Optimization.MatrixNormalization
import OAI.Combinatorics.KMedian.Optimization.RationalArgmin

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

def FractionalData.Valid (out : FractionalData n m) (k : ℕ) : Prop :=
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1

instance (out : FractionalData n m) (k : ℕ) : Decidable (out.Valid k) :=
  by unfold FractionalData.Valid; infer_instance

def FractionalData.value (out : FractionalData n m) (d : Fin m → Fin n → ℚ) : ℚ :=
  ∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i

def scaledCandidate (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) (B : ℚ) : FractionalData n m :=
  if hB : 0 < B then
    approximation (fun j i => d j i/B) r k hr hk (fun j i => div_nonneg (hd j i) hB.le)
  else ⟨Vector.replicate n 0,Vector.replicate m (Vector.replicate n 0)⟩

def feasibleScales (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : Finset ℚ :=
  (Normalization.matrixGuesses d).filter
    (fun B => (scaledCandidate d r k hr hk hd B).Valid k)

def selectFractional (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  scaledCandidate d r k hr hk hd
    (rationalArgmin (feasibleScales d r k hr hk hd)
      (fun B => (scaledCandidate d r k hr hk hd B).value d))

omit [NeZero n] [NeZero m] in
theorem value_div (out : FractionalData n m) (d : Fin m → Fin n → ℚ) (B : ℚ) :
    out.value (fun j i => d j i/B)=out.value d/B := by
  simp only [FractionalData.value,mul_div_assoc,sum_div]

theorem candidate_success (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    ∃ B ∈ feasibleScales d r k hr hk hd,
      (scaledCandidate d r k hr hk hd B).value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hBg,hB,hc0,hc1⟩ := Normalization.matrixGoodGuess d hd a hc
  have hh := approximation_integral (fun j i => d j i/B) r k hr hk
    (fun j i => div_nonneg (hd j i) hB.le) S hS hSk a ha
    (by simpa only [sum_div] using hc0) (by simpa only [sum_div] using hc1)
  have hv : (scaledCandidate d r k hr hk hd B).Valid k := by
    simp only [scaledCandidate,dite_eq_left hB,FractionalData.Valid]
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have hcand : (scaledCandidate d r k hr hk hd B).value (fun j i => d j i/B) ≤
      (1+3/(r:ℚ))*(∑ j, d j (a j)/B) := by
    simpa only [scaledCandidate,dite_eq_left hB,FractionalData.value] using hh.2.2.2.2
  refine ⟨B,mem_filter.mpr ⟨hBg,hv⟩,?_⟩
  rw [value_div,← sum_div,← mul_div_assoc] at hcand
  exact (div_le_div_iff_of_pos_right hB).mp hcand

theorem selectFractional_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card ≤ k)
    (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : 0 < ∑ j, d j (a j)) :
    let out := selectFractional d r k hr hk hd
    out.Valid k ∧ out.value d ≤ (1+3/(r:ℚ))*(∑ j, d j (a j)) := by
  obtain ⟨B,hB,hBc⟩ := candidate_success d r k hr hk hd S hS hSk a ha hc
  obtain ⟨hmem,hmin⟩ := rationalArgmin_spec (feasibleScales d r k hr hk hd)
    (fun B => (scaledCandidate d r k hr hk hd B).value d) ⟨B,hB⟩
  exact ⟨(mem_filter.mp hmem).2,(hmin B hB).trans hBc⟩

theorem feasibleScales_card (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) :
    (feasibleScales d r k hr hk hd).card ≤ m*n*(m.size+1) :=
  (card_filter_le _ _).trans (Normalization.matrixGuesses_card d)

end MetricKMedian.TruncatedLP
end
end

end OAI
