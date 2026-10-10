import OAI.Probability.SwitchChain.TripleCountGram

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteCountTransport

variable {Ω β : Type*} [Fintype Ω] [Fintype β]

def average (f : Ω → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card Ω : ℝ)

def variance (f : Ω → ℝ) : ℝ :=
  average (fun x => (f x - average f) ^ 2)

def fiberProbability (q : Ω → β) (t : β) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun x => q x = t)).card : ℝ) /
    (Fintype.card Ω : ℝ)

theorem average_comp (q : Ω → β) (f : β → ℝ) :
    average (fun x => f (q x)) = ∑ t, fiberProbability q t * f t := by
  classical
  unfold average fiberProbability
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  calc
    (∑ x : Ω, f (q x)) = ∑ x : Ω, ∑ t : β, if q x = t then f t else 0 := by
      simp
    _ = ∑ t : β, ∑ x : Ω, if q x = t then f t else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      simp

theorem law_of_card_proportional {m : ℕ} (a : Fin 3 → ℕ)
    (q : Ω → TripleCountLaw.Triple m) (C : ℝ) (hC : C ≠ 0)
    (hcard : ∀ t, (Fintype.card {x : Ω // q x = t} : ℝ) =
      C * TripleCountLaw.weight a t) :
    ∀ t, fiberProbability q t = TripleCountLaw.probability a t := by
  classical
  have hmass : (Fintype.card Ω : ℝ) =
      ∑ t, ((Finset.univ.filter (fun x => q x = t)).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := q)
      (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ, Nat.cast_sum] using
      congrArg (fun z : ℕ => (z : ℝ)) h
  have hN : (Fintype.card Ω : ℝ) = C * TripleCountLaw.totalWeight a m := by
    rw [hmass]
    simp_rw [← Fintype.card_subtype, hcard]
    rw [← Finset.mul_sum]
    rfl
  intro t
  unfold fiberProbability TripleCountLaw.probability
  rw [← Fintype.card_subtype, hcard, hN]
  exact mul_div_mul_left _ _ hC

theorem average_eq_countExpectation {m : ℕ} (a : Fin 3 → ℕ)
    (q : Ω → TripleCountLaw.Triple m)
    (hlaw : ∀ t, fiberProbability q t = TripleCountLaw.probability a t)
    (f : TripleCountLaw.Triple m → ℝ) :
    average (fun x => f (q x)) = TripleCountLaw.countExpectation a f := by
  rw [average_comp]
  simp only [hlaw, TripleCountLaw.countExpectation]

theorem variance_eq_countVariance {m : ℕ} (a : Fin 3 → ℕ)
    (q : Ω → TripleCountLaw.Triple m)
    (hlaw : ∀ t, fiberProbability q t = TripleCountLaw.probability a t)
    (f : TripleCountLaw.Triple m → ℝ) :
    variance (fun x => f (q x)) = TripleCountLaw.countVariance a f := by
  unfold variance TripleCountLaw.countVariance
  rw [average_eq_countExpectation a q hlaw f]
  exact average_eq_countExpectation a q hlaw
    (fun t => (f t - TripleCountLaw.countExpectation a f) ^ 2)

theorem count_row_variance {m : ℕ} (a : Fin 3 → ℕ)
    (q : Ω → TripleCountLaw.Triple m)
    (hlaw : ∀ t, fiberProbability q t = TripleCountLaw.probability a t)
    (b : Fin 3 → Fin (m + 1) → ℝ) :
    variance (fun x => ∑ i : Fin 3, b i ((q x).val i)) ≤
      2 * ∑ i : Fin 3, variance (fun x => b i ((q x).val i)) := by
  rw [variance_eq_countVariance a q hlaw (fun t => ∑ i : Fin 3, b i (t.val i))]
  have heach (i : Fin 3) :=
    variance_eq_countVariance a q hlaw (fun t => b i (t.val i))
  simp_rw [heach]
  exact TripleCountLaw.count_variance_sum_le_two a m b

theorem count_row_variance_of_card_proportional {m : ℕ} (a : Fin 3 → ℕ)
    (q : Ω → TripleCountLaw.Triple m) (C : ℝ) (hC : C ≠ 0)
    (hcard : ∀ t, (Fintype.card {x : Ω // q x = t} : ℝ) =
      C * TripleCountLaw.weight a t)
    (b : Fin 3 → Fin (m + 1) → ℝ) :
    variance (fun x => ∑ i : Fin 3, b i ((q x).val i)) ≤
      2 * ∑ i : Fin 3, variance (fun x => b i ((q x).val i)) :=
  count_row_variance a q (law_of_card_proportional a q C hC hcard) b

end Problem315.FiniteCountTransport

end

end OAI
