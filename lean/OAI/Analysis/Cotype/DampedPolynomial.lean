import OAI.Analysis.Cotype.Damping

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def rowSupport (P : (ι × κ) → Bool) : Finset ι :=
  Finset.univ.filter (fun i => ∃ j, P (i,j) = true)

def columnSupport (P : (ι × κ) → Bool) : Finset κ :=
  Finset.univ.filter (fun j => ∃ i, P (i,j) = true)

def indexSize (P : (ι × κ) → Bool) : ℕ :=
  (Finset.univ.filter (fun ij => P ij = true)).card

theorem rowSupport_rectangle (s : Finset ι) (t : Finset κ) (ht : t.Nonempty) :
    rowSupport (rectangle s t) = s := by
  ext i
  simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    rectangle, decide_eq_true_eq]
  exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨ht.choose, hi, ht.choose_spec⟩⟩

theorem columnSupport_rectangle (s : Finset ι) (t : Finset κ) (hs : s.Nonempty) :
    columnSupport (rectangle s t) = t := by
  ext j
  simp only [columnSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    rectangle, decide_eq_true_eq]
  exact ⟨fun ⟨_, _, hj⟩ => hj, fun hj => ⟨hs.choose, hs.choose_spec, hj⟩⟩

theorem indexSize_rectangle (s : Finset ι) (t : Finset κ) :
    indexSize (rectangle s t) = s.card * t.card := by
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  simp only [indexSize, he, Finset.card_product]

def RankOneSupported (f : ((ι × κ) → Bool) → ℝ) : Prop :=
  ∀ P, fourier f P ≠ 0 → (binaryMatrix P).rank ≤ 1

def dampedPolynomial (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) : ℝ :=
  ∑ P, fourier f P * a ^ (rowSupport P).card * b ^ (columnSupport P).card * c ^ indexSize P

theorem dampedPolynomial_eq_expectation {f : ((ι × κ) → Bool) → ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (a b c : ℝ) :
    dampedPolynomial f a b c = dampedExpectation f a b c := by
  rw [dampedExpectation_fourier]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hz : fourier f P = 0
  · simp [hz]
  obtain ⟨s, t, hs, ht, he⟩ := odd_rank_one_support hf hz (hr P hz)
  have hsne : s.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := hs; omega)
  have htne : t.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := ht; omega)
  rw [← he, dampedExpectation_odd_rectangle s t hs ht,
    rowSupport_rectangle s t htne, columnSupport_rectangle s t hsne, indexSize_rectangle]
  ring

theorem dampedPolynomial_bound {f : ((ι × κ) → Bool) → ℝ} {M a b : ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (hM : ∀ S, |f S| ≤ M)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |dampedPolynomial f a b (1/2)| ≤ M := by
  rw [dampedPolynomial_eq_expectation hf hr]
  exact dampedExpectation_bound ha hb (by norm_num) hM

end Cotype

end

end OAI
