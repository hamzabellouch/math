import OAI.Probability.MatroidProphet.Maximum.Basic

namespace OAI

namespace MatroidProphet.Maximum

open Finset

variable {n : ℕ}

lemma expectation_mem (q : Fin n → ℝ) (V : Finset (Fin n))
    (e : Fin n) (he : e ∈ V) (c : ℝ) :
    bitsExpectation q V (fun H => if e ∈ H then c else 0) = q e * c := by
  have hno : bitsExpectation q (V.erase e) (fun H => if e ∈ H then c else 0) = 0 := by
    calc
      _ = bitsExpectation q (V.erase e) (fun _ => 0) := by
        apply bitsExpectation_congr
        intro H hH
        have heH : e ∉ H := fun hh => (Finset.mem_erase.mp (hH hh)).1 rfl
        simp [heH]
      _ = 0 := bitsExpectation_const q _ 0
  have hyes : bitsExpectation q (V.erase e) (fun H => if e ∈ insert e H then c else 0) = c := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ c
  calc
    _ = bitsExpectation q (insert e (V.erase e)) (fun H => if e ∈ H then c else 0) := by
      rw [Finset.insert_erase he]
    _ = q e * c := by
      rw [bitsExpectation_insert q _ e (by simp), hno, hyes]
      ring

lemma expectation_top_two_event (V : Finset (Fin n)) (g h : Fin n)
    (hg : g ∈ V) (hh : h ∈ V) (hgh : g ≠ h) (c : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V
      (fun H => if g ∈ H then 0 else if h ∈ H then c else 0) = c / 4 := by
  let q : Fin n → ℝ := fun _ => 1 / 2
  have hno : bitsExpectation q (V.erase g)
      (fun H => if g ∈ H then 0 else if h ∈ H then c else 0) = (1 / 2 : ℝ) * c := by
    calc
      _ = bitsExpectation q (V.erase g) (fun H => if h ∈ H then c else 0) := by
        apply bitsExpectation_congr
        intro H hH
        have hgH : g ∉ H := fun hm => (Finset.mem_erase.mp (hH hm)).1 rfl
        simp [hgH]
      _ = _ := expectation_mem q (V.erase g) h (Finset.mem_erase.mpr ⟨hgh.symm, hh⟩) c
  have hyes : bitsExpectation q (V.erase g)
      (fun H => if g ∈ insert g H then 0 else if h ∈ insert g H then c else 0) = 0 := by
    simp only [Finset.mem_insert_self, ite_true]
    exact bitsExpectation_const q _ 0
  change bitsExpectation q V _ = _
  conv_lhs => rw [← Finset.insert_erase hg]
  rw [bitsExpectation_insert q _ g (by simp), hno, hyes]
  dsimp [q]
  ring

theorem maximum_expectation_two (V : Finset (Fin n)) (g h : Fin n)
    (hg : g ∈ V) (hh : h ∈ V) (hgh : g ≠ h)
    (F : Finset (Fin n) → ℝ) (c : ℝ)
    (hF : ∀ H ⊆ V, 0 ≤ F H)
    (hsuccess : ∀ H ⊆ V, g ∉ H → h ∈ H → c ≤ F H) :
    c / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
  rw [← expectation_top_two_event V g h hg hh hgh c]
  apply bitsExpectation_mono _ (fun _ => by norm_num) (fun _ => by norm_num)
  intro H hH
  split_ifs with hgH hhH
  · exact hF H hH
  · exact hsuccess H hH hgH hhH
  · exact hF H hH

theorem maximum_expectation_one (V : Finset (Fin n)) (g : Fin n) (hg : g ∈ V)
    (F : Finset (Fin n) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hF : ∀ H ⊆ V, 0 ≤ F H)
    (hsuccess : ∀ H ⊆ V, g ∉ H → c ≤ F H) :
    c / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
  have hhalf : c / 2 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) V F := by
    have hevent := Candidates.expectation_not_mem (fun _ => (1 / 2 : ℝ)) V g hg c
    have hevent' : bitsExpectation (fun _ => (1 / 2 : ℝ)) V
        (fun H => if g ∉ H then c else 0) = c / 2 := by
      rw [hevent]
      ring
    rw [← hevent']
    apply bitsExpectation_mono _ (fun _ => by norm_num) (fun _ => by norm_num)
    intro H hH
    by_cases hgH : g ∈ H
    · simpa only [hgH, not_true_eq_false, ite_false] using hF H hH
    · simpa only [hgH, not_false_eq_true, ite_true] using hsuccess H hH hgH
  linarith

end MatroidProphet.Maximum

end OAI
