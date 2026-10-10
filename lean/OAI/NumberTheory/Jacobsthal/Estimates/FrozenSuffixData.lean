import OAI.NumberTheory.Jacobsthal.Paths.ActualNearFullStopGroup

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.FrozenSuffixData
open PrimeHistories StoppedVertexHistory StoppedCountVertex ReferencePruning

theorem suffixPrimes_replacement (P : Finset ℕ) (pre tail : List ℕ) (p p' : ℕ)
    (htail : tail ≠ []) (hD : (pre++p::tail).Pairwise (· > ·))
    (hD' : (pre++p'::tail).Pairwise (· > ·)) :
    suffixPrimes P (pre++p::tail)=suffixPrimes P (pre++p'::tail) := by
  cases tail with
  | nil => exact False.elim (htail rfl)
  | cons u us =>
    have forward (p p' : ℕ) (hD' : (pre++p'::u::us).Pairwise (· > ·))
        (q : ℕ) (hA : ∀ r ∈ pre++p::u::us,q<r) : ∀ r ∈ pre++p'::u::us,q<r := by
      have hqu := hA u (by simp)
      have hup' := (List.pairwise_cons.mp (List.pairwise_append.mp hD').2.1).1 u (by simp)
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hA r (List.mem_append.mpr (Or.inl hr))
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hqu.trans hup'
        · exact hA r (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hr)))
    apply Finset.ext
    intro q
    simp only [suffixPrimes,Finset.mem_filter]
    exact and_congr_right (fun _ => ⟨forward p p' hD' q,forward p' p hD q⟩)

theorem after_available_replacement (w : ℝ) (v : Vertex) (pre tail : List ℕ) (p p' : ℕ)
    (htail : tail ≠ []) (hD : (pre++p::tail).Pairwise (· > ·))
    (hD' : (pre++p'::tail).Pairwise (· > ·)) :
    (after w v (pre++p::tail)).available=(after w v (pre++p'::tail)).available := by
  rw [after_available,after_available]
  exact suffixPrimes_replacement v.available pre tail p p' htail hD hD'

theorem terminal_suffix_cutoff (w : ℝ) (z z' : Node) (tail : List ℕ) (htail : tail ≠ []) :
    (terminal w z tail).cutoff=(terminal w z' tail).cutoff ∧
      (terminal w z tail).closed=false ∧ (terminal w z' tail).closed=false := by
  induction tail generalizing z z' with
  | nil => exact False.elim (htail rfl)
  | cons p ps ih =>
    cases ps with
    | nil => simp [terminal,step]
    | cons q qs => exact ih (step w z p) (step w z' p) (by simp)

theorem replacement_cutoff (w : ℝ) (z : Node) (pre tail : List ℕ) (p p' : ℕ) (htail : tail ≠ []) :
    (terminal w z (pre++p::tail)).cutoff=(terminal w z (pre++p'::tail)).cutoff ∧
      (terminal w z (pre++p::tail)).closed=false ∧
      (terminal w z (pre++p'::tail)).closed=false := by
  rw [show pre++p::tail=(pre++[p])++tail by simp,show pre++p'::tail=(pre++[p'])++tail by simp]
  rw [terminal_append w z (pre++[p]) tail,terminal_append w z (pre++[p']) tail]
  exact terminal_suffix_cutoff w _ _ tail htail
end NumberTheoryLean.FrozenSuffixData

end

end Erdos970

end OAI
