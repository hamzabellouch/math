import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Model
import OAI.Computability.PerfectCompleteness.Reduction.Target

namespace OAI

section

namespace PerfectCompleteness

namespace Instance

theorem countSatisfied_le_maxSatisfied {q : Nat} (G : Instance q) (s : Labeling G) :
    countSatisfied s.1 s.2 G.edges ≤ G.maxSatisfied := by
  exact Finset.le_sup (f := fun s : Labeling G => countSatisfied s.1 s.2 G.edges)
    (Finset.mem_univ s)

theorem maxSatisfied_le_length {q : Nat} (G : Instance q) :
    G.maxSatisfied ≤ G.edges.length := by
  apply Finset.sup_le
  intro s _
  exact countSatisfied_le_length s.1 s.2 G.edges

theorem maxSatisfied_attained {q : Nat} (G : Instance q) (hq : 0 < q) :
    ∃ s : Labeling G, countSatisfied s.1 s.2 G.edges = G.maxSatisfied := by
  have hne : (Finset.univ : Finset (Labeling G)).Nonempty :=
    ⟨(fun _ => ⟨0, by omega⟩, fun _ => ⟨0, hq⟩), Finset.mem_univ _⟩
  obtain ⟨s, _, h⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun s : Labeling G => countSatisfied s.1 s.2 G.edges)
  exact ⟨s, h.symm⟩

theorem value_nonneg {q : Nat} (G : Instance q) : 0 ≤ G.value :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem value_le_one {q : Nat} (G : Instance q) : G.value ≤ 1 := by
  have hlen : (0 : ℝ) < G.edges.length := by exact_mod_cast G.edgeCount_positive
  rw [value, div_le_iff₀ hlen, one_mul]
  exact_mod_cast G.maxSatisfied_le_length

theorem rate_le_value {q : Nat} (G : Instance q) (s : Labeling G) :
    (countSatisfied s.1 s.2 G.edges : ℝ) / G.edges.length ≤ G.value := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast G.countSatisfied_le_maxSatisfied s
  · exact Nat.cast_nonneg _

theorem perfectlyComplete_iff_value_eq_one {q : Nat} (G : Instance q) (hq : 0 < q) :
    PerfectlyComplete G ↔ G.value = 1 := by
  have hlen : (0 : ℝ) < G.edges.length := by exact_mod_cast G.edgeCount_positive
  constructor
  · rintro ⟨s, hs⟩
    have hc := (countSatisfied_eq_length_iff s.1 s.2 G.edges).2 hs
    have hm : G.maxSatisfied = G.edges.length :=
      le_antisymm G.maxSatisfied_le_length (hc ▸ G.countSatisfied_le_maxSatisfied s)
    simp [value, hm, ne_of_gt hlen]
  · intro hv
    obtain ⟨s, hs⟩ := G.maxSatisfied_attained hq
    have hm : G.maxSatisfied = G.edges.length := by
      have hreal : (G.maxSatisfied : ℝ) = G.edges.length := by
        have := (div_eq_one_iff_eq (ne_of_gt hlen)).1 hv
        exact this
      exact_mod_cast hreal
    exact ⟨s, (countSatisfied_eq_length_iff s.1 s.2 G.edges).1 (hs.trans hm)⟩

theorem soundAt_iff_value_le {q : Nat} (G : Instance q) (hq : 0 < q)
    (d : RationalThreshold) :
    SoundAt d G ↔ G.value ≤ (d.numerator : ℝ) / d.denominator := by
  have hlen : (0 : ℝ) < G.edges.length := by exact_mod_cast G.edgeCount_positive
  have hd : (0 : ℝ) < d.denominator := by
    exact_mod_cast (lt_trans d.positive d.belowOne)
  have hrat : ∀ s : Labeling G,
      d.denominator * countSatisfied s.1 s.2 G.edges ≤ d.numerator * G.edges.length ↔
        (countSatisfied s.1 s.2 G.edges : ℝ) / G.edges.length ≤
          (d.numerator : ℝ) / d.denominator := by
    intro s
    rw [div_le_div_iff₀ hlen hd]
    norm_cast
    rw [Nat.mul_comm (countSatisfied _ _ _) d.denominator]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := G.maxSatisfied_attained hq
    have := (hrat s).1 (h s)
    simpa [value, hs] using this
  · intro h s
    exact (hrat s).2 ((G.rate_le_value s).trans h)

end Instance
end PerfectCompleteness

end

end OAI
