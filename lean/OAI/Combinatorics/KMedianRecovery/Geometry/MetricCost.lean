import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CommonL

namespace OAI

namespace MetricKMedianRecovery.Rounding
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma metric_cost (u : ℝ) (hu : 0 < u) (C : ℕ) (hC : 0 < C) (D S : Finset V) :
    @LocalSearch.cost V (metric u hu C hC).toPseudoMetricSpace D S = (cost u C D S:ℝ) := by
  classical
  simp only [LocalSearch.cost,cost,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hS : S.Nonempty
  · simp only [LocalSearch.connection,connection,dite_eq_left hS]
    change S.inf' hS (fun i => (edge u C p i:ℝ)) = ((S.inf' hS (edge u C p):ℕ):ℝ)
    apply le_antisymm
    · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hS (edge u C p)
      rw [he]
      exact Finset.inf'_le _ hi
    · apply Finset.le_inf'
      intro i hi
      exact_mod_cast (Finset.inf'_le (edge u C p) hi)
  · simp only [LocalSearch.connection,connection,dite_eq_right hS,Nat.cast_zero]

omit [DecidableEq V] in

lemma largest_guess (D O F : Finset V) (hD : D.Nonempty) (hO : O.Nonempty)
    (hOF : O ⊆ F) (hP : 0 < LocalSearch.cost D O) :
    ∃ p ∈ D, ∃ f ∈ F, 0 < dist p f ∧ dist p f ≤ LocalSearch.cost D O ∧
      LocalSearch.cost D O ≤ D.card*dist p f := by
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image D (LocalSearch.connection O) hD
  let f := LocalSearch.nearest O hO p
  have hdf : dist p f = LocalSearch.connection O p := LocalSearch.nearest_distance O hO p
  have hupper : LocalSearch.cost D O ≤ D.card*dist p f := by
    calc
      _ ≤ ∑ _q ∈ D, LocalSearch.connection O p :=
        Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hdf]
  have hpos : 0 < dist p f := by
    by_contra hn
    have hh : D.card*dist p f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt hn)
    linarith
  refine ⟨p,hp,f,hOF (LocalSearch.nearest_mem O hO p),hpos,?_,hupper⟩
  rw [hdf]
  exact Finset.single_le_sum (fun q _ => LocalSearch.connection_nonneg O q) hp

end MetricKMedianRecovery.Rounding

end OAI
