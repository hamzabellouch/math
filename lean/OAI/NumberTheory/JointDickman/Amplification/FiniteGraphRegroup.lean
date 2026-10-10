import OAI.NumberTheory.JointDickman.Amplification.ArithmeticOffDiagonalGraph

namespace OAI

/-! # Finite regrouping by graph lag and vertex -/

namespace JointDickman
open Finset

theorem finite_graph_regroup {ι κ ν : Type*} [DecidableEq κ] [DecidableEq ν]
    (s : Finset ι) (t : Finset κ) (v : Finset ν) (lag : ι → κ)
    (edge : ι → Finset ν) (w : ι → ν → ℝ) (h : κ → ν → ℝ)
    (hlag : ∀ i ∈ s, lag i ∈ t) (hedge : ∀ i ∈ s, edge i ⊆ v) :
    (∑ i ∈ s, ∑ n ∈ edge i, w i n * h (lag i) n) =
      ∑ n ∈ v, ∑ j ∈ t, (∑ i ∈ s, if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by
  symm
  simp_rw [sum_mul]
  calc
    _ = ∑ n ∈ v, ∑ i ∈ s, ∑ j ∈ t,
        (if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by
      apply sum_congr rfl
      intro n _
      rw [sum_comm]
    _ = ∑ i ∈ s, ∑ n ∈ v, ∑ j ∈ t,
        (if lag i = j ∧ n ∈ edge i then w i n else 0) * h j n := by rw [sum_comm]
    _ = ∑ i ∈ s, ∑ n ∈ v, if n ∈ edge i then w i n * h (lag i) n else 0 := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro n _
      by_cases hn : n ∈ edge i
      · simp only [hn,and_true,ite_mul,zero_mul]
        simp [hlag i hi]
      · simp [hn]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      calc
        _ = ∑ n ∈ edge i, if n ∈ edge i then w i n * h (lag i) n else 0 := by
          apply (sum_subset (hedge i hi) _).symm
          intro n _ hn
          simp [hn]
        _ = _ := sum_congr rfl (fun n hn => by simp [hn])

end JointDickman

end OAI
