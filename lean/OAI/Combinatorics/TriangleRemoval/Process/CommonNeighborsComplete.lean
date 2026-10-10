import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.EarlyDensity

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma commonNeighbors_complete {n : ℕ} (u v : Fin n) :
    commonNeighbors (completeGraph n) u v = Finset.univ \ {u,v} := by
  ext w
  simp only [mem_commonNeighbors,mem_completeGraph,Finset.mem_sdiff,
    Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and]
  by_cases hu : u = w <;> by_cases hv : v = w <;>
    simp [hu,hv,eq_comm]

lemma currentCodegree_complete {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    currentCodegree (completeGraph n) u v = n-2 := by
  rw [currentCodegree,commonNeighbors_complete]
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.card_pair huv]

theorem initial_normalized_codegree_error {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n) (huv : u ≠ v) :
    (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0-1 =
      -1/((n : ℝ)-1)^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  rw [currentCodegree_complete u v huv,Nat.cast_sub hn,Nat.cast_ofNat]
  unfold earlyTemplateScale earlyDensity
  simp only [Nat.cast_zero,mul_zero,zero_div,sub_zero,pow_one]
  field_simp
  ring

end SharpTerminalLeave

end

end OAI
