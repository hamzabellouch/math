import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section RootOverlap
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeFamilyDegree (G : Finset (Finset V)) (v : V) : ℕ :=
  (G.filter (fun e => v ∈ e)).card

theorem sum_edgeFamilyDegree (G : Finset (Finset V))
    (hG : ∀ e ∈ G, e.card = 2) : ∑ v, edgeFamilyDegree G v = 2 * G.card := by
  classical
  calc
    _ = ∑ v, ∑ e ∈ G, if v ∈ e then 1 else 0 := by
      simp only [edgeFamilyDegree, Finset.card_filter]
    _ = ∑ e ∈ G, ∑ v, if v ∈ e then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ G, e.card := by simp
    _ = _ := by simp only [Finset.sum_congr rfl hG, Finset.sum_const, smul_eq_mul, mul_comm]

theorem uniform_root_vertex (G : Finset (Finset V)) (hne : G.Nonempty) (v : V) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e => if v ∈ e then 1 else 0) =
      (edgeFamilyDegree G v : ℝ) / G.card := by
  rw [pmfMean_uniformOfFinset]
  congr 1
  simp [edgeFamilyDegree]

theorem uniform_root_pair_vertex (G : Finset (Finset V)) (hne : G.Nonempty) (v : V) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if v ∈ e ∧ v ∈ f then 1 else 0)) =
      (edgeFamilyDegree G v : ℝ) ^ 2 / (G.card : ℝ) ^ 2 := by
  have hi (e : Finset V) :
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if v ∈ e ∧ v ∈ f then 1 else 0) =
        (if v ∈ e then 1 else 0) * ((edgeFamilyDegree G v : ℝ) / G.card) := by
    by_cases he : v ∈ e
    · simpa [he] using uniform_root_vertex G hne v
    · simp [he]
  simp_rw [hi]
  rw [pmfMean_mul_const, uniform_root_vertex]
  ring

noncomputable def rootOverlap (G : Finset (Finset V)) (hne : G.Nonempty) : ℝ := by
  classical
  exact pmfMean (PMF.uniformOfFinset G hne) (fun e =>
    pmfMean (PMF.uniformOfFinset G hne) (fun f => if ¬Disjoint e f then 1 else 0))

theorem rootOverlap_le_degree_sum (G : Finset (Finset V)) (hne : G.Nonempty) :
    rootOverlap G hne ≤ (∑ v, (edgeFamilyDegree G v : ℝ) ^ 2) / (G.card : ℝ) ^ 2 := by
  classical
  have hpt (e f : Finset V) :
      (if ¬Disjoint e f then (1 : ℝ) else 0) ≤
        ∑ v : V, if v ∈ e ∧ v ∈ f then (1 : ℝ) else 0 := by
    by_cases h : Disjoint e f
    · simp only [h, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    · obtain ⟨v, hv, hv'⟩ := Finset.not_disjoint_iff.mp h
      simp only [h, not_false_eq_true, ite_true]
      have hh := Finset.single_le_sum (f := fun x => if x ∈ e ∧ x ∈ f then (1 : ℝ) else 0)
        (s := Finset.univ) (a := v) (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
      simpa only [hv, hv', and_self, ite_true] using hh
  calc
    rootOverlap G hne ≤ pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f =>
          ∑ v : V, if v ∈ e ∧ v ∈ f then (1 : ℝ) else 0)) := by
      apply pmfMean_mono
      intro e _
      apply pmfMean_mono
      intro f _
      exact hpt e f
    _ = _ := by
      simp_rw [pmfMean_sum]
      simp_rw [uniform_root_pair_vertex]
      exact (Finset.sum_div _ _ _).symm

theorem rootOverlap_le_maxDegree (G : Finset (Finset V)) (hne : G.Nonempty)
    (hG : ∀ e ∈ G, e.card = 2) (Δ : ℝ)
    (hΔ : ∀ v, (edgeFamilyDegree G v : ℝ) ≤ Δ) :
    rootOverlap G hne ≤ 2 * Δ / G.card := by
  have hm : (0 : ℝ) < G.card := Nat.cast_pos.mpr hne.card_pos
  have hd : (∑ v, (edgeFamilyDegree G v : ℝ)) = 2 * (G.card : ℝ) := by
    exact_mod_cast sum_edgeFamilyDegree G hG
  have hs : (∑ v, (edgeFamilyDegree G v : ℝ) ^ 2) ≤ Δ * (2 * (G.card : ℝ)) := by
    rw [← hd, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hΔ v) (show (0 : ℝ) ≤ edgeFamilyDegree G v by positivity)
  calc
    _ ≤ _ := rootOverlap_le_degree_sum G hne
    _ ≤ Δ * (2 * (G.card : ℝ)) / (G.card : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp

end RootOverlap
end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
