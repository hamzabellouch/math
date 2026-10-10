import OAI.Combinatorics.CliqueFree.MaxDegree

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeLog
open CliqueFreeIndependence.WeightedGraph

lemma sum_degrees_real {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ v, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

/-- The logarithmic independence bound for ordinary clique exclusion and the graph's own
average degree, with a constant uniform in graph size and average degree. -/
theorem logarithmic_independence_bound (r : ℕ) (hr : 4 ≤ r) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
        G.CliqueFree r → 2 ≤ averageDegree G →
        c * (Fintype.card V : ℝ) * Real.log (averageDegree G) / averageDegree G ≤
          (G.indepNum : ℝ) := by
  classical
  obtain ⟨B,hB,htri⟩ := exists_optimizer_triangle_bound.{0} (r-2)
  let D : ℝ := 3+3*B/2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1/(16*D),by positivity,?_⟩
  intro V _ G hf hd
  let d : ℝ := averageDegree G
  have hd2 : 2 ≤ d := hd
  have hdpos : 0 < d := by linarith
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    intro hn
    have hz : averageDegree G = 0 := by simp [averageDegree,hn]
    rw [hz] at hd
    norm_num at hd
  have hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ)*d := by
    rw [sum_degrees_real]
    dsimp [d, averageDegree]
    field_simp
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2*d
  have hAcard : (Fintype.card V : ℝ)/2 ≤ (Fintype.card (A : Set V) : ℝ) := by
    have he : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    rw [he]
    exact degree_cutoff_card G hdpos hsum
  have hk : r-2+2 = r := Nat.sub_add_cancel (by omega)
  have hfree : (G.induce (A : Set V)).CliqueFree (r-2+2) := by
    rw [hk]
    exact (G.cliqueFree_induce_iff _ _).2 hf.cliqueFreeOn
  have hdeg (v : (A : Set V)) : ((G.induce (A : Set V)).degree v : ℝ) ≤ 2*d := by
    have hv : (G.degree v : ℝ) ≤ 2*d := (mem_filter.1 v.property).2
    exact (Nat.cast_le.2 (degree_induce_le G A v)).trans hv
  have hmax := maximum_degree_independence (r-2) hB.le (by linarith : 3 ≤ 2*d)
    htri (G.induce (A : Set V)) hfree hdeg
  have hi : ((G.induce (A : Set V)).indepNum : ℝ) ≤ G.indepNum :=
    Nat.cast_le.2 (indepNum_induce_le G A)
  have hlog : Real.log d ≤ Real.log (2*d) :=
    Real.log_le_log hdpos (by linarith)
  have hlog0 : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hnum : (Fintype.card V : ℝ)*Real.log d/2 ≤
      (Fintype.card (A : Set V) : ℝ)*Real.log (2*d) := by
    have h1 := mul_le_mul_of_nonneg_right hAcard hlog0
    have h2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) (Fintype.card (A : Set V)))
    nlinarith
  have hden : 0 < 8*D*d := by positivity
  have hcompare := div_le_div_of_nonneg_right hnum hden.le
  change (Fintype.card (A : Set V) : ℝ)*Real.log (2*d)/(4*D*(2*d)) ≤ _ at hmax
  have heq : (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d =
      ((Fintype.card V : ℝ)*Real.log d/2)/(8*D*d) := by
    field_simp
    ring
  change (1/(16*D))*(Fintype.card V : ℝ)*Real.log d/d ≤ _
  rw [heq]
  apply hcompare.trans
  have hdeneq : 8*D*d = 4*D*(2*d) := by ring
  rw [hdeneq]
  exact hmax.trans hi

end CliqueFreeLog

end

end OAI
