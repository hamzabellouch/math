import OAI.Combinatorics.CliqueFree.Deletion
import OAI.Combinatorics.CliqueFree.CrossBound
import OAI.Combinatorics.CliqueFree.TriangleBound

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma exists_optimizer_triangle_bound (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (w : V → ℝ),
      IsOptimizer G w → G.CliqueFree (k+2) → triangleMass G w ≤ B * edgeMass G w := by
  have hC : 1 ≤ 16*((k : ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨B,hB,hbound⟩ := weighted_triangles.{u} hC
  exact ⟨B,hB,fun G w hw hf ↦ hbound G w (fun v ↦ (optimizer_stationary hw v).1)
    (optimizer_cross_bound k G hw hf)⟩

lemma exists_cheap_vertex {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ B : ℝ} (hΔ : 3 ≤ Δ) (hB : 0 ≤ B)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (htri : triangleMass G w ≤ B * edgeMass G w) :
    ∃ v, mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w) ≤
      (3+3*B/2) * Real.log Δ := by
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hp (v : V) :
      w v * (mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w)) ≤
      w v + 2 * (w v * neighborMass G w v) + w v * triangleAt G w v / 2 := by
    rw [mass_closedNeighbors,edgeMass_closedNeighbors]
    have hv := (optimizer_stationary hw v).2.2
    have hN := neighborMass_nonneg G hw.1 v
    have hsq : w v * w v ≤ w v := by nlinarith [hw.1 v]
    have hmul := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  have hsum := sum_le_sum (s := univ) fun v _ ↦ hp v
  simp only [sum_add_distrib, ← mul_sum, ← sum_div] at hsum
  have he := edgeForm_self G w
  rw [edgeForm_neighbor] at he
  have ht : (∑ v, w v * triangleAt G w v) / 2 = 3*triangleMass G w := by
    unfold triangleMass
    ring
  rw [he,ht] at hsum
  have hedge := optimizer_edge_bound hw hΔ hdeg
  have hlog : 1 ≤ Real.log Δ := le_of_lt <| (Real.lt_log_iff_exp_lt (by linarith)).2
    (Real.exp_one_lt_three.trans_le hΔ)
  have hW : 0 ≤ ∑ v, w v := sum_nonneg (fun v _ ↦ hw.1 v)
  have htot : (∑ v, w v * (mass w (closedNeighbors G v) +
      edgeMass G (restrict (closedNeighbors G v) w))) ≤
        ((3+3*B/2)*Real.log Δ) * (∑ v, w v) := by
    have h1 := mul_le_mul_of_nonneg_right hlog hW
    have h2 := mul_le_mul_of_nonneg_left hedge (show 0 ≤ 2+3*B/2 by positivity)
    nlinarith
  by_contra h
  push Not at h
  have hlt (v : V) := mul_lt_mul_of_pos_left (h v) (hwpos v)
  have hh := sum_lt_sum (s := univ) (fun v _ ↦ (hlt v).le)
    ⟨Classical.arbitrary V, mem_univ _, hlt _⟩
  rw [← sum_mul] at hh
  linarith

lemma degree_induce_le (G : SimpleGraph V) (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (fun u : (G.induce (A : Set V)).neighborSet v ↦
      (⟨u.val.val, u.property⟩ : G.neighborSet v))
    (fun u z h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : G.neighborSet v ↦ (x : V)) h)

omit [Fintype V] in
lemma indepSet_image_induce (G : SimpleGraph V) (A : Finset V) (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set (A : Set V))) :
    G.IsIndepSet (I.map ⟨Subtype.val, Subtype.val_injective⟩ : Set V) := by
  classical
  intro a ha b hb hab
  obtain ⟨a',ha',rfl⟩ := mem_map.1 ha
  obtain ⟨b',hb',rfl⟩ := mem_map.1 hb
  exact hI ha' hb' (fun h ↦ hab (congrArg Subtype.val h))

omit [Fintype V] in
lemma indepSet_insert_induce (G : SimpleGraph V) (A : Finset V) (v : V)
    (hA : ∀ b ∈ A, b ≠ v ∧ ¬G.Adj v b)
    (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set _)) :
    G.IsIndepSet (↑(insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩) : Finset V) : Set V) ∧
      (insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩)).card = I.card + 1 := by
  classical
  have hnot (b : V) (hb : b ∈ I.map ⟨Subtype.val, Subtype.val_injective⟩) :
      b ≠ v ∧ ¬G.Adj v b := by
    obtain ⟨b',_,rfl⟩ := mem_map.1 hb
    exact hA b' b'.property
  have hi := indepSet_image_induce G A I hI
  constructor
  · intro a ha b hb hab
    change a ∈ insert v (I.map _) at ha
    change b ∈ insert v (I.map _) at hb
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact fun _ ↦ hab rfl
      · exact (hnot b hb).2
    · rcases hb with rfl | hb
      · exact fun h ↦ (hnot a ha).2 h.symm
      · exact hi ha hb hab
  · rw [card_insert_of_notMem (fun h ↦ (hnot v h).1 rfl), card_map]

/-- The maximum-degree induction controls the original variational functional,
not a surrogate objective or a conditional independence bound. -/
lemma maximum_degree_potential_bound (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
        potential G q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
  classical
  have aux : ∀ n : ℕ, ∀ (U : Type u) [Fintype U], Fintype.card U = n →
      ∀ H : SimpleGraph U, H.CliqueFree (k+2) → (∀ v, (H.degree v : ℝ) ≤ Δ) →
        ∃ I : Finset U, H.IsIndepSet (I : Set U) ∧
          ∀ q : U → ℝ, (∀ v, 0 ≤ q v) →
            potential H q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ hn H hfree hdegree
      rcases isEmpty_or_nonempty U with hU | hU
      · let _ := hU
        refine ⟨∅,by simp,?_⟩
        intro q _
        simp [potential,edgeMass,crossMass]
      · let _ := hU
        obtain ⟨w,hw⟩ := exists_optimizer H
        obtain ⟨v,hv⟩ := exists_cheap_vertex hw hΔ hB hdegree (htri H w hw hfree)
        let A : Finset U := (closedNeighbors H v)ᶜ
        have hA : ∀ b ∈ A, b ≠ v ∧ ¬H.Adj v b := by
          intro b hb
          simpa [A] using hb
        have hcard : Fintype.card (A : Set U) < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [A])
        have hfreeA : (H.induce (A : Set U)).CliqueFree (k+2) :=
          (H.cliqueFree_induce_iff _ _).2 hfree.cliqueFreeOn
        have hdegA (a : (A : Set U)) : ((H.induce (A : Set U)).degree a : ℝ) ≤ Δ :=
          (Nat.cast_le.2 (degree_induce_le H A a)).trans (hdegree a)
        obtain ⟨I,hI,hIp⟩ := ih _ hcard (A : Set U) rfl (H.induce (A : Set U)) hfreeA hdegA
        obtain ⟨hJ,hJcard⟩ := indepSet_insert_induce H A v hA I hI
        refine ⟨insert v (I.map ⟨Subtype.val,Subtype.val_injective⟩),hJ,?_⟩
        intro q hq
        have hres := hIp (fun a ↦ w a) (fun a ↦ hw.1 a)
        rw [potential_induce] at hres
        have hcost := optimizer_deletion_cost hw (closedNeighbors H v)
        change potential H w - potential H (restrict A w) = _ at hcost
        rw [hJcard,Nat.cast_add,Nat.cast_one]
        have hmax := hw.2 q hq
        nlinarith
  exact aux _ V rfl G hf hdeg

end CliqueFreeIndependence.WeightedGraph

end

end OAI
