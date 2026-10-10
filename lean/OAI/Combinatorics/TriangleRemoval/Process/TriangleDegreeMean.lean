import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift

namespace OAI

section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma triangles_delete_eq_sdiff_hitting {n : ℕ} (G : Graph n) (t : Finset (Fin n)) :
    triangles (G \ t.powersetCard 2) = triangles G \ hittingTriangles G (t.powersetCard 2) := by
  ext u
  simp only [mem_triangles, hittingTriangles, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hu,hs⟩
    refine ⟨⟨hu, fun e he => (Finset.mem_sdiff.mp (hs he)).1⟩, ?_⟩
    rintro ⟨_,hd⟩
    apply hd
    apply Finset.disjoint_left.mpr
    intro e het heu
    exact (Finset.mem_sdiff.mp (hs heu)).2 het
  · rintro ⟨⟨hu,hs⟩,hn⟩
    refine ⟨hu, ?_⟩
    intro e he
    refine Finset.mem_sdiff.mpr ⟨hs he, ?_⟩
    intro het
    apply hn
    refine ⟨⟨hu,hs⟩, ?_⟩
    exact fun hd => Finset.disjoint_left.mp hd het he

lemma triangle_edge_inter_card_le_one {n : ℕ} {G : Graph n}
    {t u : Finset (Fin n)} (ht : t ∈ triangles G) (hu : u ∈ triangles G)
    (hne : t ≠ u) : (t.powersetCard 2 ∩ u.powersetCard 2).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  apply hne
  have he' := Finset.mem_inter.mp he
  have hf' := Finset.mem_inter.mp hf
  exact triangle_eq_of_two_edges (mem_triangles.mp ht).1 (mem_triangles.mp hu).1
    (Finset.mem_powersetCard.mp he'.1).2 (Finset.mem_powersetCard.mp hf'.1).2 hef
    (Finset.mem_powersetCard.mp he'.1).1 (Finset.mem_powersetCard.mp hf'.1).1
    (Finset.mem_powersetCard.mp he'.2).1 (Finset.mem_powersetCard.mp hf'.2).1

lemma triangle_incidence_swap {n : ℕ} (G : Graph n) (f : Finset (Fin n) → ℝ) :
    (∑ t ∈ triangles G, ∑ e ∈ t.powersetCard 2, f e) =
      ∑ e ∈ G, (triangleDegree G e : ℝ) * f e := by
  classical
  calc
    _ = ∑ t ∈ triangles G, ∑ e ∈ G, if e ∈ t.powersetCard 2 then f e else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      exact ⟨fun he => ⟨(mem_triangles.mp ht).2 he,he⟩, fun he => he.2⟩
    _ = ∑ e ∈ G, ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then f e else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter]
      simp [triangleDegree, incidentTriangles, mul_comm]

lemma triangle_degree_sum {n : ℕ} (G : Graph n) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)) = 3 * (triangles G).card := by
  have h := triangle_incidence_swap G (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  calc
    _ = ∑ t ∈ triangles G, ((t.powersetCard 2).card : ℝ) := h.symm
    _ = ∑ _t ∈ triangles G, (3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [triangle_edge_card ht]
      norm_num
    _ = _ := by simp; ring

lemma triangle_incidence_sum_on {n : ℕ} (G F : Graph n) :
    (∑ e ∈ F, (triangleDegree G e : ℝ)) =
      ∑ t ∈ triangles G, ((F ∩ t.powersetCard 2).card : ℝ) := by
  classical
  have he (e : Finset (Fin n)) : (triangleDegree G e : ℝ) =
      ∑ t ∈ triangles G, if e ∈ t.powersetCard 2 then (1 : ℝ) else 0 := by
    simp [triangleDegree, incidentTriangles, Finset.sum_boole]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_boole]
  congr 1

lemma triangle_hit_multiplicity {n : ℕ} {G : Graph n} {t u : Finset (Fin n)}
    (ht : t ∈ triangles G) (hu : u ∈ triangles G) :
    ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ) =
      (if u ∈ hittingTriangles G (t.powersetCard 2) then 1 else 0) +
      (if u = t then 2 else 0) := by
  classical
  by_cases hut : u = t
  · subst u
    have hhit : t ∈ hittingTriangles G (t.powersetCard 2) := by
      apply Finset.mem_filter.mpr
      refine ⟨ht, ?_⟩
      intro hd
      have hzero : t.powersetCard 2 = ∅ := disjoint_self.mp hd
      have hc := triangle_edge_card ht
      rw [hzero,Finset.card_empty] at hc
      omega
    norm_num [hhit, triangle_edge_card ht]
  · by_cases hhit : u ∈ hittingTriangles G (t.powersetCard 2)
    · have hnon : (t.powersetCard 2 ∩ u.powersetCard 2).Nonempty := by
        exact Finset.not_disjoint_iff_nonempty_inter.mp (Finset.mem_filter.mp hhit).2
      have hcard : (t.powersetCard 2 ∩ u.powersetCard 2).card = 1 := by
        exact Nat.le_antisymm (triangle_edge_inter_card_le_one ht hu (Ne.symm hut))
          (Finset.one_le_card.mpr hnon)
      simp [hhit,hut,hcard]
    · have hd : Disjoint (t.powersetCard 2) (u.powersetCard 2) := by
        by_contra hn
        exact hhit (Finset.mem_filter.mpr ⟨hu,hn⟩)
      simp [hhit,hut,Finset.disjoint_iff_inter_eq_empty.mp hd]

theorem triangle_hitting_card_exact {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((hittingTriangles G (t.powersetCard 2)).card : ℝ) =
      (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) - 2 := by
  classical
  rw [triangle_incidence_sum_on]
  have hm : (∑ u ∈ triangles G, ((t.powersetCard 2 ∩ u.powersetCard 2).card : ℝ)) =
      ((hittingTriangles G (t.powersetCard 2)).card : ℝ) + 2 := by
    calc
      _ = ∑ u ∈ triangles G,
          ((if u ∈ hittingTriangles G (t.powersetCard 2) then (1 : ℝ) else 0) +
          (if u = t then 2 else 0)) := by
        apply Finset.sum_congr rfl
        exact fun u hu => triangle_hit_multiplicity ht hu
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_boole,Finset.sum_ite_eq',ht,ite_true]
        have hf : (triangles G).filter (fun u => u ∈ hittingTriangles G (t.powersetCard 2)) =
            hittingTriangles G (t.powersetCard 2) := by
          ext u
          simp only [hittingTriangles,Finset.mem_filter]
          tauto
        rw [hf]
  linarith

theorem triangle_count_delete {n : ℕ} {G : Graph n} {t : Finset (Fin n)}
    (ht : t ∈ triangles G) :
    ((triangles (G \ t.powersetCard 2)).card : ℝ) =
      (triangles G).card - (∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) + 2 := by
  have hsub : hittingTriangles G (t.powersetCard 2) ⊆ triangles G := Finset.filter_subset _ _
  rw [triangles_delete_eq_sdiff_hitting,Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub), triangle_hitting_card_exact ht]
  ring

theorem step_mean_triangle_count {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - (∑ e ∈ G, (triangleDegree G e : ℝ)^2) /
        (triangles G).card + 2 := by
  classical
  rw [step_mean G _ hQ]
  have he : (∑ t ∈ triangles G, ((triangles (G \ t.powersetCard 2)).card : ℝ)) =
      (triangles G).card * ((triangles G).card + 2 : ℝ) -
      ∑ e ∈ G, (triangleDegree G e : ℝ)^2 := by
    calc
      _ = ∑ t ∈ triangles G, (((triangles G).card : ℝ) + 2 -
          ∑ e ∈ t.powersetCard 2, (triangleDegree G e : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [triangle_count_delete ht]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,triangle_incidence_swap]
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, pow_two]
        ring
  rw [he]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  field_simp
  ring

noncomputable def triangleDegreeMean {n : ℕ} (G : Graph n) : ℝ :=
  3 * (triangles G).card / G.card

noncomputable def triangleDegreeVariance {n : ℕ} (G : Graph n) : ℝ :=
  ∑ e ∈ G, ((triangleDegree G e : ℝ) - triangleDegreeMean G)^2

lemma triangleDegreeVariance_nonneg {n : ℕ} (G : Graph n) :
    0 ≤ triangleDegreeVariance G := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma triangleDegreeMean_mass {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (G.card : ℝ) * triangleDegreeMean G = 3 * (triangles G).card := by
  have hm : (G.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hG.card_pos
  unfold triangleDegreeMean
  field_simp

theorem triangle_degree_second_moment {n : ℕ} {G : Graph n} (hG : G.Nonempty) :
    (∑ e ∈ G, (triangleDegree G e : ℝ)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hv : triangleDegreeVariance G =
      (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
      2*triangleDegreeMean G*(∑ e ∈ G, (triangleDegree G e : ℝ)) +
      (G.card : ℝ)*(triangleDegreeMean G)^2 := by
    unfold triangleDegreeVariance
    calc
      _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 -
          2*triangleDegreeMean G*(triangleDegree G e : ℝ) + (triangleDegreeMean G)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
  rw [hlin, ← hm] at hv
  nlinarith only [hv]

lemma graph_nonempty_of_triangles {n : ℕ} {G : Graph n} (hQ : (triangles G).Nonempty) :
    G.Nonempty := by
  obtain ⟨t,ht⟩ := hQ
  have hc := triangle_edge_card ht
  have he : (t.powersetCard 2).Nonempty := Finset.card_pos.mp (by omega)
  exact he.mono (mem_triangles.mp ht).2

theorem step_mean_triangle_count_centered {n : ℕ} {G : Graph n}
    (hQ : (triangles G).Nonempty) :
    pmfMean (step G) (fun H => ((triangles H).card : ℝ)) =
      (triangles G).card - 9*(triangles G).card / G.card -
      triangleDegreeVariance G / (triangles G).card + 2 := by
  rw [step_mean_triangle_count hQ, triangle_degree_second_moment (graph_nonempty_of_triangles hQ)]
  have hq : ((triangles G).card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ.card_pos
  have hm : (G.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (graph_nonempty_of_triangles hQ).card_pos
  unfold triangleDegreeMean
  field_simp
  ring

lemma triangle_degree_variance_shift {n : ℕ} {G : Graph n} (hG : G.Nonempty) (d : ℝ) :
    (∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2) =
      triangleDegreeVariance G + (G.card : ℝ)*(triangleDegreeMean G-d)^2 := by
  have hlin := triangle_degree_sum G
  have hm := triangleDegreeMean_mass hG
  have hsec := triangle_degree_second_moment hG
  calc
    _ = (∑ e ∈ G, (triangleDegree G e : ℝ)^2) -
        2*d*(∑ e ∈ G, (triangleDegree G e : ℝ))+(G.card : ℝ)*d^2 := by
      calc
        _ = ∑ e ∈ G, ((triangleDegree G e : ℝ)^2 - 2*d*(triangleDegree G e : ℝ) + d^2) := by
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
          Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    _ = _ := by rw [hsec,hlin,← hm]; ring

lemma triangle_degree_variance_le {n : ℕ} {G : Graph n} (hG : G.Nonempty)
    (d δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ e ∈ G, |(triangleDegree G e : ℝ)-d| ≤ δ) :
    triangleDegreeVariance G ≤ (G.card : ℝ)*δ^2 := by
  have hv : triangleDegreeVariance G ≤ ∑ e ∈ G, ((triangleDegree G e : ℝ)-d)^2 := by
    rw [triangle_degree_variance_shift hG d]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  apply hv.trans
  calc
    _ ≤ ∑ _e ∈ G, δ^2 := by
      apply Finset.sum_le_sum
      intro e he
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ).mpr (h e he)
    _ = _ := by simp

end SharpTerminalLeave
end

end OAI
