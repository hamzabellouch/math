import Mathlib

namespace OAI

namespace FacetExposure

@[instance_reducible] noncomputable def graphMetric {V : Type*} (G : SimpleGraph V) (hG : G.Connected) :
    MetricSpace V where
  dist x y := (G.dist x y : ℝ)
  dist_self x := by simp
  dist_comm x y := by rw [G.dist_comm]
  dist_triangle x y z := by exact_mod_cast hG.dist_triangle
  eq_of_dist_eq_zero := by
    intro x y h
    exact hG.dist_eq_zero_iff.mp (by exact_mod_cast h)

theorem expose_edge {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (x y : V) (hxy : G.Adj x y) (hbridge : ¬G.IsBridge s(x,y))
    (β : ℝ) (hβ : 0 < β) (hβhalf : β < 1/2)
    (S : Set V) (hx : x ∈ S) (hy : y ∈ S) (a : V → ℝ)
    (ha : |a x - a y| = 1)
    (hslack : ∀ u ∈ S, ∀ v ∈ S, s(u,v) ≠ s(x,y) →
      |a u - a v| ≤ (1-β) * (G.dist u v : ℝ)) :
    ∃ g : V → ℝ, (∀ u ∈ S, g u = a u) ∧
      |g x - g y| = 1 ∧
      (∀ u v, G.Adj u v → s(u,v) ≠ s(x,y) → |g u - g v| ≤ 1-β) := by
  let H := G.deleteEdges {s(x,y)}
  have hH : H.Connected := hG.preconnected.connected_deleteEdges_of_not_isBridge hbridge
  let : MetricSpace V := graphMetric H hH
  let K : NNReal := ⟨1-β, by linarith⟩
  have hno : ¬H.Adj x y := by simp [H, SimpleGraph.deleteEdges_adj]
  have hdist : 2 ≤ H.dist x y := hH.one_lt_dist_of_ne_of_not_adj hxy.ne hno
  have hLip : LipschitzOnWith K a S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    change |a u - a v| ≤ (1-β) * (H.dist u v : ℝ)
    by_cases huv : s(u,v) = s(x,y)
    · rcases Sym2.eq_iff.mp huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rw [ha]
        have hd : (2 : ℝ) ≤ (H.dist u v : ℝ) := by exact_mod_cast hdist
        nlinarith
      · rw [abs_sub_comm, ha, H.dist_comm]
        have hd : (2 : ℝ) ≤ (H.dist v u : ℝ) := by exact_mod_cast hdist
        nlinarith
    · exact (hslack u hu v hv huv).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast ((hH u v).dist_anti
          (SimpleGraph.deleteEdges_le {s(x,y)}))) K.coe_nonneg)
  obtain ⟨g, hg, hga⟩ := hLip.extend_real
  refine ⟨g, fun u hu => (hga hu).symm, ?_, ?_⟩
  · rw [←hga hx, ←hga hy]
    exact ha
  · intro u v huv hne
    have huv' : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨huv, by simpa using hne⟩
    have hd := hg.dist_le_mul u v
    change |g u-g v| ≤ (1-β) * (H.dist u v : ℝ) at hd
    simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr huv', Nat.cast_one, mul_one] using hd

theorem expose_shell_edge {V : Type*} (G : SimpleGraph V) (hG : G.Connected)
    (x y : V) (hxy : G.Adj x y) (hbridge : ¬G.IsBridge s(x,y))
    (β : ℝ) (hβ : 0 < β) (hβhalf : β < 1/2)
    (S : Set V) (h : V → ℝ) (cx cy : ℝ)
    (hcx : x ∈ S → cx = h x) (hcy : y ∈ S → cy = h y)
    (hc : |cx-cy| = 1)
    (hss : ∀ u ∈ S, ∀ v ∈ S, |h u-h v| ≤ (1-β)*(G.dist u v : ℝ))
    (hxs : ∀ b ∈ S, b ≠ y → |cx-h b| ≤ (1-β)*(G.dist x b : ℝ))
    (hys : ∀ b ∈ S, b ≠ x → |cy-h b| ≤ (1-β)*(G.dist y b : ℝ)) :
    ∃ g : V → ℝ, (∀ b ∈ S, g b = h b) ∧ |g x-g y| = 1 ∧
      (∀ u v, G.Adj u v → s(u,v) ≠ s(x,y) → |g u-g v| ≤ 1-β) := by
  classical
  let a : V → ℝ := fun u => if u = x then cx else if u = y then cy else h u
  have hax : a x = cx := by simp [a]
  have hay : a y = cy := by simp [a,hxy.ne']
  have has : ∀ u ∈ S, a u = h u := by
    intro u hu
    by_cases hx : u = x
    · subst u; simpa [a] using hcx hu
    · by_cases hy : u = y
      · subst u; simpa [a,hx] using hcy hu
      · simp [a,hx,hy]
  have hslack : ∀ u ∈ insert x (insert y S), ∀ v ∈ insert x (insert y S),
      s(u,v) ≠ s(x,y) → |a u-a v| ≤ (1-β)*(G.dist u v : ℝ) := by
    intro u hu v hv hne
    simp only [Set.mem_insert_iff] at hu hv
    rcases hu with rfl | rfl | hu
    · rcases hv with rfl | rfl | hv
      · simp
      · exact False.elim (hne rfl)
      · rw [hax,has v hv]
        exact hxs v hv (by intro h; subst v; exact hne rfl)
    · rcases hv with rfl | rfl | hv
      · exact False.elim (hne (Sym2.eq_swap))
      · simp
      · rw [hay,has v hv]
        exact hys v hv (by intro h; subst v; exact hne (Sym2.eq_swap))
    · rcases hv with rfl | rfl | hv
      · rw [has u hu,hax,abs_sub_comm,G.dist_comm]
        exact hxs u hu (by intro h; subst u; exact hne (Sym2.eq_swap))
      · rw [has u hu,hay,abs_sub_comm,G.dist_comm]
        exact hys u hu (by intro h; subst u; exact hne rfl)
      · rw [has u hu,has v hv]
        exact hss u hu v hv
  obtain ⟨g,hg,he,hs⟩ := expose_edge G hG x y hxy hbridge β hβ hβhalf
    (insert x (insert y S)) (by simp) (by simp) a (by rw [hax,hay]; exact hc) hslack
  refine ⟨g,?_,he,hs⟩
  intro b hb
  exact (hg b (by simp [hb])).trans (has b hb)

lemma not_bridge_of_triangle {V : Type*} {G : SimpleGraph V} {x y z : V}
    (hxz : G.Adj x z) (hzy : G.Adj z y) (hxy : x ≠ y) :
    ¬G.IsBridge s(x,y) := by
  rw [SimpleGraph.isBridge_iff, not_not]
  have ha : (G.deleteEdges {s(x,y)}).Adj x z := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hxz, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨_,h⟩ | ⟨h,_⟩)
    · exact hzy.ne h
    · exact hxy h
  have hb : (G.deleteEdges {s(x,y)}).Adj z y := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨hzy, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨h,_⟩ | ⟨_,h⟩)
    · exact hxz.ne h.symm
    · exact hxy h.symm
  exact ha.reachable.trans hb.reachable

end FacetExposure

end OAI
