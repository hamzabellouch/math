import Mathlib
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization
import OAI.Combinatorics.ThinTrees.Metric.Profiles

namespace OAI

/-! Metric shell charging. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set StrongThinTree.Geometry

variable {V I : Type*} [Fintype V] [PseudoMetricSpace V]

def relativeBall (c : V → ℝ) (δ : ℝ) : Set (V → ℝ) :=
  {q | q ∈ polytope ∧ ‖q - c‖ < δ}

def relativeShell (c : V → ℝ) (a b : ℝ) : Set (V → ℝ) :=
  {q | q ∈ polytope ∧ a < ‖q - c‖ ∧ ‖q - c‖ < b}

omit [PseudoMetricSpace V] in
lemma radius_reverse_triangle (q r c : V → ℝ) :
    |‖r - c‖ - ‖q - c‖| ≤ ‖r - q‖ := by
  have h := abs_norm_sub_norm_le (r - c) (q - c)
  simpa only [sub_sub_sub_cancel_right] using h

theorem disjoint_relative_balls_iff {q r : V → ℝ}
    (hq : q ∈ polytope) (hr : r ∈ polytope) {δ : ℝ} :
    Disjoint (relativeBall q δ) (relativeBall r δ) ↔ 2 * δ ≤ ‖q - r‖ := by
  constructor
  · intro hdis
    by_contra h
    have hdist : ‖r - q‖ < 2 * δ := by
      rw [norm_sub_rev]
      exact lt_of_not_ge h
    have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hm := mix_mem hq hr ht
    have hl : ‖mix q r (1 / 2) - q‖ = 1 / 2 * ‖r - q‖ := by
      simpa only [mix_zero, sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        using segment_distance q r (1 / 2) 0
    have hr' : ‖mix q r (1 / 2) - r‖ = 1 / 2 * ‖r - q‖ := by
      have h := segment_distance q r (1 / 2) 1
      norm_num only [mix_one, show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num] at h
      exact h
    exact Set.disjoint_left.mp hdis ⟨hm, by rw [hl]; linarith⟩
      ⟨hm, by rw [hr']; linarith⟩
  · intro hdist
    apply Set.disjoint_left.mpr
    rintro s ⟨_, hs⟩ ⟨_, hs'⟩
    have h := dist_triangle q s r
    simp only [dist_eq_norm] at h
    rw [norm_sub_rev q s] at h
    linarith

theorem ball_shell_intersection_iff {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {a b δ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ commonRadius V) (hδ : 0 < δ) :
    (relativeBall q δ ∩ relativeShell (profile (plus x)) a b).Nonempty ↔
      a - δ < ‖q - profile (plus x)‖ ∧ ‖q - profile (plus x)‖ < b + δ := by
  constructor
  · rintro ⟨z, ⟨_, hzδ⟩, _, hza, hzb⟩
    have h := abs_sub_le_iff.mp (radius_reverse_triangle q z (profile (plus x)))
    constructor <;> linarith [h.1, h.2]
  · rintro ⟨ha', hb'⟩
    obtain ⟨z, hz, hzδ, hza, hzb⟩ := ball_intersects_shell hq x ha hab hb hδ ha' hb'
    exact ⟨z, ⟨hz, hzδ⟩, hz, hza, hzb⟩

theorem shell_segment_length_bound [Fintype I] (c : I → V) (a b : I → ℝ)
    (hab : ∀ i, a i ≤ b i)
    (hdis : Pairwise (fun i j => Disjoint
      (relativeShell (profile (c i)) (a i) (b i))
      (relativeShell (profile (c j)) (a j) (b j))))
    {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope) :
    ∑ i, |clamp (a i) (b i) ‖q - profile (c i)‖ -
      clamp (a i) (b i) ‖r - profile (c i)‖| ≤ ‖r - q‖ := by
  apply clamped_affine_disjoint_sum a b
    (fun i => ‖q - profile (c i)‖) (fun i => ‖r - profile (c i)‖)
    (norm_nonneg _) hab (fun i => radius_reverse_triangle q r (profile (c i)))
  rintro i j hij t ht ⟨hia, hib, hja, hjb⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hrad (s : V) : ‖mix q r t - profile s‖ =
      ‖q - profile s‖ + t * (‖r - profile s‖ - ‖q - profile s‖) := by
    rw [radius_mix hq hr s ht']
    ring
  apply Set.disjoint_left.mp (hdis hij) (mix_mem hq hr ht' |> fun hm =>
    show mix q r t ∈ relativeShell (profile (c i)) (a i) (b i) from
      ⟨hm, by rwa [hrad], by rwa [hrad]⟩)
  exact ⟨mix_mem hq hr ht', by rwa [hrad], by rwa [hrad]⟩

theorem shell_length_bound {n m k : ℕ} (G : StrongThinTree.MultiGraph n m)
    (hk : G.EdgeConnected k) (X : Fin n → V) [Fintype I]
    (c : I → V) (a b : I → ℝ) (hab : ∀ i, a i ≤ b i)
    (hinner : ∀ i, ∃ u, dist (X u) (c i) ≤ a i)
    (houter : ∀ i, ∃ v, b i ≤ dist (X v) (c i))
    (hdis : Pairwise (fun i j => Disjoint
      (relativeShell (profile (c i)) (a i) (b i))
      (relativeShell (profile (c j)) (a j) (b j)))) :
    (k : ℝ) * ∑ i, (b i - a i) ≤
      ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
  calc
    _ = ∑ i, (k : ℝ) * (b i - a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ∑ e : Fin m,
        |clamp (a i) (b i) (dist (X (G.left e)) (c i)) -
          clamp (a i) (b i) (dist (X (G.right e)) (c i))| := by
      exact Finset.sum_le_sum fun i _ => G.clamped_variation_lower hk
        (fun u => dist (X u) (c i)) (hab i) (hinner i) (houter i)
    _ = ∑ e : Fin m, ∑ i,
        |clamp (a i) (b i) (dist (X (G.left e)) (c i)) -
          clamp (a i) (b i) (dist (X (G.right e)) (c i))| := Finset.sum_comm
    _ ≤ ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
      apply Finset.sum_le_sum
      intro e _
      have h := shell_segment_length_bound c a b hab hdis
        (profile_mem (X (G.left e))) (profile_mem (X (G.right e)))
      simpa only [profile_norm_sub, dist_comm (X (G.right e)) (X (G.left e))] using h

theorem routed_shell_length_bound {n m : ℕ} (G : StrongThinTree.MultiGraph n m)
    (X : Fin n → V) [Fintype I] (c : I → V) (a b : I → ℝ)
    (R L : I → Finset (Fin n)) (q : ℝ)
    (hab : ∀ i, a i ≤ b i) (hconn : ∀ i, G.EdgeConnectedReal (R i) q)
    (hinner : ∀ i, ∃ u ∈ R i, u ∈ L i ∧ dist (X u) (c i) ≤ a i)
    (houter : ∀ i, ∃ v ∈ R i, b i ≤ dist (X v) (c i))
    (hprotect : ∀ i e, e ∈ G.inducedEdges (R i) →
      ((G.left e ∈ L i ∧ G.right e ∉ L i) ∨
        (G.right e ∈ L i ∧ G.left e ∉ L i)) →
      b i ≤ dist (X (G.left e)) (c i) ∧ b i ≤ dist (X (G.right e)) (c i))
    (hdis : ∀ i j, i ≠ j → ¬ Disjoint (L i) (L j) → Disjoint
      (relativeShell (profile (c i)) (a i) (b i))
      (relativeShell (profile (c j)) (a j) (b j))) :
    q * ∑ i, (b i - a i) ≤
      ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
  classical
  let f (i : I) (e : Fin m) : ℝ :=
    |clamp (a i) (b i) (dist (X (G.left e)) (c i)) -
      clamp (a i) (b i) (dist (X (G.right e)) (c i))|
  calc
    _ = ∑ i, q * (b i - a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i, ∑ e ∈ G.inducedEdges (L i), f i e := by
      apply Finset.sum_le_sum
      intro i _
      exact G.routed_variation_lower (fun u => dist (X u) (c i)) (hab i)
        (hconn i) (hinner i) (houter i) (hprotect i)
    _ = ∑ e : Fin m, ∑ i ∈ univ.filter (fun i => e ∈ G.inducedEdges (L i)), f i e := by
      simp only [StrongThinTree.MultiGraph.inducedEdges, Finset.sum_filter, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [Finset.sum_comm]
    _ ≤ ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
      apply Finset.sum_le_sum
      intro e _
      let W := univ.filter (fun i => e ∈ G.inducedEdges (L i))
      change ∑ i ∈ W, f i e ≤ _
      rw [← Finset.sum_coe_sort]
      have hdis' : Pairwise (fun i j : W => Disjoint
          (relativeShell (profile (c i)) (a i) (b i))
          (relativeShell (profile (c j)) (a j) (b j))) := by
        intro i j hij
        apply hdis i j (fun h => hij (Subtype.ext h))
        intro hL
        exact Finset.disjoint_left.mp hL
          ((G.mem_inducedEdges _ _).mp (mem_filter.mp i.property).2).1
          ((G.mem_inducedEdges _ _).mp (mem_filter.mp j.property).2).1
      have h := shell_segment_length_bound (fun i : W => c i)
        (fun i : W => a i) (fun i : W => b i) (fun i => hab i) hdis'
        (profile_mem (X (G.left e))) (profile_mem (X (G.right e)))
      simpa only [f, profile_norm_sub, dist_comm (X (G.right e)) (X (G.left e))] using h

theorem doubled_shell_length_bound {n m k : ℕ} (G : StrongThinTree.MultiGraph n m)
    (hk : G.EdgeConnected k) (X : Fin n → V) [Fintype I]
    (c : I → V) (a b : I → ℝ) (hab : ∀ i, a i ≤ b i)
    (hinner : ∀ i, ∃ u, dist (X u) (c i) ≤ a i)
    (houter : ∀ i, ∃ v, b i ≤ dist (X v) (c i))
    (hdis : Pairwise (fun i j => Disjoint
      (relativeShell (profile (plus (c i))) (a i) (b i))
      (relativeShell (profile (plus (c j))) (a j) (b j)))) :
    (k : ℝ) * ∑ i, (b i - a i) ≤
      ∑ e : Fin m, dist (X (G.left e)) (X (G.right e)) := by
  simpa only [dist_plus] using shell_length_bound G hk (fun u => plus (X u))
    (fun i => plus (c i)) a b hab (by simpa only [dist_plus])
    (by simpa only [dist_plus]) hdis

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
