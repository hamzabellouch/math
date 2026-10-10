import Mathlib
import OAI.Geometry.Borsuk.Simplicial.Approximation

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped Topology

lemma fineCrossMap_mesh (n r : ℕ) (c : Chain (cross n))
    {t : {s : Finset (EuclideanSpace ℝ (Fin n)) // s ∈ hemisphereComplex (n:ℝ)}}
    (ht : t ∈ (fineCrossMap n r c).support) :
    ∀ x ∈ t.val, ∀ y ∈ t.val, dist x y ≤ (((n:ℝ)-1)/n)^r * 2 := by
  obtain ⟨s,_,ht⟩ := support_linearMap (cross n) (hemisphereComplex (n:ℝ)) _ c ht
  exact fineCrossMap_simplex_mesh n r s.property ht

lemma cross_union_labels_mem {m : ℕ} [NeZero m] {V : Type*} [DecidableEq V]
    (s : Finset V) (hs : s.Nonempty) (f g : V → EuclideanSpace ℝ (Fin m))
    (hn : ∀ x ∈ s, ‖f x‖ = 1 ∧ ‖g x‖ = 1)
    (hclose : ∀ x ∈ s, ∀ y ∈ s,
      dist (f x) (f y) < (1:ℝ)/m ∧ dist (f x) (g y) < (1:ℝ)/m ∧
      dist (g x) (f y) < (1:ℝ)/m ∧ dist (g x) (g y) < (1:ℝ)/m) :
    s.image (fun x => sphereLabel (f x)) ∪ s.image (fun x => sphereLabel (g x)) ∈ cross m := by
  refine ⟨(hs.image _).mono Finset.subset_union_left, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;> exact sphereLabel_bound _
  · intro v hv w hw he
    rcases Finset.mem_union.mp hv with hf | hg <;>
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ‹_› <;>
      rcases Finset.mem_union.mp hw with hff | hgg <;>
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ‹_›
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).1 (hclose x hx y hy).1 he
    · exact sphereLabel_compatible _ _ (hn x hx).1 (hn y hy).2 (hclose x hx y hy).2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).1 (hclose x hx y hy).2.2.1 he
    · exact sphereLabel_compatible _ _ (hn x hx).2 (hn y hy).2 (hclose x hx y hy).2.2.2 he

lemma sphere_homotopy_chains (n m : ℕ) (hn : 0 < n) [NeZero m] (hmn : m ≤ n)
    (H : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hH : ContinuousOn H (Set.Icc (0:ℝ) 1 ×ˢ annulus n))
    (hHn : ∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ annulus n, ‖H p‖ = 1) :
    ∃ δ > 0, ∀ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ →
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      approximation n m r (fun x => sphereLabel (H (t,x))) (crossFundamental n) =
      approximation n m r (fun x => sphereLabel (H (u,x))) (crossFundamental n) := by
  classical
  have hcompact : IsCompact (Set.Icc (0:ℝ) 1 ×ˢ annulus n) := isCompact_Icc.prod (annulus_compact n)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hH) ((1:ℝ)/m)
      (div_pos zero_lt_one (by exact_mod_cast NeZero.pos m))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  let C : Set.Icc (0:ℝ) 1 → Chain (cross m) :=
    fun t => approximation n m r (fun x => sphereLabel (H (t.val,x))) (crossFundamental n)
  have hClocal : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq C).mpr
    intro t
    filter_upwards [Metric.ball_mem_nhds t hδ] with u hu
    apply approximation_agree_top n m r hn _ _ hmn
    intro s hs
    have hmesh := fineCrossMap_mesh n r (crossFundamental n) hs
    have ha : ∀ x ∈ s.val, x ∈ annulus n :=
      fun x hx => hemisphere_vertex_annulus n hn s.property hx
    have hh (v w : Set.Icc (0:ℝ) 1) (hv : dist v.val w.val < δ)
        (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ s.val)
        (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ s.val) :
        dist (H (v.val,x)) (H (w.val,y)) < (1:ℝ)/m := by
      apply hclose (v.val,x) ⟨v.property,ha x hx⟩ (w.val,y) ⟨w.property,ha y hy⟩
      rw [Prod.dist_eq]
      exact max_lt hv ((hmesh x hx y hy).trans_lt hr)
    have hut : dist u.val t.val < δ := hu
    have htu : dist t.val u.val < δ := by simpa only [dist_comm] using hut
    apply cross_union_labels_mem s.val s.property.1 _ _
    · intro x hx
      exact ⟨hHn (u.val,x) ⟨u.property,ha x hx⟩,hHn (t.val,x) ⟨t.property,ha x hx⟩⟩
    · intro x hx y hy
      exact ⟨hh u u (by simpa using hδ) x hx y hy,hh u t hut x hx y hy,
        hh t u htu x hx y hy,hh t t (by simpa using hδ) x hx y hy⟩
  let : PreconnectedSpace (Set.Icc (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  intro t ht u hu
  exact hClocal.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨u,hu⟩

lemma exists_small_cross_mesh (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℕ, (((n:ℝ)-1)/n)^r * 2 < δ := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hq : ((n:ℝ)-1)/n < 1 := (div_lt_one hn').mpr (by linarith)
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < δ/2 by linarith) hq
  exact ⟨r,by linarith⟩

end BorsukNine.SimplicialChains

end OAI
