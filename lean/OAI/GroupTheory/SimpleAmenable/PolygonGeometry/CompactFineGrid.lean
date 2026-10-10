import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CompactFineGrid

def closedWindowBox (n : ℕ) (cell : Fin 2 → Fin n) : Set (ℝ × ℝ) :=
  {p | ∀ j, ordinary (windowCut n 0 (cell j).castSucc) ≤ realCoordinate p j ∧
    realCoordinate p j ≤ ordinary (windowCut n 0 (cell j).succ)}

theorem closedWindowBox_subset (n : ℕ) (cell : Fin 2 → Fin n) :
    closedWindowBox n cell ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  intro p hp
  have h (j : Fin 2) : realCoordinate p j ∈ Set.Icc (0:ℝ) 1 := by
    have hl := (windowCut_bounds n 0 (cell j).castSucc).1
    have hu := (windowCut_bounds n 0 (cell j).succ).2
    simp only [Int.cast_zero,zero_mul,map_zero,zero_add] at hl hu
    exact ⟨hl.trans (hp j).1,(hp j).2.trans hu⟩
  exact ⟨h 0,h 1⟩

theorem closedWindowBox_nonempty (n : ℕ) (cell : Fin 2 → Fin n) :
    (closedWindowBox n cell).Nonempty := by
  refine ⟨(ordinary (windowCut n 0 (cell 0).castSucc),
    ordinary (windowCut n 0 (cell 1).castSucc)),?_⟩
  intro j
  have he : realCoordinate
      (ordinary (windowCut n 0 (cell 0).castSucc),
       ordinary (windowCut n 0 (cell 1).castSucc)) j =
      ordinary (windowCut n 0 (cell j).castSucc) := by fin_cases j <;> rfl
  rw [he]
  exact ⟨le_rfl,(windowCut_strictMono n 0 (Fin.castSucc_lt_succ (i := cell j))).le⟩

theorem windowPlanarLift_zero {a : ℕ} (p : GenericSquare a) :
    windowPlanarLift (fun _ => 0) p=p.val := by
  apply Prod.ext
  · change p.val.1-⌊p.val.1-ordinary ((0:CutRing)*cutTau)⌋=p.val.1
    simp only [zero_mul,map_zero,sub_zero,Int.floor_eq_zero_iff.mpr p.property.1,Int.cast_zero]
  · change p.val.2-⌊p.val.2-ordinary ((0:CutRing)*cutTau)⌋=p.val.2
    simp only [zero_mul,map_zero,sub_zero,Int.floor_eq_zero_iff.mpr p.property.2.1,Int.cast_zero]

theorem windowRectangle_subset_closed {a : ℕ} (n : ℕ) (hn : 201 ≤ n)
    (cell : Fin 2 → Fin n) (p : GenericSquare a)
    (hp : p ∈ (windowRectangle a n (fun _ => 0) cell).val) :
    p.val ∈ closedWindowBox n cell := by
  intro j
  have h := (windowRectangle_mem n hn (fun _ => 0) cell p).mp hp j
  rw [windowPlanarLift_zero] at h
  exact ⟨h.1,h.2.le⟩

theorem compact_open_cover_fine_grid {ι : Type*}
    (O : ι → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 201 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      200/(n:ℝ) < ε ∧ ∀ cell : Fin 2 → Fin n, ∃ i,
        closedWindowBox n cell ⊆ O i := by
  obtain ⟨δ,hδ,hlocal⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc) hO hcover
  have hmin : 0 < min δ ε := lt_min hδ hε
  obtain ⟨N,hN⟩ := exists_nat_gt (200/min δ ε)
  refine ⟨max 201 N,le_max_left _ _,fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmesh : 200/(n:ℝ) < min δ ε := by
    rw [div_lt_iff₀ hnpos]
    have hNN : (N:ℝ) ≤ n := by exact_mod_cast hnN
    have hlt := (div_lt_iff₀ hmin).mp hN
    nlinarith
  refine ⟨hmesh.trans_le (min_le_right _ _),fun cell => ?_⟩
  obtain ⟨x,hx⟩ := closedWindowBox_nonempty n cell
  obtain ⟨i,hi⟩ := hlocal x (closedWindowBox_subset n cell hx)
  refine ⟨i,fun p hp => hi ?_⟩
  apply Metric.mem_ball.mpr
  exact (closedWindow_diameter n (fun _ => 0) cell p x hp hx).trans_lt
    (hmesh.trans_le (min_le_left _ _))

theorem compact_local_bounds_fine_grid {ι : Type*}
    (O : ι → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ N : ℕ, 201 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ cell : Fin 2 → Fin n, ∃ i,
        200/(n:ℝ) < ε i ∧ closedWindowBox n cell ⊆ O i := by
  classical
  obtain ⟨s,hs⟩ := (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover O hO hcover
  have hspos : s.Nonempty := by
    have hh := hs (show ((0,0) : ℝ × ℝ) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 from
      ⟨⟨le_rfl,by norm_num⟩,⟨le_rfl,by norm_num⟩⟩)
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hi,_⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi⟩
  obtain ⟨i₀,_,hi₀⟩ := s.exists_min_image ε hspos
  have hcov : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i : s, O i.val := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩
  obtain ⟨N,hN,hfine⟩ := compact_open_cover_fine_grid (fun i : s => O i.val)
    (fun i => hO i.val) hcov (ε i₀) (hε i₀)
  refine ⟨N,hN,fun n hn cell => ?_⟩
  obtain ⟨hmesh,hcells⟩ := hfine n hn
  obtain ⟨i,hi⟩ := hcells cell
  exact ⟨i.val,hmesh.trans_le (hi₀ i.val i.property),hi⟩

end CompactFineGrid

section SimultaneousConcurrentTemplates

theorem vertex_type_zero (D : ℕ) (hD : 0 < D) :
    ∃ t : VertexType D, vertexRepresentative D t=0 := by
  let f : Fin D := ⟨0,hD⟩
  refine ⟨((f,f),(f,f)),?_⟩
  simp [vertexRepresentative,finiteCutResidue,ordinary_apply,f]

theorem ordinary_pair_near (z : ℝ × ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : CutRing × CutRing, dist (ordinary u.1,ordinary u.2) z < ε := by
  obtain ⟨u,hu,hu'⟩ := exists_cut_between (x := z.1-ε) (y := z.1+ε) (by linarith)
  obtain ⟨v,hv,hv'⟩ := exists_cut_between (x := z.2-ε) (y := z.2+ε) (by linarith)
  refine ⟨(u,v),?_⟩
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem simultaneous_active_template {ι : Type*} (ha : 0 < a)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      dist (vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2)) z < C.epsilon/4 ∧
      ∀ i, cutForm a (j i) z=ordinary (c i) →
        integralCutForm a (j i) (u+C.anchors t (j i))=c i ∧
        dist (ordinary (u+C.anchors t (j i)).1,ordinary (u+C.anchors t (j i)).2)
          (vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2)) < C.epsilon := by
  classical
  have hε : 0 < C.epsilon/4 := by linarith [C.positive]
  by_cases htwo : ∃ i k, cutForm a (j i) z=ordinary (c i) ∧
      cutForm a (j k) z=ordinary (c k) ∧ j i≠j k
  · obtain ⟨i,k,hi,hk,hik⟩ := htwo
    obtain ⟨t,u,v,hz⟩ := all_intersections_finite_templates ha (j i) (j k) hik (c i) (c k) z hi hk
    refine ⟨t,(u,v),by simpa only [← hz,dist_self] using hε,fun e he => ?_⟩
    have hh := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec
      t (u,v) (j e) (c e) z hz he
    simpa only [hz] using hh
  obtain ⟨t,ht⟩ := vertex_type_zero (commonVertexDenominator a) (commonVertexDenominator_pos ha)
  by_cases hone : ∃ i, cutForm a (j i) z=ordinary (c i)
  · obtain ⟨i,hi⟩ := hone
    obtain ⟨u,hu,hclose⟩ := allowable_line_anchor a (j i) (c i) z hi hε
    have hcenter : (ordinary u.1,ordinary u.2)=
        vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2) := by simp only [ht,zero_add]
    refine ⟨t,u,by simpa only [ht,zero_add] using hclose,fun k hk => ?_⟩
    have hdir : j i=j k := by
      by_contra hn
      exact htwo ⟨i,k,hi,hk,hn⟩
    have hc : c i=c k := ordinary_injective (hi.symm.trans (hdir ▸ hk))
    have hline : cutForm a (j k) (ordinary u.1,ordinary u.2)=ordinary (c k) := by
      rw [cutForm_ordinary,← hdir,hu,hc]
    have hh := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec
      t u (j k) (c k) (ordinary u.1,ordinary u.2) hcenter hline
    simpa only [ht,zero_add] using hh
  · obtain ⟨u,hu⟩ := ordinary_pair_near z (C.epsilon/4) hε
    refine ⟨t,u,by simpa only [ht,zero_add] using hu,fun i hi => ?_⟩
    exact (hone ⟨i,hi⟩).elim

theorem simultaneous_active_neighborhood {ι : Type*} (ha : 0 < a)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      (∀ p : ℝ × ℝ, dist p z < C.epsilon/2 → ∀ k,
        ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate p k ∧
        realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      ∀ i, cutForm a (j i) z=ordinary (c i) →
        integralCutForm a (j i) (u+C.anchors t (j i))=c i ∧
        ∀ p : ℝ × ℝ,
          (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
            realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
          ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t (j i)) k)|<3*C.epsilon := by
  obtain ⟨t,u,hclose,hactive⟩ := C.simultaneous_active_template ha j c z
  refine ⟨t,u,?_,fun i hi => ⟨(hactive i hi).1,?_⟩⟩
  · intro p hp k
    apply (C.margins t).translated_inner u p ?_ k
    have htri := dist_triangle p z
      (vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2))
    rw [dist_comm z] at htri
    linarith [C.positive]
  · intro p hp k
    exact (C.margins t).translated_outer u (u+C.anchors t (j i)) p (hactive i hi).2 hp k

end ConcurrentGeometry
end SimultaneousConcurrentTemplates

end SimpleAmenable
end
end

end OAI
