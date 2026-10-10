import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.RectangularAtlas
import OAI.GroupTheory.SimpleAmenable.Homology.UniformConcurrentMesh
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.VertexMargins

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentGeometry

structure ConcurrentGeometryData (a D : ℕ) (r : CutRing) where
  epsilon : ℝ
  positive : 0<epsilon
  radius : 100*epsilon ≤ ordinary r
  first_gap : 100*epsilon ≤ Real.goldenRatio-1
  second_gap : 100*epsilon ≤ 2-Real.goldenRatio
  anchors : VertexType D → Fin 4 → CutRing × CutRing
  anchors_spec : ∀ t j, AllowableVertexLine a (vertexRepresentative D t) j →
    cutForm a j (vertexRepresentative D t)=
      ordinary (integralCutForm a j (anchors t j)) ∧
    dist (ordinary (anchors t j).1,ordinary (anchors t j).2)
      (vertexRepresentative D t)<epsilon
  margins : ∀ t : VertexType D,
    VertexMargin (vertexRepresentative D t) epsilon
  mesh : ℕ
  mesh_large : 201 ≤ mesh
  clipping : symmetricWindowLength r ≤ mesh
  mesh_fine : lineIntersectionConstant a*(200/(mesh:ℝ))<epsilon
  window : ℕ
  start : Fin 2 → ℤ
  labels : ∀ t j,
    (start j ≤ endpointLabel ((margins t).lower j) ∧
      endpointLabel ((margins t).lower j)<start j+window) ∧
    (start j ≤ endpointLabel ((margins t).upper j) ∧
      endpointLabel ((margins t).upper j)<start j+window)

abbrev ConcurrentGeometry (a : ℕ) (r : CutRing) :=
  ConcurrentGeometryData a (commonVertexDenominator a) r

theorem concurrentGeometry_exists (a : ℕ) (r : CutRing) (hr : 0<ordinary r) :
    Nonempty (ConcurrentGeometry a r) := by
  let ε := min (ordinary r) (min (Real.goldenRatio-1) (2-Real.goldenRatio))/100
  have hε : 0<ε := by
    apply div_pos
    · exact lt_min hr (lt_min (by linarith [Real.one_lt_goldenRatio])
        (by linarith [Real.goldenRatio_lt_two]))
    · norm_num
  have hr' : 100*ε ≤ ordinary r := by dsimp [ε]; linarith [min_le_left (ordinary r) (min (Real.goldenRatio-1) (2-Real.goldenRatio))]
  have hg : 100*ε ≤ Real.goldenRatio-1 := by
    have h := (min_le_right (ordinary r) (min (Real.goldenRatio-1) (2-Real.goldenRatio))).trans (min_le_left _ _)
    dsimp [ε]; linarith
  have hg' : 100*ε ≤ 2-Real.goldenRatio := by
    have h := (min_le_right (ordinary r) (min (Real.goldenRatio-1) (2-Real.goldenRatio))).trans (min_le_right _ _)
    dsimp [ε]; linarith
  obtain ⟨U,hU⟩ := finite_vertex_anchors a (commonVertexDenominator a) hε
  obtain ⟨V⟩ := finite_vertex_margins (commonVertexDenominator a) hε
  obtain ⟨N,hN⟩ := exists_nat_gt (200*lineIntersectionConstant a/ε)
  let n := max 201 (max N (symmetricWindowLength r))
  have hn : 201 ≤ n := le_max_left _ _
  have hNn : N ≤ n := (le_max_left _ _).trans (le_max_right _ _)
  have hn' : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hmesh : lineIntersectionConstant a*(200/(n:ℝ))<ε := by
    rw [← mul_div_assoc,div_lt_iff₀ hn']
    have h := (div_lt_iff₀ hε).mp hN
    have hcast : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hNn
    nlinarith
  let p (i : VertexType (commonVertexDenominator a) × Bool) (j : Fin 2) :=
    endpointLabel (if i.2 then (V i.1).upper j else (V i.1).lower j)
  obtain ⟨k,q,hq⟩ := finite_coordinate_windows_container (fun _ : VertexType (commonVertexDenominator a) × Bool => 1) p
  refine ⟨⟨ε,hε,hr',hg,hg',U,hU,V,n,hn,(le_max_right _ _).trans (le_max_right _ _),hmesh,k,q,?_⟩⟩
  intro t j
  have hL := hq (t,false) j
  have hV := hq (t,true) j
  simp only [p, Bool.false_eq_true, ↓reduceIte] at hL
  simp only [p, ↓reduceIte] at hV
  constructor <;> constructor <;> omega

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem mesh_small : 200/(C.mesh:ℝ)<C.epsilon := by
  have h := mul_le_mul_of_nonneg_right (lineIntersectionConstant_ge_one a)
    (show 0 ≤ 200/(C.mesh:ℝ) by positivity)
  simpa only [one_mul] using h.trans_lt C.mesh_fine

theorem margin_resolved (t : VertexType (commonVertexDenominator a)) :
    ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives C.window C.start) s).val)
      (coordinateRectangle a (C.margins t).lower (C.margins t).upper).val := by
  intro x y hxy
  exact and_congr
    (coordinateLabelWindow_resolved C.window C.start 0 _ _ (C.labels t 0).1 (C.labels t 0).2 x y hxy)
    (coordinateLabelWindow_resolved C.window C.start 1 _ _ (C.labels t 1).1 (C.labels t 1).2 x y hxy)

end ConcurrentGeometry

noncomputable def initialPatchPrimitives (r : CutRing) (n : ℕ) :
    Sum (Fin 5) (Fin 2 × Fin (n-1)) → Fin 5 × (CutRing × CutRing) :=
  Sum.elim (fun j => (j,0)) (coordinateWindowPrimitives n (symmetricWindowStart r))

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

structure PatchAtlas where
  rectangles : B.RectangularAtlas
  geometry : ConcurrentGeometry a r
  initial : ∀ u I b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (initialPatchPrimitives r geometry.mesh) u)
  concurrent : ∀ t u I b hb, B.PrimitiveFamilyLaw I b hb
    (translatedTemplate (Sum.elim
      (fun j : Fin 4 => (⟨j.val+1,by omega⟩,geometry.anchors t j))
      (coordinateWindowPrimitives geometry.window geometry.start)) u)

end InitialCoverSystem

theorem patchAtlas_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (hlarge : 20 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      Nonempty B.PatchAtlas := by
  obtain ⟨C⟩ := concurrentGeometry_exists a r hr.1
  obtain ⟨L₁,hL₁⟩ := rectangularAtlas_eventually (hm := hm) hlarge hr hSlope hconj
  obtain ⟨L₂,hL₂⟩ := fixedChartTables_eventually (hm := hm) hr (by omega)
    (fun _ : Unit => initialPatchPrimitives r C.mesh)
  obtain ⟨L₃,hL₃⟩ := concurrent_chart_tables_eventually (hm := hm) hr (by omega)
    C.anchors (fun _ => coordinateWindowPrimitives C.window C.start)
  refine ⟨L₁+L₂+L₃,fun M hM B => ?_⟩
  obtain ⟨A⟩ := hL₁ M (by omega) B
  exact ⟨⟨A,C,(fun u I b hb => hL₂ M (by omega) B () u I b hb),hL₃ M (by omega) B⟩⟩

end ConcurrentGeometry

section ClosedCellTemplates

theorem closedWindow_diameter (n : ℕ) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (x y : ℝ × ℝ)
    (hx : ∀ d, ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate x d ∧
      realCoordinate x d ≤ ordinary (windowCut n (q d) (cell d).succ))
    (hy : ∀ d, ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate y d ∧
      realCoordinate y d ≤ ordinary (windowCut n (q d) (cell d).succ)) :
    dist x y ≤ 200/(n:ℝ) := by
  have h (d : Fin 2) : |realCoordinate x d-realCoordinate y d| ≤ 200/(n:ℝ) := by
    have hh := windowCut_mesh n (q d) (cell d)
    have hx' := hx d
    have hy' := hy d
    apply abs_le.mpr
    constructor <;> linarith
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  exact ⟨h 0,h 1⟩

theorem windowRectangle_closed_intersection_near {a : ℕ} (ha : 0<a)
    (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (x y u v : GenericSquare a)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hu : u ∈ (windowRectangle a n q cell).val)
    (hv : v ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x) ≤ ordinary c)
    (hcy : ordinary c ≤ cutForm a i (windowPlanarLift q y))
    (hdu : cutForm a j (windowPlanarLift q u) ≤ ordinary d)
    (hdv : ordinary d ≤ cutForm a j (windowPlanarLift q v)) :
    ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d ∧
      ∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut n (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut n (q k) (cell k).succ)) →
        dist z p ≤ lineIntersectionConstant a*(200/(n:ℝ)) := by
  obtain ⟨z,hz,hz'⟩ := allowable_lines_intersect ha i j hij c d
  refine ⟨z,hz,hz',fun p hp => ?_⟩
  have hc (t : GenericSquare a) (ht : t ∈ (windowRectangle a n q cell).val) :
      dist p (windowPlanarLift q t) ≤ 200/(n:ℝ) := by
    apply closedWindow_diameter n q cell p (windowPlanarLift q t) hp
    intro k
    exact ⟨((windowRectangle_mem n hn q cell t).mp ht k).1,
      ((windowRectangle_mem n hn q cell t).mp ht k).2.le⟩
  have h₁ := crossing_level_bound (ordinary (lineNormal a i).1) (ordinary (lineNormal a i).2)
    (ordinary c) (200/(n:ℝ)) p (windowPlanarLift q x) (windowPlanarLift q y)
    (by simpa only [cutForm_normal] using hcx) (by simpa only [cutForm_normal] using hcy)
    (hc x hx) (hc y hy)
  have h₂ := crossing_level_bound (ordinary (lineNormal a j).1) (ordinary (lineNormal a j).2)
    (ordinary d) (200/(n:ℝ)) p (windowPlanarLift q u) (windowPlanarLift q v)
    (by simpa only [cutForm_normal] using hdu) (by simpa only [cutForm_normal] using hdv)
    (hc u hu) (hc v hv)
  have hδ : 0 ≤ 200/(n:ℝ) := by positivity
  have hm₁ := mul_le_mul_of_nonneg_right (le_max_left
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hm₂ := mul_le_mul_of_nonneg_right (le_max_right
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hh := real_two_lines_distance_bound _ _ _ _ (ordinary c) (ordinary d)
    (real_lineDet_ne_zero ha i j hij) z p (by simpa only [cutForm_normal] using hz)
    (by simpa only [cutForm_normal] using hz') _ (by positivity) (h₁.trans hm₁) (h₂.trans hm₂)
  have hh' : dist z p ≤ lineIntersectionCoefficient a i j*(200/(n:ℝ)) := by
    simpa only [lineIntersectionCoefficient,lineDet,map_sub,map_mul,mul_assoc] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_right (lineIntersectionCoefficient_le a i j) hδ)

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem crossing_cell_template (ha : 0<a) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (x y v w : GenericSquare a)
    (hx : x ∈ (windowRectangle a C.mesh q cell).val)
    (hy : y ∈ (windowRectangle a C.mesh q cell).val)
    (hv : v ∈ (windowRectangle a C.mesh q cell).val)
    (hw : w ∈ (windowRectangle a C.mesh q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x) ≤ ordinary c)
    (hcy : ordinary c ≤ cutForm a i (windowPlanarLift q y))
    (hdv : cutForm a j (windowPlanarLift q v) ≤ ordinary d)
    (hdw : ordinary d ≤ cutForm a j (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      integralCutForm a i (u+C.anchors t i)=c ∧
      integralCutForm a j (u+C.anchors t j)=d ∧
      (∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
        ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate p k ∧
          realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      (∀ b ∈ ({i,j} : Set (Fin 4)), ∀ p : ℝ × ℝ,
        (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
        ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) := by
  obtain ⟨z,hz,hz',hclose⟩ := windowRectangle_closed_intersection_near ha C.mesh C.mesh_large q cell
    i j hij c d x y v w hx hy hv hw hcx hcy hdv hdw
  obtain ⟨t,u₁,u₂,htu⟩ := all_intersections_finite_templates ha i j hij c d z hz hz'
  let u := (u₁,u₂)
  have hi := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec t u i c z htu hz
  have hj := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec t u j d z htu hz'
  refine ⟨t,u,hi.1,hj.1,?_,?_⟩
  · intro p hp k
    apply (C.margins t).translated_inner u p
    rw [← htu,dist_comm]
    exact ((hclose p hp).trans_lt C.mesh_fine).le
  · intro b hb p hp k
    have hb' : b=i ∨ b=j := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hb
    have hdist : dist (ordinary (u+C.anchors t b).1,ordinary (u+C.anchors t b).2)
        (vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2))<C.epsilon := by
      rw [← htu]
      rcases hb' with rfl | rfl
      · exact hi.2
      · exact hj.2
    exact (C.margins t).translated_outer u (u+C.anchors t b) p hdist hp k

end ConcurrentGeometry
end ClosedCellTemplates

end SimpleAmenable
end
end

end OAI
