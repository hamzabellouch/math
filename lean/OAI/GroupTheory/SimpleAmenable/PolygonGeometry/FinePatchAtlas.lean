import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowClipping
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FinePatchAtlas

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

noncomputable def refineMesh (n : ℕ) (hn : C.mesh  ≤  n) : ConcurrentGeometry a r :=
  { C with
    mesh := n
    mesh_large := C.mesh_large.trans hn
    clipping := C.clipping.trans hn
    mesh_fine := by
      have hpos : (0:ℝ) < C.mesh := by exact_mod_cast (show 0 < C.mesh by have := C.mesh_large; omega)
      have hle : (C.mesh:ℝ) ≤ n := by exact_mod_cast hn
      have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 200) hpos hle
      exact (mul_le_mul_of_nonneg_left h (by linarith [lineIntersectionConstant_ge_one a])).trans_lt C.mesh_fine }

theorem exists_finer (C : ConcurrentGeometry a r) (K δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ConcurrentGeometry a r, K*(200/(D.mesh:ℝ)) < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (200*K/δ)
  let n := max C.mesh N
  let D := C.refineMesh n (le_max_left _ _)
  refine ⟨D,?_⟩
  change K*(200/(n:ℝ)) < δ
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by have := C.mesh_large; dsimp [n]; omega)
  rw [← mul_div_assoc,div_lt_iff₀ hn]
  have h := (div_lt_iff₀ hδ).mp hN
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast (le_max_right C.mesh N)
  nlinarith

end ConcurrentGeometry

theorem rectangularAtlas_fixed_radius_eventually {a m : ℕ} {r : CutRing} {hm : 2  ≤  m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (hlarge : 20  ≤  m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ s : CutRing, 0 < ordinary s ∧ ordinary s < ordinary r/8 ∧
      ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
        ∃ A : B.RectangularAtlas, A.radius=s := by
  obtain ⟨s,u,v,hs,hsr,huv,hshort⟩ := exists_symmetric_short_chart a r hr.1
  obtain ⟨k,p,hp⟩ := exists_full_overlap_window a r u
  obtain ⟨s₁,hs₁,hs₁'⟩ := exists_cut_between (by linarith : (0:ℝ) < ordinary r/8)
  obtain ⟨L₁,hL₁⟩ := coordinate_all_eventually (hm := hm) hlarge hr hSlope hconj
  obtain ⟨L₂,hL₂⟩ := tangentChartTables_eventually (hm := hm) hr (by omega) k p u
  obtain ⟨L₃,hL₃⟩ := tangentChartTables_eventually (hm := hm) hr (by omega)
    (symmetricWindowLength s₁) (symmetricWindowStart s₁) u
  refine ⟨s₁,hs₁,hs₁',L₁+L₂+L₃,fun M hM B => ?_⟩
  refine ⟨⟨k,p,u,v,huv,?_,hp,hL₁ M (by omega) B,?_,s₁,hs₁,hs₁',?_⟩,rfl⟩
  · nlinarith
  · intro d e z I _ b hb
    exact hL₂ M (by omega) B d e z I b hb
  · intro d e z I _ b hb
    exact hL₃ M (by omega) B d e z I b hb

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2  ≤  m}
    (B : InitialCoverSystem a r m hm M)

structure FinePatchAtlas extends B.PatchAtlas where
  far_mesh : (1+|ordinary (cutTau^a)|)*(200/(geometry.mesh:ℝ)) < ordinary rectangles.radius/4

end InitialCoverSystem

theorem finePatchAtlas_eventually {a m : ℕ} {r : CutRing} {hm : 2  ≤  m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      Nonempty B.FinePatchAtlas := by
  obtain ⟨s,hs,_hsr,L₁,hL₁⟩ := rectangularAtlas_fixed_radius_eventually (hm := hm) hlarge hr hSlope hconj
  obtain ⟨C₀⟩ := concurrentGeometry_exists a r hr.1
  obtain ⟨C,hC⟩ := C₀.exists_finer (1+|ordinary (cutTau^a)|) (ordinary s/4) (by positivity)
  obtain ⟨L₂,hL₂⟩ := fixedChartTables_eventually (hm := hm) hr (by omega)
    (fun _ : Unit => initialPatchPrimitives r C.mesh)
  obtain ⟨L₃,hL₃⟩ := concurrent_chart_tables_eventually (hm := hm) hr (by omega)
    C.anchors (fun _ => coordinateWindowPrimitives C.window C.start)
  refine ⟨L₁+L₂+L₃,fun M hM B => ?_⟩
  obtain ⟨A,hA⟩ := hL₁ M (by omega) B
  refine ⟨{ rectangles := A
            geometry := C
            initial := fun u I b hb => hL₂ M (by omega) B () u I b hb
            concurrent := hL₃ M (by omega) B
            far_mesh := ?_ }⟩
  simpa only [hA] using hC

end FinePatchAtlas

section FarGridActions

theorem cutForm_dist_bound (a : ℕ) (j : Fin 4) (x y : ℝ × ℝ) :
    |cutForm a j x-cutForm a j y| ≤ (1+|ordinary (cutTau^a)|)*dist x y := by
  have hc : 0 ≤ |ordinary (cutTau^a)| *dist x y := mul_nonneg (abs_nonneg _) dist_nonneg
  have hslope : ordinary (cutTau^a)=Real.goldenRatio^a := by simp
  fin_cases j
  · have h := linear_form_dist_bound 1 0 x y
    simp only [one_mul,zero_mul,add_zero,abs_one,abs_zero] at h
    change |x.1-y.1| ≤ _
    nlinarith
  · have h := linear_form_dist_bound 0 1 x y
    simp only [one_mul,zero_mul,zero_add,abs_one,abs_zero] at h
    change |x.2-y.2| ≤ _
    nlinarith
  · have h := linear_form_dist_bound (-Real.goldenRatio^a) 1 x y
    change |(x.2-Real.goldenRatio^a*x.1)-(y.2-Real.goldenRatio^a*y.1)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope,add_comm] using h
  · have h := linear_form_dist_bound 1 (-Real.goldenRatio^a) x y
    change |(x.1-Real.goldenRatio^a*x.2)-(y.1-Real.goldenRatio^a*y.2)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope] using h

theorem windowRectangle_far_sign {a : ℕ} (j : Fin 4)
    (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (z : ℝ × ℝ) (hz : ∀ d,
      ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate z d ∧
      realCoordinate z d ≤ ordinary (windowCut n (q d) (cell d).succ))
    (c : ℝ) (hfar : (1+|ordinary (cutTau^a)|)*(200/(n:ℝ)) < |cutForm a j z-c|)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val) :
    (c ≤ cutForm a j (windowPlanarLift q p)) ↔ c ≤ cutForm a j z := by
  have hh := (windowRectangle_mem n hn q cell p).mp hp
  have hd := closedWindow_diameter n q cell (windowPlanarLift q p) z
    (fun d => ⟨(hh d).1,(hh d).2.le⟩) hz
  have hb := (cutForm_dist_bound a j (windowPlanarLift q p) z).trans
    (mul_le_mul_of_nonneg_left hd (by positivity))
  by_cases h : c ≤ cutForm a j z
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hfar
    have h' := (abs_le.mp hb).1
    constructor
    · intro _; exact h
    · intro _; linarith
  · have hc : cutForm a j z < c := lt_of_not_ge h
    rw [abs_of_neg (sub_neg.mpr hc)] at hfar
    have h' := (abs_le.mp hb).2
    exact iff_of_false (by intro hh; linarith) h

theorem windowRectangle_far_clipped {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (k : Fin 2 → ℤ)
    (hk : ∀ d, -ordinary r ≤ ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
      ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ) ≤ ordinary r)
    (z : ℝ × ℝ) (hz : ∀ d,
      ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate z d ∧
      realCoordinate z d ≤ ordinary (windowCut n (q d) (cell d).succ))
    (hfar : (1+|ordinary (cutTau^a)|)*(200/(n:ℝ)) <
      |cutForm a j z+cutForm a j ((k 0:ℝ),(k 1:ℝ))|) :
    clippedSlopePrimitive a r j ⊓ windowRectangle a n q cell =
      if 0 ≤ cutForm a j z+cutForm a j ((k 0:ℝ),(k 1:ℝ))
      then windowRectangle a n q cell else ⊥ := by
  classical
  apply Subtype.ext
  ext p
  have hside (hp : p ∈ (windowRectangle a n q cell).val) :
      (p ∈ (clippedSlopePrimitive a r j).val) ↔
        0 ≤ cutForm a j z+cutForm a j ((k 0:ℝ),(k 1:ℝ)) := by
    have hf := windowRectangle_far_sign j n hn q cell z hz
      (-cutForm a j ((k 0:ℝ),(k 1:ℝ))) (by simpa only [sub_neg_eq_add] using hfar) p hp
    have he := windowRectangle_clipped_sign r j hr n hn q cell k hk p hp
    change (p ∈ (clippedSlopePrimitive a r j).val) ↔
      0 ≤ cutForm a j (windowPlanarLift q p+((k 0:ℝ),(k 1:ℝ))) at he
    rw [cutForm_add] at he
    rw [he,← neg_le_iff_add_nonneg,hf,neg_le_iff_add_nonneg]
  by_cases h : 0 ≤ cutForm a j z+cutForm a j ((k 0:ℝ),(k 1:ℝ))
  · simp only [h,↓reduceIte]
    change (p ∈ (clippedSlopePrimitive a r j).val ∧ p ∈ (windowRectangle a n q cell).val) ↔
      p ∈ (windowRectangle a n q cell).val
    exact ⟨And.right,fun hp => ⟨(hside hp).mpr h,hp⟩⟩
  · simp only [h,↓reduceIte]
    change (p ∈ (clippedSlopePrimitive a r j).val ∧ p ∈ (windowRectangle a n q cell).val) ↔ False
    exact ⟨fun hp => h ((hside hp.2).mp hp.1),False.elim⟩

end FarGridActions

end SimpleAmenable
end
end

end OAI
