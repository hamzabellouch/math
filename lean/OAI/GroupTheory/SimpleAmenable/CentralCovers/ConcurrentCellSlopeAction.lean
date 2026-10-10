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
section ConcurrentCellSlopeAction
namespace InitialCoverSystem.RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.RectangularAtlas) (C : ConcurrentGeometry a r)

theorem concurrent_cell_slope_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (ha : 0<a)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (d : Fin 2) (axis : Fin 4) (hne : slopeDirection d≠axis)
    (z : CutRing × CutRing) (c : CutRing)
    (hclip : ∀ k, -ordinary r ≤ ordinary (windowCut C.mesh (q k) (cell k).castSucc)-
        ordinary (pointCoordinate z k) ∧
      ordinary (windowCut C.mesh (q k) (cell k).succ)-ordinary (pointCoordinate z k) ≤ ordinary r)
    (x y v w : GenericSquare a)
    (hx : x ∈ (windowRectangle a C.mesh q cell).val)
    (hy : y ∈ (windowRectangle a C.mesh q cell).val)
    (hv : v ∈ (windowRectangle a C.mesh q cell).val)
    (hw : w ∈ (windowRectangle a C.mesh q cell).val)
    (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤ ordinary (integralCutForm a (slopeDirection d) z))
    (hcy : ordinary (integralCutForm a (slopeDirection d) z) ≤ cutForm a (slopeDirection d) (windowPlanarLift q y))
    (hdv : cutForm a axis (windowPlanarLift q v) ≤ ordinary c)
    (hdw : ordinary c ≤ cutForm a axis (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      integralCutForm a (slopeDirection d) (u+C.anchors t (slopeDirection d))=
        integralCutForm a (slopeDirection d) z ∧
      integralCutForm a axis (u+C.anchors t axis)=c ∧
      (∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
        ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate p k ∧
          realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      (∀ b ∈ ({slopeDirection d,axis} : Set (Fin 4)), ∀ p : ℝ × ℝ,
        (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
        ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) ∧
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
        B.AlignedSmallSupported f →
        SmallControlled B.c f (B.windowSector (by omega) C.mesh (A.rectangles C.mesh) q
          (windowRectangle a C.mesh q cell)) →
        ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
          ∀ b ∈ f.range,
            A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
              A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨t,u,hline,haxis,hmargin,hclose⟩ := C.crossing_cell_template ha q cell
    (slopeDirection d) axis hne (integralCutForm a (slopeDirection d) z) c
    x y v w hx hy hv hw hcx hcy hdv hdw
  refine ⟨t,u,hline,haxis,hmargin,hclose,?_⟩
  let L := fun k => windowCut C.mesh (q k) (cell k).castSucc
  let V := fun k => windowCut C.mesh (q k) (cell k).succ
  have hLV (k) : ordinary (L k) ≤ ordinary (V k) :=
    (windowCut_strictMono C.mesh (q k) (Fin.castSucc_lt_succ (i := cell k))).le
  obtain ⟨z₀,hz₀,hz₀cell⟩ := windowRectangle_crossing_line_point C.mesh C.mesh_large q cell
    (slopeDirection d) (integralCutForm a (slopeDirection d) z) x y hx hy hcx hcy
  have hLcell : ∀ k, ordinary (L k) ≤ realCoordinate (ordinary (L 0),ordinary (L 1)) k ∧
      realCoordinate (ordinary (L 0),ordinary (L 1)) k ≤ ordinary (V k) := by
    intro k; fin_cases k <;> exact ⟨le_rfl,hLV _⟩
  have hVcell : ∀ k, ordinary (L k) ≤ realCoordinate (ordinary (V 0),ordinary (V 1)) k ∧
      realCoordinate (ordinary (V 0),ordinary (V 1)) k ≤ ordinary (V k) := by
    intro k; fin_cases k <;> exact ⟨hLV _,le_rfl⟩
  have hclip' : ∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate (u+C.anchors t (slopeDirection d)) k) ∧
      ordinary (V k)-ordinary (pointCoordinate (u+C.anchors t (slopeDirection d)) k) ≤ ordinary r := by
    intro k
    have hmL := fun l => (hmargin _ hLcell l).imp le_of_lt le_of_lt
    have hmV := fun l => (hmargin _ hVcell l).imp le_of_lt le_of_lt
    have h₁ := hclose (slopeDirection d) (by simp) _ hmL k
    have h₂ := hclose (slopeDirection d) (by simp) _ hmV k
    have hc₁ : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
    have hc₂ : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
    rw [hc₁] at h₁
    rw [hc₂] at h₂
    have hb₁ := (abs_lt.mp h₁).1
    have hb₂ := (abs_lt.mp h₂).2
    have hh := C.radius
    have hpos := C.positive
    constructor <;> linarith
  have hnear (k) : |ordinary (L k)-realCoordinate z₀ k| ≤ ordinary r/4 ∧
      |ordinary (V k)-realCoordinate z₀ k| ≤ ordinary r/4 := by
    have hh := hz₀cell k
    have hm := windowCut_mesh C.mesh (q k) (cell k)
    have he := C.mesh_small
    have hr' := C.radius
    have hpos := C.positive
    change ordinary (L k) ≤ realCoordinate z₀ k ∧ realCoordinate z₀ k ≤ ordinary (V k) at hh
    change ordinary (V k)-ordinary (L k) ≤ 200/(C.mesh:ℝ) at hm
    rw [abs_of_nonpos (by linarith : ordinary (L k)-realCoordinate z₀ k≤0),
      abs_of_nonneg (by linarith : 0≤ordinary (V k)-realCoordinate z₀ k)]
    constructor <;> linarith
  intro f hf hc I s b hb
  exact A.slope_line_action hlarge hr d z (u+C.anchors t (slopeDirection d)) hline.symm L V hLV
    hclip hclip' z₀ hz₀ hnear C.mesh q (windowRectangle_resolved C.mesh (by have hh := C.mesh_large; omega) q cell)
    f hf hc I s b hb

end InitialCoverSystem.RectangularAtlas
end ConcurrentCellSlopeAction

section ActualTemplateWindows
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem templateWindowSector_eq (hlarge : 15 < m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (z : CutRing × CutRing) (g : B.CoordinateWindowLaw k)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (v : Fin 2 × Fin (k-1) → ι)
    (hv : ∀ i, P (v i)=translatedTemplate (coordinateWindowPrimitives k p) z i)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val) :
    B.fullGeometricSector hlarge P h (spatialTranslate z V)=
      B.windowSector hlarge k g (fun j => pointLabel z j+p j) (spatialTranslate z V) := by
  apply B.chartCoordinateSector_eq_window hlarge k g (fun j => pointLabel z j+p j)
    P h v Prod.fst (fun i => z+(coordinateWindowPrimitives k p i).2)
  · intro i
    rw [hv i]
    rfl
  · intro i
    change pointLabel z i.1 + p i.1 ≤ pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1
    rw [pointLabel_add,coordinateWindow_pointLabel]
    omega
  · intro i
    change pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1 < pointLabel z i.1+p i.1+(k-1:ℕ)
    rw [pointLabel_add,coordinateWindow_pointLabel]
    have hi := i.2.isLt
    omega
  · intro x y he
    apply (translatedTemplate_resolved (a := a) (r := r) (coordinateWindowPrimitives k p) V hV z) x y
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,coordinateWindowPrimitives,
      initialTest_coordinate] using he

theorem all_rectangle_control_to_template (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (z : CutRing × CutRing)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (v : Fin 2 × Fin (k-1) → ι)
    (hv : ∀ i, P (v i)=translatedTemplate (coordinateWindowPrimitives k p) z i)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k p) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k (fun j => pointLabel z j+p j)) i).val) (spatialTranslate z V).val)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ spatialTranslate z V)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W)) :
    SmallControlled B.c f (B.fullGeometricSector (by omega) P h (spatialTranslate z V)) := by
  rw [B.templateWindowSector_eq (by omega) k p z (g k) P h v hv V hV]
  apply B.control_trans hlarge f _ _ hf (B.fullGeometricSector_supported (by omega) _ _ _ hV') hc
  exact B.all_window_control (by omega) g n k q _ W (spatialTranslate z V) hinc hW hV'

end InitialCoverSystem
end ActualTemplateWindows

end SimpleAmenable
end
end

end OAI
