import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalStarTables
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CompactFineGrid
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveFormalSectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SimultaneousActiveActions
namespace InitialCoverSystem.RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.RectangularAtlas) (C : ConcurrentGeometry a r)

theorem simultaneous_active_slope_actions {ι : Type*}
    (hlarge : 20 ≤ m+1) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (ha : 0 < a)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      (∀ p : ℝ × ℝ, dist p z < C.epsilon/2 → ∀ k,
        ordinary ((C.margins t).lower k+pointCoordinate u k)<realCoordinate p k ∧
        realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      ∀ i, cutForm a (j i) z=ordinary (c i) →
        integralCutForm a (j i) (u+C.anchors t (j i))=c i ∧
        ∀ (d : Fin 2), j i=slopeDirection d → ∀ v : CutRing × CutRing,
          integralCutForm a (slopeDirection d) v=c i →
          ∀ L V : Fin 2 → CutRing,
          (∀ k, ordinary (L k) ≤ ordinary (V k)) →
          (∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate v k) ∧
            ordinary (V k)-ordinary (pointCoordinate v k) ≤ ordinary r) →
          (∀ k, |ordinary (L k)-realCoordinate z k| < C.epsilon/2 ∧
            |ordinary (V k)-realCoordinate z k| < C.epsilon/2) →
          ∀ n q,
          ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
            (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val →
          ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
          B.AlignedSmallSupported f →
          SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q
            (coordinateRectangle a L V)) →
          ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
            ∀ b ∈ f.range,
              A.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
              A.slope (by omega) d (u+C.anchors t (j i)) (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d (u+C.anchors t (j i)) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨t,u,hmargin,hactive⟩ := C.simultaneous_active_neighborhood ha j c z
  refine ⟨t,u,hmargin,fun i hi => ⟨(hactive i hi).1,?_⟩⟩
  intro d hd v hv L V hLV hclip hnear n q hW f hf hc I s b hb
  have hLdist : dist (ordinary (L 0),ordinary (L 1)) z < C.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).1,(hnear 1).1⟩
  have hVdist : dist (ordinary (V 0),ordinary (V 1)) z < C.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).2,(hnear 1).2⟩
  have hclip' : ∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate (u+C.anchors t (j i)) k) ∧
      ordinary (V k)-ordinary (pointCoordinate (u+C.anchors t (j i)) k) ≤ ordinary r := by
    intro k
    have hL := (hactive i hi).2 (ordinary (L 0),ordinary (L 1))
      (fun l => (hmargin _ hLdist l).imp le_of_lt le_of_lt) k
    have hV := (hactive i hi).2 (ordinary (V 0),ordinary (V 1))
      (fun l => (hmargin _ hVdist l).imp le_of_lt le_of_lt) k
    have heL : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
    have heV : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
    rw [heL] at hL
    rw [heV] at hV
    have hL' := (abs_lt.mp hL).1
    have hV' := (abs_lt.mp hV).2
    have hrad := C.radius
    have hpos := C.positive
    constructor <;> linarith
  have hline : integralCutForm a (slopeDirection d) v=
      integralCutForm a (slopeDirection d) (u+C.anchors t (j i)) := by
    rw [hv,← hd,(hactive i hi).1]
  have hz : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) v) := by
    rw [hv,← hd]; exact hi
  have hnear' : ∀ k, |ordinary (L k)-realCoordinate z k| ≤ ordinary r/4 ∧
      |ordinary (V k)-realCoordinate z k| ≤ ordinary r/4 := by
    intro k
    have hh := hnear k
    have hrad := C.radius
    have hpos := C.positive
    constructor <;> linarith
  exact A.slope_line_action hlarge hr d v (u+C.anchors t (j i)) hline L V hLV
    hclip hclip' z hz hnear' n q hW f hf hc I s b hb

end InitialCoverSystem.RectangularAtlas
end SimultaneousActiveActions

section ActualFormalPartitions
variable {a : ℕ} {ι D : Type*}

theorem polygon_partition_formal_extension (U : ι → polygonAlgebra a)
    (W : D → polygonAlgebra a) (d₀ : D)
    (hW : ∀ d, ResolvedBy (fun i => (U i).val) (W d).val)
    (hd : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hc : ∀ x : GenericSquare a, ∃ d, x ∈ (W d).val) :
    ∃ C : D → Set (ι → Bool),
      (Pairwise fun d e => Disjoint (C d) (C e)) ∧
      (∀ σ, ∃ d, σ ∈ C d) ∧
      ∀ d x, polygonAssignment U x ∈ C d ↔ x ∈ (W d).val := by
  classical
  let chooseCell (σ : ι → Bool) : D :=
    if h : ∃ x : GenericSquare a, polygonAssignment U x=σ then
      Classical.choose (hc (Classical.choose h)) else d₀
  refine ⟨fun d => {σ | chooseCell σ=d},?_,?_,?_⟩
  · intro d e hde
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    exact hde (hσ.symm.trans hτ)
  · intro σ
    exact ⟨chooseCell σ,rfl⟩
  · intro d x
    have hx : ∃ y : GenericSquare a, polygonAssignment U y=polygonAssignment U x := ⟨x,rfl⟩
    have hy := Classical.choose_spec hx
    have hcell := Classical.choose_spec (hc (Classical.choose hx))
    have hactual : x ∈ (W (chooseCell (polygonAssignment U x))).val := by
      dsimp only [chooseCell]
      rw [dite_eq_left hx]
      exact (hW _ _ _ ((polygonAssignment_eq_iff U _ _).mp hy)).mp hcell
    change chooseCell (polygonAssignment U x)=d ↔ x ∈ (W d).val
    constructor
    · intro he; exact he ▸ hactual
    · intro hxW
      by_contra hn
      exact Set.disjoint_left.mp (hd hn) hactual hxW

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {J κ : Type*} [Finite κ] {η : J → Type*} [∀ i, Finite (η i)]

theorem independent_formal_partition (hlarge : 15 < m+1)
    (P : (i : J) → η i → Fin 5 × (CutRing × CutRing))
    (T : ∀ i, FormalStarTable (A.starFamily hlarge (P i)))
    (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : (i : J) → κ → η i) (he : ∀ i, P i ∘ v i=Q)
    (hQ : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (W : D → polygonAlgebra a) (d₀ : D)
    (hW : ∀ d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) Q j).val) (W d).val)
    (hd : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hc : ∀ x : GenericSquare a, ∃ d, x ∈ (W d).val) :
    ∃ C : (i : J) → D → Set (η i → Bool),
      (∀ i, Pairwise fun d e => Disjoint (C i d) (C i e)) ∧
      (∀ i σ, ∃ d, σ ∈ C i d) ∧
      (∀ i d, (T i).sector (C i d)=B.fullGeometricSector hlarge Q hQ (W d)) ∧
      (∀ i d, (T i).sector (C i d)ᶜ=B.fullGeometricSector hlarge Q hQ (W d)ᶜ) := by
  classical
  obtain ⟨U,hUd,hUc,hU⟩ := polygon_partition_formal_extension
    (primitiveTests (a := a) (r := r) Q) W d₀ hW hd hc
  let C : (i : J) → D → Set (η i → Bool) := fun i d =>
    (fun σ : η i → Bool => σ ∘ v i) ⁻¹' U d
  refine ⟨C,?_,?_,?_,?_⟩
  · intro i d e hde
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    exact Set.disjoint_left.mp (hUd hde) hσ hτ
  · intro i σ
    exact hUc (σ ∘ v i)
  · intro i d
    have h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i ∘ v i) := by rw [he i]; exact hQ
    have hWd : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i ∘ v i) j).val) (W d).val := by
      rw [he i]; exact hW d
    have hUd' : ∀ x, polygonAssignment (primitiveTests (a := a) (r := r) (P i ∘ v i)) x ∈ U d ↔ x ∈ (W d).val := by
      rw [he i]; exact hU d
    have hh := A.formalSector_subfamily_eq hlarge (P i) (T i) (v i) h (U d) (W d) hWd hUd'
    simpa only [C,he i] using hh
  · intro i d
    have h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i ∘ v i) := by rw [he i]; exact hQ
    have hWd : ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i ∘ v i) j).val) ((W d)ᶜ).val := by
      rw [he i]
      intro x y hxy
      exact not_congr (hW d x y hxy)
    have hUd' : ∀ x, polygonAssignment (primitiveTests (a := a) (r := r) (P i ∘ v i)) x ∈ (U d)ᶜ ↔ x ∈ ((W d)ᶜ).val := by
      rw [he i]
      intro x
      exact not_congr (hU d x)
    have hh := A.formalSector_subfamily_eq hlarge (P i) (T i) (v i) h (U d)ᶜ (W d)ᶜ hWd hUd'
    simpa only [C,he i,Set.preimage_compl] using hh

end InitialCoverSystem.PatchAtlas
end ActualFormalPartitions

end SimpleAmenable
end
end

end OAI
