import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ClosedLocalAssignments
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalGridPieces
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RefinementNeighborhoods
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGermActions

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitive_family_global_templates {ι : Type*} [Finite ι]
    (ha : 0<a) (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
    StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ,
    (∀ cell : Fin 2 → Fin N,
      ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val) ∧
    ∀ (cell : Fin 2 → Fin N) (J : Type)
      (f : J → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    (∀ v, B.AlignedSmallSupported (f v)) →
    (∀ v, SmallControlled B.c (f v) (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell))) →
    ∃ L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f,
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
  classical
  let _ := Fintype.ofFinite ι
  let Z := {z : ℝ × ℝ // z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1}
  have hlocal (z : Z) := A.primitive_family_local_templates ha hlarge hr P z.val z.property.1 z.property.2 hmesh
  choose G δ hδ htemplates using hlocal
  let O : Z → Set (ℝ × ℝ) := fun z => Metric.ball z.val (δ z)
  have hO z : IsOpen (O z) := Metric.isOpen_ball
  have hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ z, O z := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,Metric.mem_ball_self (hδ ⟨z,hz⟩)⟩
  obtain ⟨s,hs⟩ := (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover O hO hcover
  have hcov : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ z : s, O z.val := by
    intro x hx
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hz,hx⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hx⟩
  let S : Finset CutRing := Finset.univ.biUnion (fun z : s => Finset.univ.biUnion (fun i : ι =>
    Finset.univ.biUnion (fun k : Fin 2 =>
      {pointCoordinate (G z.val i).oldOffset k-r,pointCoordinate (G z.val i).oldOffset k+r})))
  have hSlo (z : s) (i : ι) (k : Fin 2) : pointCoordinate (G z.val i).oldOffset k-r ∈ S := by
    simp only [S,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨z,i,k,Or.inl rfl⟩
  have hShi (z : s) (i : ι) (k : Fin 2) : pointCoordinate (G z.val i).oldOffset k+r ∈ S := by
    simp only [S,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨z,i,k,Or.inr rfl⟩
  obtain ⟨N,hN,e,he,hzero,hlast,hfine,hends,hgrids,hboxes⟩ := compact_common_refining_grid S
    (fun _ : s × ι => A.geometry.mesh) (fun _ => A.geometry.mesh_large)
    (fun _ => symmetricWindowStart r) (fun k => (G k.1.val k.2).oldOffset)
    (fun z : s => O z.val) (fun z => hO z.val) hcov (fun _ => 1) (fun _ => by norm_num)
  obtain ⟨n,q,hW⟩ := refinedGridRectangle_resolved (a := a) r e
  refine ⟨N,hN,e,he,hzero,hlast,hfine,n,q,hW,?_⟩
  intro cell J f hf hc
  obtain ⟨z,hz,_⟩ := hboxes cell
  have hnear := closedRefinedBox_endpoint_near e he cell z.val.val (δ z.val) hz
  exact htemplates z.val N e he hzero hlast hfine
    (fun i k => hends _ (hSlo z i k)) (fun i k => hends _ (hShi z i k))
    cell hnear n q (hW cell)
    (fun i => refinedGridRectangle_subset_translated_window e he hzero hlast hfine cell
      A.geometry.mesh A.geometry.mesh_large (symmetricWindowStart r) (G z.val i).oldOffset
      (hgrids (z,i))) J f hf hc

theorem primitiveStar_zero (hlarge : 15 < m+1) (u : CutRing × CutRing) :
    A.primitiveStar hlarge (0,u)=B.c.comp (universalProjection _) := by
  unfold primitiveStar
  have hu : spatialTranslate u (initialTest a r 0)=wholePolygon a := by
    apply Subtype.ext
    ext p
    simp [spatialTranslate,initialTest,wholePolygon]
  rw [hu,B.fullGeometricSector_whole]

theorem primitive_table_with_coordinates {κ : Type*} [Fintype κ]
    (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (p : Fin 5 × (CutRing × CutRing)) (j : κ → Fin 2) (v : κ → CutRing × CutRing) :
    ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) p := by
  classical
  have hc (d : Fin 2) (u : CutRing × CutRing) (e : Fin 2) (w : CutRing × CutRing) :
      Nonempty (FormalStarTable (A.starFamily (by omega)
        (oneSlopeCoordinates d u (Option.elim' e j) (Option.elim' w v)))) :=
    A.oneSlope_formal_table hlarge hr ha d u _ _
  have hconstant (u : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (0,u) := by
    let T := Classical.choice (hc 0 0 0 0)
    refine ⟨_,fun _ => rfl,T,Set.univ,?_⟩
    rw [T.sector_input none,A.primitiveStar_zero]
    rfl
  have hcoordinate (e : Fin 2) (w : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (coordinateTestIndex e,w) := by
    let T := Classical.choice (hc 0 0 e w)
    refine ⟨_,fun _ => rfl,T,{σ | σ (some none)=true},?_⟩
    exact T.sector_input (some (some none))
  have hslope (d : Fin 2) (u : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (slopeTestIndex d,u) := by
    let T := Classical.choice (hc d u 0 0)
    refine ⟨_,fun _ => rfl,T,{σ | σ none=true},?_⟩
    exact T.sector_input (some none)
  rcases p with ⟨p,u⟩
  fin_cases p
  · exact hconstant u
  · exact hcoordinate 0 u
  · exact hcoordinate 1 u
  · exact hslope 0 u
  · exact hslope 1 u

theorem primitive_family_actual_global_law {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    HasCentralLaw (smallFamilyModel (actualTestMask (primitiveTests (a := a) (r := r) P)))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) P)).rangeRestrict := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨N,hN,e,he,hzero,hlast,hfine,n,q,hW,htemplates⟩ :=
    A.primitive_family_global_templates ha (by omega) hr P hmesh
  let D := Fin 2 → Fin N
  let _ : Nonempty D := ⟨fun _ => ⟨0,hN⟩⟩
  let κ := Fin 2 × Fin (n-1)
  let W : D → polygonAlgebra a := refinedGridRectangle a N e
  let Q₀ := coordinateWindowPrimitives n q
  let P' : Option ι → Fin 5 × (CutRing × CutRing) := Option.elim' (0,0) P
  have ht (i : Option ι) := A.primitive_table_with_coordinates hlarge hr ha (P' i)
    (Prod.fst : κ → Fin 2) (fun k : κ => (Q₀ k).2)
  choose Q hQ T U hU using ht
  let F := fun i => A.starFamily (by omega) (Q i)
  have hinput : formalGridInput F T U=A.starFamily (by omega) P := by
    funext i
    change (T i).sector (U i)=_
    rw [hU]
    cases i with
    | none => exact A.primitiveStar_zero (by omega) 0
    | some i => rfl
  have hsub (i : Option ι) : Q i ∘ (fun k : κ => some (some k))=Q₀ := by
    funext k
    exact hQ i k
  have hcoord (i : Option ι) : ∀ I, I.card ≤ 15 → ∀ b hb,
      B.PrimitiveFamilyLaw I b hb (Q i ∘ (fun k : κ => some (some k))) := by
    rw [hsub]
    exact fun I _ b hb => A.rectangles.rectangles n I b hb q
  have hmasks (i : Option ι) := A.formalRectangleMasks (by omega) (Q i) (T i)
    (fun k : κ => some (some k)) (hcoord i) W
    (by rw [hsub]; exact hW)
    (refinedGridRectangle_cover hN e he hzero hlast hfine)
    (refinedGridRectangle_disjoint e he hzero hlast hfine)
  choose C hdis hcover hj' hk' hactual using hmasks
  let j : D → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
    fun d => B.windowSector (by omega) n (A.rectangles.rectangles n) q (W d)
  let k : D → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
    fun d => B.windowSector (by omega) n (A.rectangles.rectangles n) q (W d)ᶜ
  have hj (i : Option ι) (d : D) : (T i).sector (C i d)=j d := by
    rw [hj']
    simp only [hsub]
    rfl
  have hk (i : Option ι) (d : D) : (T i).sector (C i d)ᶜ=k d := by
    rw [hk']
    simp only [hsub]
    rfl
  have hF (i : Option ι) (v) : B.AlignedSmallSupported (F i v) :=
    A.starFamily_supported (by omega) (Q i) v
  have hc (i : Option ι) : F i none=B.c.comp (universalProjection _) := rfl
  have hpieces (d : D) : ∀ i, B.AlignedSmallSupported (formalGridPiece F T U C d i) :=
    formalGridPiece_supported F T U C _ hF d
  have hcontrols (d : D) : ∀ i, SmallControlled B.c (formalGridPiece F T U C d i) (j d) :=
    formalGridPiece_control F T U C B.c hc j hj d
  have htemplates' (d : D) : ∃ L : B.LocalPatchTemplate (by omega)
      (formalGridInput F T U) (formalGridPiece F T U C d),
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
    rw [hinput]
    exact htemplates d (Option ι) (formalGridPiece F T U C d) (hpieces d) (hcontrols d)
  choose L hreal using htemplates'
  apply B.independent_actual_patching hlarge F T U C hF hc hdis hcover j k hj hk
    (fun d => B.fullGeometricSector_supported (by omega) Q₀ _ (W d) (hW d))
    (fun d s t => B.fullGeometricSector_commute (by omega) Q₀ _ (W d) (W d)ᶜ
      (hW d) disjoint_compl_right s t) ?_ (B.smallPrimitiveInputs (by omega) P) ?_
    (primitiveTests (a := a) (r := r) P) L hreal
  · rw [hinput]
    rfl
  · intro I i
    rw [hinput]
    exact A.starFamily_small (by omega) P I i

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
