import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions
import OAI.GroupTheory.SimpleAmenable.Homology.FiniteCutResolution
import OAI.GroupTheory.SimpleAmenable.CentralCovers.RefinedClippedModels

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitive_germ_action_neighborhood {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : Fin 5 × (CutRing × CutRing)) (z : ℝ × ℝ) (G : PrimitiveGerm a r z p)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (idx : G.Index → ι) (hidx : ∀ k, (j (idx k),c (idx k))=G.cuts k)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate p.2 (initialTest a r p.1)).val)
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    : ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    (∀ k, cutFraction (pointCoordinate G.oldOffset k-r) ∈ Set.range e) →
    (∀ k, cutFraction (pointCoordinate G.oldOffset k+r) ∈ Set.range e) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val →
    ∀ initial : Fin 2 → Fin A.geometry.mesh,
    refinedGridRectangle a N e cell ≤ spatialTranslate G.oldOffset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) initial) →
    ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
    B.AlignedSmallSupported f →
    SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell)) →
    ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
    ∀ x ∈ f.range,
    A.primitiveStar (by omega) p (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) p (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate p.2 (initialTest a r p.1)) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate p.2 (initialTest a r p.1)) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  cases G with
  | constant u =>
    obtain ⟨δ,hδ,hlocal⟩ := T.refined_cells_locally_decided hr
    refine ⟨δ,hδ,?_⟩
    intro N e he hzero hlast hmesh' _ _ cell hnear n q hW _ _ f hf hc I s x hx
    apply A.constant_model_action hlarge hr T hz₁ hz₂ u f hf ?_ I s x hx
    exact A.coordinate_control_inward_gate hlarge T.vertex T.offset _
      (A.coordinate_inward_resolved T.vertex T.offset z) n q _ hW
      (fun p hp => (hlocal N e he hzero hlast hmesh' cell hnear p hp).1) f hf hc
  | coordinate d u G =>
    have hlo : j (idx false)=axisDirection d ∧ c (idx false)=G.lower := ⟨congrArg Prod.fst (hidx false),congrArg Prod.snd (hidx false)⟩
    have hhi : j (idx true)=axisDirection d ∧ c (idx true)=G.upper := ⟨congrArg Prod.fst (hidx true),congrArg Prod.snd (hidx true)⟩
    have hR' : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val := by
      simpa only [initialTest_coordinate] using hR
    obtain ⟨O,hO,hz,hact⟩ := A.coordinate_model_action_neighborhood hlarge hr d u z G T hz₁ hz₂
      (idx false) (idx true) hlo hhi hR'
    obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hO z hz
    refine ⟨δ,hδ,?_⟩
    intro N e he hzero hlast hmesh' _ _ cell hnear n q hW _ _ f hf hc I s x hx
    simp only [initialTest_coordinate]
    exact hact n q _ hW
      (fun p hp => hball (refinedGridRectangle_point_near e he hzero hlast hmesh' cell z δ hnear p hp))
      f hf hc I s x hx
  | slope d u G hbox =>
    have hlo (k : Fin 2) : j (idx (.inl (k,false)))=axisDirection k ∧
        c (idx (.inl (k,false)))=pointCoordinate G.offset k-r := ⟨congrArg Prod.fst (hidx (.inl (k,false))),congrArg Prod.snd (hidx (.inl (k,false)))⟩
    have hhi (k : Fin 2) : j (idx (.inl (k,true)))=axisDirection k ∧
        c (idx (.inl (k,true)))=pointCoordinate G.offset k+r := ⟨congrArg Prod.fst (hidx (.inl (k,true))),congrArg Prod.snd (hidx (.inl (k,true)))⟩
    have hs : j (idx (.inr ()))=slopeDirection d ∧
        c (idx (.inr ()))=integralCutForm a (slopeDirection d) G.offset := ⟨congrArg Prod.fst (hidx (.inr ())),congrArg Prod.snd (hidx (.inr ()))⟩
    have hR' : ResolvedBy (fun i => halfPlane a (j i) (c i))
        (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val := by
      simpa only [initialTest_slope] using hR
    simpa only [PrimitiveGerm.oldOffset,initialTest_slope] using
      A.refined_clipped_model_action_neighborhood hlarge hr d u z G hbox T hz₁ hz₂
        (fun k => idx (.inl (k,false))) (fun k => idx (.inl (k,true))) (idx (.inr ())) hlo hhi hs hR' hmesh

theorem primitive_family_local_templates {ι : Type*} [Finite ι]
    (ha : 0<a) (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing)) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    ∃ G : ∀ i, PrimitiveGerm a r z (P i), ∃ δ : ℝ, 0<δ ∧
    ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    (∀ i k, cutFraction (pointCoordinate (G i).oldOffset k-r) ∈ Set.range e) →
    (∀ i k, cutFraction (pointCoordinate (G i).oldOffset k+r) ∈ Set.range e) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val →
    (∀ i, ∃ initial : Fin 2 → Fin A.geometry.mesh,
      refinedGridRectangle a N e cell ≤ spatialTranslate (G i).oldOffset
        (windowRectangle a A.geometry.mesh (symmetricWindowStart r) initial)) →
    ∀ (J : Type) (f : J → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    (∀ v, B.AlignedSmallSupported (f v)) →
    (∀ v, SmallControlled B.c (f v) (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell))) →
    ∃ L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f,
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
  classical
  let _ := Fintype.ofFinite ι
  let G (i : ι) := Classical.choice (PrimitiveGerm.nonempty (a := a) (z := z) hr (P i))
  let R := primitiveTests (a := a) (r := r) P
  let K := Σ i, (G i).Index
  let dir : K → Fin 4 := fun v => ((G v.1).cuts v.2).1
  let cut : K → CutRing := fun v => ((G v.1).cuts v.2).2
  obtain ⟨S,hR,hS⟩ := finite_cut_resolution_extend R dir cut
  let j : S → Fin 4 := fun p => p.val.1
  let c : S → CutRing := fun p => p.val.2
  obtain ⟨T⟩ := A.geometry.inwardChart_exists ha j c z
  let idx (i : ι) (k : (G i).Index) : S := ⟨(G i).cuts k,hS ⟨i,k⟩⟩
  have hidx i k : (j (idx i k),c (idx i k))=(G i).cuts k := rfl
  have hres i : ResolvedBy (fun s => halfPlane a (j s) (c s))
      (spatialTranslate (P i).2 (initialTest a r (P i).1)).val := hR i
  have hact i := A.primitive_germ_action_neighborhood hlarge hr (P i) z (G i) T hz₁ hz₂
    (idx i) (hidx i) (hres i) hmesh
  choose δ hδ hacts using hact
  obtain ⟨δ₀,hδ₀,hinside⟩ := T.refined_cells_locally_decided hr
  let radius : Option ι → ℝ := Option.elim' δ₀ δ
  have hpositive (i : Option ι) : 0<radius i := by
    cases i with
    | none => exact hδ₀
    | some i => exact hδ i
  obtain ⟨imin,_,hmin⟩ := Finset.univ.exists_min_image radius
    (show (Finset.univ : Finset (Option ι)).Nonempty from Finset.univ_nonempty)
  refine ⟨G,radius imin,hpositive imin,?_⟩
  intro N e he hzero hlast hmesh' hlends huends cell hnear n q hW hinitial J f hf hc
  have hnear₀ k : |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ₀ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ₀ := by
    have hm : radius imin≤δ₀ := hmin none (Finset.mem_univ none)
    exact ⟨(hnear k).1.trans_le hm,(hnear k).2.trans_le hm⟩
  have hinc : refinedGridRectangle a N e cell ≤ A.geometry.inwardMargin T.vertex T.offset z :=
    fun p hp => (hinside N e he hzero hlast hmesh' cell hnear₀ p hp).1
  let L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f := {
    index := Fin 4 ⊕ (Fin 2 × Fin (A.geometry.window-1))
    tests := A.concurrentPrimitives T.vertex T.offset
    lawful := A.concurrentLaw T.vertex T.offset
    margin := A.geometry.inwardMargin T.vertex T.offset z
    predicates := T.polygons R
    margin_resolved := A.concurrent_inward_resolved T.vertex T.offset z
    predicates_resolved := A.inward_model_resolved T R
    controlled := fun v => A.coordinate_control_inward_gate hlarge T.vertex T.offset _
      (A.coordinate_inward_resolved T.vertex T.offset z) n q _ hW hinc (f v) (hf v) (hc v)
    action := by
      intro i I s v x hx
      let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
      have hneari k : |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ i ∧
          |ordinary (e (cell k).succ)-realCoordinate z k|<δ i := by
        have hm : radius imin≤δ i := hmin (some i) (Finset.mem_univ (some i))
        exact ⟨(hnear k).1.trans_le hm,(hnear k).2.trans_le hm⟩
      obtain ⟨initial,hi⟩ := hinitial i
      exact hacts i N e he hzero hlast hmesh' (hlends i) (huends i) cell hneari n q hW
        initial hi (f v) (hf v) (hc v) I' s x hx }
  refine ⟨L,?_⟩
  intro x hx
  obtain ⟨y,_,hy⟩ := T.polygons_assignment_realized hr hz₁ hz₂ R hR x hx Set.univ isOpen_univ (Set.mem_univ z)
  exact ⟨y,hy⟩

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
