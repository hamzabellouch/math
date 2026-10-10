import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlTransfer
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullSector
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ControlCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntersectionControl
namespace ActualLawfulTable
variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_split (U V : Set Ω) (s : UniversalExtension E) :
    T.sector U s = T.sector (U ∩ V) s*T.sector (U \ V) s := by
  have hd : Disjoint (U ∩ V) (U \ V) := Set.disjoint_left.mpr (by aesop)
  have he : (U ∩ V) ∪ (U \ V) = U := by ext x; simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]; tauto
  have hh := DFunLike.congr_fun (T.sector_union hd) s
  simpa only [he,commutingProduct_apply] using hh

theorem sector_four_factors (U V : Set Ω) (s : UniversalExtension E) :
    T.sector Set.univ s = T.sector (U ∩ V) s*T.sector (U \ V) s*
      T.sector (V \ U) s*T.sector (U ∪ V)ᶜ s := by
  rw [T.sector_split Set.univ U s]
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff]
  rw [T.sector_split U V s,T.sector_split Uᶜ V s]
  have he₁ : Uᶜ ∩ V = V \ U := by ext x; simp only [Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_sdiff]; tauto
  have he₂ : Uᶜ \ V = (U ∪ V)ᶜ := by ext x; simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_sdiff]; tauto
  simp only [he₁,he₂,mul_assoc]

end ActualLawfulTable

variable {α H Q Ω : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]
    {q : H →* Q} {v : (Ω → alternatingGroup α) →* Q}
    (T : ActualLawfulTable q v) (c : alternatingGroup α →* H)

theorem table_small_control_intersection
    (hwhole : T.sector Set.univ = c.comp (universalProjection (alternatingGroup α)))
    (f : TrackStar α →* H) (U V : Set Ω)
    (hU : SmallControlled c f (T.sector U)) (hV : SmallControlled c f (T.sector V)) :
    SmallControlled c f (T.sector (U ∩ V)) := by
  refine small_control_intersection c f (T.sector (U ∩ V)) (T.sector (U \ V))
    (T.sector (V \ U)) (T.sector (U ∪ V)ᶜ) ?_ ?_ ?_ ?_ ?_ ?_
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · intro s
    rw [← T.sector_four_factors U V s,hwhole]
    rfl
  · intro I t x hx
    dsimp only
    rw [← T.sector_split U V]
    exact hU I t x hx
  · intro I t x hx
    dsimp only
    have he : V ∩ U = U ∩ V := Set.inter_comm _ _
    have hh := T.sector_split V U (universalMap (subtypeAlternatingHom I.val) t)
    rw [he] at hh
    rw [← hh]
    exact hV I t x hx

variable {a : ℕ} {ι : Type*}

theorem resolvedPolygonMask_inter (U : ι → polygonAlgebra a) (V W : Set (GenericSquare a))
    (hV : ResolvedBy (fun i => (U i).val) V) (hW : ResolvedBy (fun i => (U i).val) W) :
    resolvedPolygonMask U (V ∩ W) = resolvedPolygonMask U V ∩ resolvedPolygonMask U W := by
  ext ω
  obtain ⟨x,hx⟩ := ω.property
  obtain rfl : ω = ⟨polygonAssignment U x,⟨x,rfl⟩⟩ := Subtype.ext hx.symm
  have hVW : ResolvedBy (fun i => (U i).val) (V ∩ W) := by
    intro x y he
    exact and_congr (hV x y he) (hW x y he)
  simp only [Set.mem_inter_iff,resolvedPolygonMask_mem U _ hVW x,
    resolvedPolygonMask_mem U _ hV x,resolvedPolygonMask_mem U _ hW x]

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_intersection_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hfV : SmallControlled B.c f (B.fullGeometricSector hlarge P h V))
    (hfW : SmallControlled B.c f (B.fullGeometricSector hlarge P h W)) :
    SmallControlled B.c f (B.fullGeometricSector hlarge P h (V ⊓ W)) := by
  have hw := B.fullGeometricSector_whole hlarge P h
  unfold fullGeometricSector at hw hfV hfW ⊢
  change (B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) Set.univ) = _ at hw
  rw [resolvedPolygonMask_univ] at hw
  change SmallControlled _ _ ((B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) (V.val ∩ W.val)))
  rw [resolvedPolygonMask_inter _ _ _ hV hW]
  exact table_small_control_intersection _ B.c hw f _ _ hfV hfW

end InitialCoverSystem
end IntersectionControl

section ActualRectangleBridge

noncomputable def coordinateRectangle (a : ℕ) (u v : Fin 2 → CutRing) : polygonAlgebra a :=
  coordinateInterval a 0 (u 0) (v 0) ⊓ coordinateInterval a 1 (u 1) (v 1)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_rectangle_bridge_control (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p q : Fin 2 → ℤ),
      (∀ j, ((q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      ∀ u v U V : Fin 2 → CutRing,
      (∀ j, ordinary (u j) ≤ ordinary (v j)) →
      (∀ j, ordinary (U j) ≤ ordinary (u j)-δ) →
      (∀ j, ordinary (v j)+δ ≤ ordinary (V j)) →
      (∀ j, ordinary (V j)-ordinary (U j) < 1) →
      (∀ j, p j ≤ endpointLabel (u j) ∧ endpointLabel (u j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+s j) →
      (∀ j, q j ≤ endpointLabel (U j) ∧ endpointLabel (U j) < q j+(n/8:ℕ)) →
      (∀ j, q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n h j (s j) (hs j) (p j) (coordinateInterval a j (u j) (v j)))) →
      SmallControlled B.c f (B.windowSector (by omega) n h q (coordinateRectangle a U V)) := by
  obtain ⟨N,hN,hbridge⟩ := B.old_axis_bridge_control hlarge hK hδ
  refine ⟨N,hN,?_⟩
  intro n hn h s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
  have hc (j : Fin 2) : SmallControlled B.c f
      (B.windowSector (by omega) n h q (coordinateInterval a j (U j) (V j))) := by
    have hh := hbridge n hn h j (s j) (hs j) (p j) (q j) (hpq j)
      (u j) (v j) (U j) (V j) (huv j) (hU j) (hV j) (hlen j)
      (hlu j) (hlv j) (hlU j) (hlV j) f hf (hstart j)
    rw [B.axisSector_in_window (by omega) n h j (n/8) (Nat.div_le_self n 8)
      (q j) q le_rfl (by omega) (coordinateInterval a j (U j) (V j))
      (axisInterval_resolved j (n/8) (q j) (U j) (V j) (hlU j) (hlV j))] at hh
    exact hh
  apply B.fullGeometricSector_intersection_control (by omega) (coordinateWindowPrimitives n q)
    (fun I _ b hb => h I b hb q) (coordinateInterval a 0 (U 0) (V 0))
    (coordinateInterval a 1 (U 1) (V 1)) ?_ ?_ f (hc 0) (hc 1)
  · exact coordinateLabelWindow_resolved n q 0 (U 0) (V 0)
      ⟨(hlU 0).1,by have h' := (hlU 0).2; omega⟩
      ⟨(hlV 0).1,by have h' := (hlV 0).2; omega⟩
  · exact coordinateLabelWindow_resolved n q 1 (U 1) (V 1)
      ⟨(hlU 1).1,by have h' := (hlU 1).2; omega⟩
      ⟨(hlV 1).1,by have h' := (hlV 1).2; omega⟩

end InitialCoverSystem
end ActualRectangleBridge

end SimpleAmenable
end
end

end OAI
