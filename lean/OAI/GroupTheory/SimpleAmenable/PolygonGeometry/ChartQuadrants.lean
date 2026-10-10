import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.IntersectionControl

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ChartQuadrants

theorem coordinateRectangle_lift {a : ℕ} (u v : Fin 2 → CutRing)
    (huv : ∀ j, ordinary (u j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (u j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a u v).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) ∧
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) := by
  change p ∈ coordinateBetween a 0 (u 0) (v 0) ∧
    p ∈ coordinateBetween a 1 (u 1) (v 1) at hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff 0 (u 0) (v 0) (huv 0) (hlen 0) p).mp hp.1
  obtain ⟨l,hl⟩ := (mem_coordinateBetween_iff 1 (u 1) (v 1) (huv 1) (hlen 1) p).mp hp.2
  refine ⟨(coordinate 0 p+(k:ℝ),coordinate 1 p+(l:ℝ)),?_,hk,hl⟩
  simp only [Int.fract_add_intCast,Int.fract_eq_self.mpr (coordinate_bounds 0 p),
    Int.fract_eq_self.mpr (coordinate_bounds 1 p)]
  rfl

theorem coordinateRectangle_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u v : Fin 2 → CutRing)
    (huv : ∀ k, ordinary (u k) ≤ ordinary (v k))
    (hu : ∀ k, -ordinary r < ordinary (u k))
    (hv : ∀ k, ordinary (v k) < ordinary r)
    (hside : ∀ t : ℝ × ℝ,
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) →
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) → 0 ≤ cutForm a j t) :
    coordinateRectangle a u v ≤ clippedSlopePrimitive a r j := by
  intro p hp
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift u v huv
    (fun k => by have h1 := hu k; have h2 := hv k; linarith [hr.2]) p hp
  apply (mem_clippedSlope_lift r j hr p t ?_ ht).mpr
  · exact hside t hx hy
  · exact ⟨⟨(hu 0).trans_le hx.1,hx.2.trans (hv 0)⟩,
      ⟨(hu 1).trans_le hy.1,hy.2.trans (hv 1)⟩⟩

theorem coordinateRectangle_negative_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u v : Fin 2 → CutRing)
    (huv : ∀ k, ordinary (u k) ≤ ordinary (v k))
    (hu : ∀ k, -ordinary r < ordinary (u k))
    (hv : ∀ k, ordinary (v k) < ordinary r)
    (hside : ∀ t : ℝ × ℝ,
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) →
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) → cutForm a j t < 0) :
    coordinateRectangle a u v ≤ (clippedSlopePrimitive a r j)ᶜ := by
  intro p hp hpos
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift u v huv
    (fun k => by have h1 := hu k; have h2 := hv k; linarith [hr.2]) p hp
  have hR : (-ordinary r < t.1 ∧ t.1 < ordinary r) ∧
      (-ordinary r < t.2 ∧ t.2 < ordinary r) :=
    ⟨⟨(hu 0).trans_le hx.1,hx.2.trans (hv 0)⟩,
      ⟨(hu 1).trans_le hy.1,hy.2.trans (hv 1)⟩⟩
  have hh := (mem_clippedSlope_lift r j hr p t hR ht).mp hpos
  exact (not_lt_of_ge hh) (hside t hx hy)

theorem northwest_quadrant_sign {a : ℕ} (r s : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hs : 0 < ordinary s ∧ ordinary s < ordinary r) :
    coordinateRectangle a ![-s,0] ![0,s] ≤ clippedSlopePrimitive a r 2 := by
  apply coordinateRectangle_sign r 2 hr
  · intro k; fin_cases k <;> simp <;> linarith [hs.1]
  · intro k; fin_cases k <;> simp <;> linarith [hr.1,hs.2]
  · intro k; fin_cases k <;> simp <;> linarith [hr.1,hs.2]
  · intro t hx hy
    change ordinary (-s) ≤ t.1 ∧ t.1 < ordinary 0 at hx
    change ordinary 0 ≤ t.2 ∧ t.2 < ordinary s at hy
    have hlambda : 0 ≤ Real.goldenRatio^a := pow_nonneg Real.goldenRatio_pos.le _
    have hx' : t.1 ≤ 0 := by simpa using hx.2.le
    have hy' : 0 ≤ t.2 := by simpa using hy.1
    change 0 ≤ t.2-Real.goldenRatio^a*t.1
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hlambda hx').trans hy')

theorem southeast_quadrant_sign {a : ℕ} (r s : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hs : 0 < ordinary s ∧ ordinary s < ordinary r) :
    coordinateRectangle a ![0,-s] ![s,0] ≤ (clippedSlopePrimitive a r 2)ᶜ := by
  apply coordinateRectangle_negative_sign r 2 hr
  · intro k; fin_cases k <;> simp <;> linarith [hs.1]
  · intro k; fin_cases k <;> simp <;> linarith [hr.1,hs.2]
  · intro k; fin_cases k <;> simp <;> linarith [hr.1,hs.2]
  · intro t hx hy
    change ordinary 0 ≤ t.1 ∧ t.1 < ordinary s at hx
    change ordinary (-s) ≤ t.2 ∧ t.2 < ordinary 0 at hy
    have hlambda : 0 ≤ Real.goldenRatio^a := pow_nonneg Real.goldenRatio_pos.le _
    have hx' : 0 ≤ t.1 := by simpa using hx.1
    have hy' : t.2 < 0 := by simpa using hy.2
    change t.2-Real.goldenRatio^a*t.1 < 0
    exact sub_neg.mpr (hy'.trans_le (mul_nonneg hlambda hx'))

end ChartQuadrants

section ChartAction
namespace ActualLawfulTable
variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_same_action (U V W : Set Ω) (he : U ∩ W = V ∩ W) :
    SameActionOn (T.sector U) (T.sector V) (T.sector W).range := by
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  rw [T.sector_split U W s,T.sector_split V W s]
  rw [conj_mul_of_commute _ _ _
    (T.sector_commute (Set.disjoint_left.mpr (by aesop)) s t)]
  rw [conj_mul_of_commute _ _ _
    (T.sector_commute (Set.disjoint_left.mpr (by aesop)) s t)]
  rw [he]
end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_same_action (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U V W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (he : U ⊓ W = V ⊓ W) :
    SameActionOn (B.fullGeometricSector hlarge P h U)
      (B.fullGeometricSector hlarge P h V) (B.fullGeometricSector hlarge P h W).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_same_action
  rw [← resolvedPolygonMask_inter _ U.val W.val hU hW,
    ← resolvedPolygonMask_inter _ V.val W.val hV hW]
  exact congrArg (resolvedPolygonMask (primitiveTests (a := a) (r := r) P))
    (congrArg Subtype.val he)

theorem chart_action_transfer (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U V W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (he : U ⊓ W = V ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hcontrol : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  apply small_control_comparison _ B.c B.constant_aligned B.disjoint_aligned f _ hf hcontrol I.val _ _
    (B.fullGeometricSector_supported (by omega) P h U hU I ⟨s,rfl⟩)
    (B.fullGeometricSector_supported (by omega) P h V hV I ⟨s,rfl⟩)
    (by have hh := I.property.2; simp only [Fintype.card_fin]; omega)
  intro J t
  exact B.fullGeometricSector_same_action (by omega) P h U V W hU hV hW he _ _ ⟨_,rfl⟩

end InitialCoverSystem
end ChartAction

end SimpleAmenable
end
end

end OAI
