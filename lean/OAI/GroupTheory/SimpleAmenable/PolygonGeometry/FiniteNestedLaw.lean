import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.StarAtomLaw
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricCharts
import OAI.GroupTheory.SimpleAmenable.CentralCovers.UniformTangentTransport

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteNestedLaw
variable {E H Q : Type*} [Group E] [Group H] [Group Q]

theorem prefix_range_le_differences (f : E →* H) (l h : ℕ → E →* H)
    (hf : ∀ i s, f s = l i s*h i s)
    (hc : ∀ i j, i ≤ j → ∀ s t, Commute (l i s) (h j t))
    (hl : l 0 = 1) (N : ℕ) (j : ℕ) (hj : j ≤ N) :
    (l j).range ≤ ⨆ i : Fin N, (cutDifference f l h hf hc i.val).range := by
  let K : Subgroup H := ⨆ i : Fin N, (cutDifference f l h hf hc i.val).range
  rintro x ⟨s,rfl⟩
  have he := cutDifference_telescope f l h hf hc j s
  rw [hl] at he
  simp only [MonoidHom.one_apply,inv_one,one_mul] at he
  rw [← he]
  apply K.list_prod_mem
  intro y hy
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
  have hi' : i < j := List.mem_range.mp hi
  exact (le_iSup (fun i : Fin N => (cutDifference f l h hf hc i.val).range)
    ⟨i,by omega⟩) ⟨s,rfl⟩

theorem centralOn_of_nested_star_cuts (q : H →* Q)
    (N : ℕ) (v : (Fin N → E) →* Q) (hv : Function.Injective v)
    (f : UniversalExtension E →* H) (l h : ℕ → UniversalExtension E →* H)
    (hf : ∀ i s, f s = l i s*h i s)
    (hc : ∀ i j, i ≤ j → ∀ s t, Commute (l i s) (h j t))
    (hl : l 0 = 1)
    (hproj : ∀ i : Fin N, q.comp (cutDifference f l h hf hc i.val) =
      (v.comp (sectorMask {i})).comp (universalProjection E)) :
    CentralOn q (⨆ j : Fin (N+1), (l j.val).range) := by
  have hpair : Pairwise fun i j : Fin N => ∀ s t,
      Commute (cutDifference f l h hf hc i.val s) (cutDifference f l h hf hc j.val t) := by
    intro i j hij s t
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact cutDifference_pairwise f l h hf hc i.val j.val hij s t
    · exact (cutDifference_pairwise f l h hf hc j.val i.val hij t s).symm
  have hcentral := centralOn_of_star_atoms q v hv (fun i : Fin N => cutDifference f l h hf hc i.val) hpair hproj
  apply hcentral.mono
  apply iSup_le
  intro j
  exact prefix_range_le_differences f l h hf hc hl N j.val (by omega)

end FiniteNestedLaw

section CommonContainingWindows

theorem source_chart_containing_window (n t : ℕ) (p z v : ℤ) (b d : ℕ)
    (hv : p ≤ v ∧ v < p+t)
    (hz : (z-v).natAbs ≤ d)
    (hsize : t+2*d+2*b+2 ≤ n) :
    p ⊓ (z-(b:ℤ)) ≤ p ∧ p+t ≤ (p ⊓ (z-(b:ℤ)))+n ∧
    p ⊓ (z-(b:ℤ)) ≤ z-(b:ℤ) ∧
    z-(b:ℤ)+(2*b+2:ℕ) ≤ (p ⊓ (z-(b:ℤ)))+n := by
  have hh : |z-v| ≤ (d:ℤ) := by
    simpa only [Int.natCast_natAbs] using (show ((z-v).natAbs:ℤ) ≤ (d:ℤ) by exact_mod_cast hz)
  have ha := abs_le.mp hh
  have hn : (t:ℤ)+2*(d:ℤ)+2*(b:ℤ)+2 ≤ (n:ℤ) := by exact_mod_cast hsize
  constructor
  · exact inf_le_left
  constructor
  · rw [min_def]
    split_ifs <;> omega
  constructor
  · exact inf_le_right
  · rw [min_def]
    split_ifs <;> omega

theorem fixed_chart_margin_eventually (b : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n*9/10+2*b+2 ≤ n := by
  refine ⟨20*b+20,?_⟩
  intro n hn
  have hh := Nat.mul_div_le (n*9) 10
  omega

theorem transverse_chart_margin_eventually (b : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n/4+2*(n/10+1)+2*b+2 ≤ n := by
  refine ⟨20*b+40,?_⟩
  intro n hn
  have h₀ := Nat.mul_div_le n 4
  have h₁ := Nat.mul_div_le n 10
  omega

end CommonContainingWindows

section QuadrantControl

def signQuadrantLower (s : CutRing) (d : Fin 2) (positive : Bool) (j : Fin 2) : CutRing :=
  if positive then (if j=d then -s else 0) else (if j=d then 0 else -s)

def signQuadrantUpper (s : CutRing) (d : Fin 2) (positive : Bool) (j : Fin 2) : CutRing :=
  if positive then (if j=d then 0 else s) else (if j=d then s else 0)

theorem signQuadrant_side {a : ℕ} (r s : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hs : 0 < ordinary s ∧ ordinary s < ordinary r) (d : Fin 2) (positive : Bool) :
    coordinateRectangle a (signQuadrantLower s d positive) (signQuadrantUpper s d positive) ≤
      if positive then clippedSlopePrimitive a r (slopeDirection d)
      else (clippedSlopePrimitive a r (slopeDirection d))ᶜ := by
  have hSlope : 0 ≤ Real.goldenRatio^a := pow_nonneg Real.goldenRatio_pos.le _
  cases positive with
  | true =>
    apply coordinateRectangle_sign r (slopeDirection d) hr
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower,signQuadrantUpper] <;> linarith [hs.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower] <;> linarith [hs.2,hr.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantUpper] <;> linarith [hs.2,hr.1]
    · intro t hx hy
      fin_cases d
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change 0 ≤ t.2-Real.goldenRatio^a*t.1
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hSlope hx.2.le).trans hy.1)
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change 0 ≤ t.1-Real.goldenRatio^a*t.2
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hSlope hy.2.le).trans hx.1)
  | false =>
    apply coordinateRectangle_negative_sign r (slopeDirection d) hr
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower,signQuadrantUpper] <;> linarith [hs.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower] <;> linarith [hs.2,hr.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantUpper] <;> linarith [hs.2,hr.1]
    · intro t hx hy
      fin_cases d
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change t.2-Real.goldenRatio^a*t.1 < 0
        exact sub_neg.mpr (hy.2.trans_le (mul_nonneg hSlope hx.1))
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change t.1-Real.goldenRatio^a*t.2 < 0
        exact sub_neg.mpr (hx.2.trans_le (mul_nonneg hSlope hy.1))

theorem coordinateRectangle_mono {a : ℕ} (L V l v : Fin 2 → CutRing)
    (hL : ∀ j, ordinary (l j) ≤ ordinary (L j))
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hV : ∀ j, ordinary (V j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1) :
    coordinateRectangle a L V ≤ coordinateRectangle a l v := by
  exact inf_le_inf (coordinateInterval_mono 0 _ _ _ _ (hL 0) (hLV 0) (hV 0) (hlen 0))
    (coordinateInterval_mono 1 _ _ _ _ (hL 1) (hLV 1) (hV 1) (hlen 1))

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem rectangle_control_from_axes (hlarge : 15 < m+1)
    (n : ℕ) (g : B.CoordinateWindowLaw n)
    (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p q : Fin 2 → ℤ)
    (hp : ∀ j, q j ≤ p j) (hq : ∀ j, p j+t j ≤ q j+n)
    (L V : Fin 2 → CutRing)
    (hL : ∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j)
    (hV : ∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hc : ∀ j, SmallControlled B.c f
      (B.axisSector hlarge n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) :
    SmallControlled B.c f (B.windowSector hlarge n g q (coordinateRectangle a L V)) := by
  have hsmall (j : Fin 2) := axisInterval_resolved (a := a) (r := r)
    j (t j) (p j) (L j) (V j) (hL j) (hV j)
  have hlargeL (j : Fin 2) : q j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < q j+n := by
    have hh := hL j; have hh' := hp j; have hh'' := hq j; omega
  have hlargeV (j : Fin 2) : q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+n := by
    have hh := hV j; have hh' := hp j; have hh'' := hq j; omega
  have he (j : Fin 2) := B.axisSector_in_window hlarge n g j (t j) (ht j) (p j) q
    (hp j) (hq j) (coordinateInterval a j (L j) (V j)) (hsmall j)
  change SmallControlled B.c f (B.fullGeometricSector hlarge _ _
    (coordinateInterval a 0 (L 0) (V 0) ⊓ coordinateInterval a 1 (L 1) (V 1)))
  apply B.fullGeometricSector_intersection_control hlarge _ _ _ _
    (coordinateInterval_window n q 0 _ _ (hlargeL 0) (hlargeV 0))
    (coordinateInterval_window n q 1 _ _ (hlargeL 1) (hlargeV 1)) f
  · change SmallControlled B.c f (B.windowSector hlarge n g q (coordinateInterval a 0 (L 0) (V 0)))
    rw [← he 0]; exact hc 0
  · change SmallControlled B.c f (B.windowSector hlarge n g q (coordinateInterval a 1 (L 1) (V 1)))
    rw [← he 1]; exact hc 1

theorem tangentSign_quadrant_control (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    (n : ℕ) (g : B.CoordinateWindowLaw n)
    (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p q : Fin 2 → ℤ)
    (hp : ∀ j, q j ≤ p j) (hq : ∀ j, p j+t j ≤ q j+n)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool)
    (hstart : ∀ j, q j ≤ pointLabel z j+symmetricWindowStart s j)
    (hend : ∀ j, pointLabel z j+symmetricWindowStart s j+symmetricWindowLength s ≤ q j+n)
    (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hL : ∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j)
    (hV : ∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j)
    (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (L j))
    (hup : ∀ j, ordinary (V j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : ∀ j, SmallControlled B.c f
      (B.axisSector (by omega) n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) :
    SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
      (symmetricWindowStart s) u h d z positive) := by
  have hlab (j : Fin 2) :
      symmetricWindowStart s j ≤ endpointLabel (signQuadrantLower s d positive j) ∧
      endpointLabel (signQuadrantLower s d positive j) < symmetricWindowStart s j+symmetricWindowLength s := by
    unfold signQuadrantLower
    split <;> split <;> first | exact (symmetricWindow_labels s j).1 | exact (symmetricWindow_labels s j).2.1
  have hvab (j : Fin 2) :
      symmetricWindowStart s j ≤ endpointLabel (signQuadrantUpper s d positive j) ∧
      endpointLabel (signQuadrantUpper s d positive j) < symmetricWindowStart s j+symmetricWindowLength s := by
    unfold signQuadrantUpper
    split <;> split <;> first | exact (symmetricWindow_labels s j).2.1 | exact (symmetricWindow_labels s j).2.2
  apply B.tangentSign_control_from_rectangle hlarge _ _ u h n g q d z positive hstart hend
    _ _ hlab hvab (signQuadrant_side r s hr hs d positive) (coordinateRectangle a L V) ?_ f hf
    (B.rectangle_control_from_axes (by omega) n g t ht p q hp hq L V hL hV f hc)
  rw [spatialTranslate_coordinateRectangle]
  apply coordinateRectangle_mono L V _ _
  · intro j; simpa only [map_add,pointCoordinate] using hlo j
  · exact hLV
  · intro j; simpa only [map_add,pointCoordinate] using hup j
  · intro j
    simp only [map_add,add_sub_add_right_eq_sub]
    unfold signQuadrantUpper signQuadrantLower
    split <;> split <;> simp only [map_zero,map_neg] <;> linarith [hs.2,hr.2]

end InitialCoverSystem
end QuadrantControl

end SimpleAmenable
end
end

end OAI
