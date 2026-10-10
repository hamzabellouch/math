import OAI.Combinatorics.CompleteCrossing.Drawing
import OAI.Combinatorics.Crossing.ClosedPolygonIntersection
import OAI.Combinatorics.Crossing.IntervalSegmentStrict
import OAI.Combinatorics.Crossing.OrderedAffineSubdivision
import OAI.Combinatorics.Crossing.PolygonalArcInjective
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Planar segment geometry, affine parametrizations, and oriented arc directions. -/

section

/-! Generic planar ingredients reused through exact definitions of actual paths. -/
noncomputable section
open Set
open scoped BigOperators Classical

namespace Paper170

theorem segmentPoint_eq (a b : Plane) (t : ℝ) :
    segmentPoint a b t = Zarankiewicz.segmentPoint a b t := rfl

theorem det2_eq (a b : Plane) : det2 a b = Zarankiewicz.det2 a b := rfl

theorem segmentIntersection_eq_segmentCrossingSign (a b c d : Plane) :
    segmentIntersection a b c d = Zarankiewicz.segmentCrossingSign a b c d := by
  simp only [segmentIntersection, segmentPoint_eq, det2_eq,
    Zarankiewicz.segmentCrossingSign, Zarankiewicz.SegmentsCrossProperly]
  by_cases h : ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
      Zarankiewicz.segmentPoint a b s = Zarankiewicz.segmentPoint c d t
  · simp only [h, ite_true, and_true]
    rcases lt_trichotomy (Zarankiewicz.det2 (b-a) (d-c)) 0 with hd | hd | hd
    · simp [hd, ne_of_lt hd, not_lt.mpr hd.le]
    · simp [hd]
    · simp [hd, ne_of_gt hd]
  · simp only [h, ite_false, and_false]

theorem segmentIntersection_swap (a b c d : Plane) :
    segmentIntersection c d a b = -segmentIntersection a b c d := by
  simpa only [segmentIntersection_eq_segmentCrossingSign] using
    Zarankiewicz.segmentCrossingSign_swap a b c d

theorem TransversePolygons.segmentPairTransverse {v w : ℕ → Plane} {n m : ℕ}
    (h : TransversePolygons v w n m) (i : Fin n) (j : Fin m) :
    Zarankiewicz.SegmentPairTransverse (v i.val) (v (i.val+1))
      (w j.val) (w (j.val+1)) := by
  intro s hs t ht he
  have hs0 : s ≠ 0 := by
    intro hz
    subst s
    have hh : v i.val = segmentPoint (w j.val) (w (j.val+1)) t := by
      simpa only [segmentPoint_eq, Zarankiewicz.segmentPoint_zero] using he
    exact h.left_vertices_avoid i.val (Nat.le_of_lt i.isLt) j.val j.isLt t ht hh
  have hs1 : s ≠ 1 := by
    intro hz
    subst s
    have hh : v (i.val+1) = segmentPoint (w j.val) (w (j.val+1)) t := by
      simpa only [segmentPoint_eq, Zarankiewicz.segmentPoint_one] using he
    exact h.left_vertices_avoid (i.val+1) i.isLt j.val j.isLt t ht hh
  have ht0 : t ≠ 0 := by
    intro hz
    subst t
    have hh : w j.val = segmentPoint (v i.val) (v (i.val+1)) s := by
      simpa only [segmentPoint_eq, Zarankiewicz.segmentPoint_zero] using he.symm
    exact h.right_vertices_avoid j.val (Nat.le_of_lt j.isLt) i.val i.isLt s hs hh
  have ht1 : t ≠ 1 := by
    intro hz
    subst t
    have hh : w (j.val+1) = segmentPoint (v i.val) (v (i.val+1)) s := by
      simpa only [segmentPoint_eq, Zarankiewicz.segmentPoint_one] using he.symm
    exact h.right_vertices_avoid (j.val+1) j.isLt i.val i.isLt s hs hh
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hs1⟩
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩
  exact ⟨h.transverse i.val i.isLt j.val j.isLt ⟨s,hs',t,ht',he⟩, hs', ht'⟩

theorem closed_polygon_intersection_zero (v w : ℕ → Plane) (n m : ℕ)
    (hv : v n = v 0) (hw : w m = w 0) (htrans : TransversePolygons v w n m) :
    polygonIntersection v w n m = 0 := by
  simpa only [polygonIntersection, segmentIntersection_eq_segmentCrossingSign,
    Zarankiewicz.polygonIntersection] using
    Zarankiewicz.closed_polygon_intersection_zero v w n m hv hw htrans.segmentPairTransverse

/-- Transfer a genuine affine parametrization, retaining the identical path and knots. -/
def ofZarankiewiczParametrization {a b : Plane} {γ : Path a b}
    (P : Zarankiewicz.PolygonalParametrization γ) : PolygonalParametrization γ where
  pieces := P.pieces
  positive := by
    by_contra hn
    have hp : P.pieces = 0 := by omega
    have hi : (0 : Fin (P.pieces+1)) = Fin.last P.pieces := by
      apply Fin.ext
      exact hp.symm
    have he := P.first.symm.trans ((congrArg P.knot hi).trans P.last)
    exact zero_ne_one he
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := by
    intro i t hlo hhi
    have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
    obtain ⟨u,hu⟩ := Zarankiewicz.intervalSegment_surjective_interval
      (P.knot i.castSucc) (P.knot i.succ) hlt t ⟨hlo,hhi⟩
    have he := P.affine i u
    rw [hu] at he
    have hp := congrArg Subtype.val hu
    have hd : (P.knot i.succ : ℝ) - P.knot i.castSucc ≠ 0 := sub_ne_zero.mpr (ne_of_gt (show (P.knot i.castSucc : ℝ) < P.knot i.succ from hlt))
    have hquot : ((t : ℝ) - P.knot i.castSucc) /
        ((P.knot i.succ : ℝ) - P.knot i.castSucc) = (u : ℝ) := by
      apply (div_eq_iff hd).mpr
      dsimp [Zarankiewicz.intervalSegment] at hp
      nlinarith
    rw [hquot]
    exact he

theorem simple_polygonal_replacement {a b : Plane} (hab : a ≠ b)
    (U : Set Plane) (hU : IsOpen U) (γ : Path a b) (hγ : range γ ⊆ U) :
    ∃ η : Path a b, Function.Injective η ∧ range η ⊆ U ∧
      Nonempty (PolygonalParametrization η) := by
  obtain ⟨P,hP,hPU,_⟩ := Zarankiewicz.exists_simple_polygonalChain_of_path hab γ U hU
    (fun t => hγ ⟨t,rfl⟩)
  obtain ⟨Q⟩ := P.hasFiniteAffineCover.nonempty_polygonalParametrization
  exact ⟨P.path,hP,hPU,⟨ofZarankiewiczParametrization Q⟩⟩

theorem squaredLength_pos {x : Plane} (hx : x ≠ 0) : 0 < squaredLength x := by
  have h0 : 0 ≤ x.1^2 := sq_nonneg x.1
  have h1 : 0 ≤ x.2^2 := sq_nonneg x.2
  change 0 < x.1^2 + x.2^2
  by_contra hh
  have ha : x.1 = 0 := by nlinarith
  have hb : x.2 = 0 := by nlinarith
  exact hx (Prod.ext ha hb)

theorem inversion_involutive : Function.Involutive inversion := by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [inversion, squaredLength]
  · have hq : squaredLength x ≠ 0 := ne_of_gt (squaredLength_pos hx)
    have hlen : squaredLength (inversion x) = (squaredLength x)⁻¹ := by
      change (x.1 / squaredLength x)^2 + (x.2 / squaredLength x)^2 = _
      rw [div_pow, div_pow, ← add_div]
      change squaredLength x / squaredLength x ^ 2 = (squaredLength x)⁻¹
      field_simp [hq]
    rw [inversion, hlen]
    apply Prod.ext <;> simp [inversion, hq]

theorem inversion_fixes_circle (x : Plane) (hx : squaredLength x = 1) : inversion x = x := by
  simp [inversion, hx]

end Paper170

end
end

section

/-! The frozen subdivision and the reused geometric subdivision describe the same path. -/
noncomputable section
open Set
open scoped Classical
namespace Paper170

def toZarankiewiczParametrization {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : Zarankiewicz.PolygonalParametrization γ where
  pieces := P.pieces
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := by
    intro i t
    have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
    have hlohi := Zarankiewicz.intervalSegment_between
      (P.knot i.castSucc) (P.knot i.succ) t hlt.le
    have he := P.affine i _ hlohi.1 hlohi.2
    have hd : (P.knot i.succ : ℝ) - P.knot i.castSucc ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (show (P.knot i.castSucc : ℝ) < P.knot i.succ from hlt))
    have hquot : (((Zarankiewicz.intervalSegment (P.knot i.castSucc) (P.knot i.succ) t :
        unitInterval) : ℝ) - P.knot i.castSucc) /
          ((P.knot i.succ : ℝ) - P.knot i.castSucc) = (t : ℝ) := by
      apply (div_eq_iff hd).mpr
      dsimp [Zarankiewicz.intervalSegment]
      ring
    rw [hquot] at he
    exact he

theorem vertices_toZarankiewicz {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (i : ℕ) :
    (toZarankiewiczParametrization P).vertices i = P.vertices i := rfl

theorem PolygonalParametrization.segment_mem_interior {V E : Type} {G : Graph V E}
    (D : ContinuousDrawing G) (e : E) (P : PolygonalParametrization (D.edge e))
    (i : Fin P.pieces) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    segmentPoint (P.vertices i.val) (P.vertices (i.val+1)) s ∈ edgeInterior D e := by
  let t : unitInterval := ⟨s,hs.1.le,hs.2.le⟩
  let u := Zarankiewicz.intervalSegment (P.knot i.castSucc) (P.knot i.succ) t
  have hlt : P.knot i.castSucc < P.knot i.succ := P.increasing Fin.castSucc_lt_succ
  have hu := Zarankiewicz.intervalSegment_strict_between
    (P.knot i.castSucc) (P.knot i.succ) t hlt (show t ∈ Ioo (0 : unitInterval) 1 from hs)
  refine ⟨u,⟨lt_of_le_of_lt (P.knot i.castSucc).property.1 hu.1,
    lt_of_lt_of_le hu.2 (P.knot i.succ).property.2⟩,?_⟩
  exact (toZarankiewiczParametrization P).segment_formula i t

theorem PolygonalParametrization.vertices_first {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : P.vertices 0 = a :=
  (toZarankiewiczParametrization P).vertices_first

theorem PolygonalParametrization.vertices_last {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) : P.vertices P.pieces = b :=
  (toZarankiewiczParametrization P).vertices_last

theorem PolygonalParametrization.direction_ne_zero {a b : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : ℕ) (hi : i < P.pieces) : P.vertices (i+1) - P.vertices i ≠ 0 :=
  (toZarankiewiczParametrization P).direction_ne_zero hγ i hi

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
open scoped BigOperators
namespace Paper170Geometry

theorem sum_eq_sum_of_unique_match {A B : Type} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) (R : A → B → Prop)
    (hf : ∀a, f a≠0 → ∃!b, g b≠0 ∧ R a b)
    (hg : ∀b, g b≠0 → ∃!a, f a≠0 ∧ R a b)
    (heq : ∀a b, f a≠0 → g b≠0 → R a b → f a=g b) :
    ∑a, f a = ∑b, g b := by
  classical
  have hrow (a : A) : f a = ∑b : B, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 := by
    by_cases ha : f a=0
    · simp [ha]
    · obtain ⟨b, hb, hu⟩ := hf a ha
      symm
      rw [Finset.sum_eq_single b]
      · rw [ite_eq_left ⟨ha, hb.1, hb.2⟩]
      · intro c _ hcb
        have hn : ¬(f a≠0 ∧ g c≠0 ∧ R a c) := fun h => hcb (hu c h.2)
        simp only [ite_eq_right hn]
      · simp
  have hcol (b : B) : (∑a : A, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0) = g b := by
    by_cases hb : g b=0
    · simp [hb]
    · obtain ⟨a, ha, hu⟩ := hg b hb
      rw [Finset.sum_eq_single a]
      · rw [ite_eq_left ⟨ha.1,hb,ha.2⟩]
        exact heq a b ha.1 hb ha.2
      · intro c _ hca
        have hn : ¬(f c≠0 ∧ g b≠0 ∧ R c b) := fun h => hca (hu c ⟨h.1,h.2.2⟩)
        simp only [ite_eq_right hn]
      · simp
  calc
    ∑a, f a = ∑a, ∑b, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 :=
      Finset.sum_congr rfl (fun a _ => hrow a)
    _ = ∑b, ∑a, if f a≠0 ∧ g b≠0 ∧ R a b then f a else 0 := Finset.sum_comm
    _ = ∑b, g b := Finset.sum_congr rfl (fun b _ => hcol b)

theorem segmentCrossingSign_ne_zero_iff (a b c d : Plane) :
    segmentCrossingSign a b c d ≠ 0 ↔ SegmentsCrossProperly a b c d := by
  unfold segmentCrossingSign
  split_ifs <;> simp_all

theorem meeting_of_mem_openSegments (a b c d x : Plane)
    (hx : x∈openSegmentTrace a b) (hy : x∈openSegmentTrace c d) :
    ∃s∈Ioo (0:ℝ) 1, ∃t∈Ioo (0:ℝ) 1, segmentPoint a b s=segmentPoint c d t := by
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  exact ⟨s,hs,t,ht,hsx.trans htx.symm⟩

theorem openSegments_inter_subsingleton (a b c d : Plane) (hdet : det2 (b-a) (d-c)≠0) :
    (openSegmentTrace a b ∩ openSegmentTrace c d).Subsingleton := by
  rintro x ⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩ y ⟨⟨u,hu,huy⟩,⟨v,hv,hvy⟩⟩
  have he := segment_intersection_parameters_unique a b c d hdet s t u v
    (hsx.trans htx.symm) (huy.trans hvy.symm)
  exact hsx.symm.trans ((congrArg (segmentPoint a b) he.1).trans huy)

theorem segmentCrossingSign_eq_of_pos_directions
    (a b c d a' b' c' d' x : Plane) (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (he : b-a=r • (b'-a')) (hf : d-c=s • (d'-c'))
    (hxa : x∈openSegmentTrace a b) (hxc : x∈openSegmentTrace c d)
    (hxa' : x∈openSegmentTrace a' b') (hxc' : x∈openSegmentTrace c' d') :
    segmentCrossingSign a b c d = segmentCrossingSign a' b' c' d' := by
  have hm := meeting_of_mem_openSegments a b c d x hxa hxc
  have hm' := meeting_of_mem_openSegments a' b' c' d' x hxa' hxc'
  simp only [segmentCrossingSign, SegmentsCrossProperly, hm, hm', and_true,
    he, hf, det2_smul_left, det2_smul_right, ne_eq, mul_eq_zero,
    ne_of_gt hr, ne_of_gt hs, false_or, mul_pos_iff_of_pos_left hr,
    mul_pos_iff_of_pos_left hs]

theorem polygonIntersection_eq_fin_sum (v w : ℕ → Plane) (n m : ℕ) :
    polygonIntersection v w n m = ∑i : Fin n, ∑j : Fin m,
      segmentCrossingSign (v i.val) (v (i.val+1)) (w j.val) (w (j.val+1)) := by
  unfold polygonIntersection
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]

end Paper170Geometry

end
end

section

noncomputable section
open Set
namespace Paper170

/-- Two injective paths with the same endpoints and trace have the same orientation. -/
theorem path_reparametrization {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η) :
    ∃ f : unitInterval → unitInterval, Continuous f ∧ StrictMono f ∧
      f 0 = 0 ∧ f 1 = 1 ∧ ∀ t, γ (f t) = η t := by
  let e := (γ.continuous.isClosedEmbedding hγ).isEmbedding.toHomeomorph
  let lift : unitInterval → Set.range γ := fun t =>
    ⟨η t, hrange.symm ▸ Set.mem_range_self t⟩
  let f : unitInterval → unitInterval := fun t => e.symm (lift t)
  have heval (t) : γ (f t) = η t := by
    have h := congrArg Subtype.val (e.apply_symm_apply (lift t))
    exact h
  have hzero : f 0 = 0 := hγ (by simpa using heval 0)
  have hone : f 1 = 1 := hγ (by simpa using heval 1)
  have hc : Continuous f := e.symm.continuous.comp
    (η.continuous.subtype_mk (fun t => hrange.symm ▸ Set.mem_range_self t))
  have hi : Function.Injective f := by
    intro s t hst
    apply hη
    rw [← heval s, ← heval t, hst]
  refine ⟨f, hc, ?_, hzero, hone, heval⟩
  apply hc.strictMono_of_inj_boundedOrder _ hi
  simpa only [show (⊥ : unitInterval) = 0 from rfl,
    show (⊤ : unitInterval) = 1 from rfl, hzero, hone] using
    (show (0 : unitInterval) ≤ 1 from zero_le_one)

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170

lemma intervalSegment_lt_iff {a b p q : unitInterval} (hab : a < b) :
    intervalSegment a b p < intervalSegment a b q ↔ p < q := by
  have hd : 0 < b.val - a.val := sub_pos.mpr hab
  change (1 - p.val) * a.val + p.val * b.val <
    (1 - q.val) * a.val + q.val * b.val ↔ p.val < q.val
  have he : ((1 - q.val) * a.val + q.val * b.val) -
      ((1 - p.val) * a.val + p.val * b.val) =
      (q.val - p.val) * (b.val - a.val) := by ring
  rw [← sub_pos, he, mul_pos_iff_of_pos_right hd, sub_pos]

lemma segmentPoint_sub_segmentPoint (A B : Plane) (p q : ℝ) :
    Paper170.segmentPoint A B q - Paper170.segmentPoint A B p = (q-p) • (B-A) := by
  ext <;> simp [Paper170.segmentPoint] <;> ring

/-- Oriented affine pieces of two parametrizations of the same simple arc have
positively proportional directions whenever they overlap to the right. -/
theorem path_segments_direction {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (p q : unitInterval) (hp : p < 1) (hq : q < 1)
    (hpoint : Paper170.segmentPoint A B p.val = Paper170.segmentPoint C D q.val) :
    ∃ r : ℝ, 0 < r ∧ D-C = r • (B-A) := by
  obtain ⟨f, hc, hf, _, _, heval⟩ := path_reparametrization γ η hγ hη hrange
  let u := intervalSegment a₀ a₁ p
  let v := intervalSegment b₀ b₁ q
  have hmatch : f v = u := hγ (by rw [heval, hηseg, hγseg, hpoint])
  have hu : u < a₁ := by
    simpa [u, intervalSegment] using (intervalSegment_lt_iff ha).mpr hp
  have hv : v < b₁ := by
    simpa [v, intervalSegment] using (intervalSegment_lt_iff hb).mpr hq
  obtain ⟨c, huc, hcmin⟩ := exists_between (lt_min hu (hmatch ▸ hf hv))
  have hfc : f v < c := by rwa [hmatch]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo hv.le hc.continuousOn
    ⟨hfc, (lt_min_iff.mp hcmin).2⟩
  have hctop : c < a₁ := (lt_min_iff.mp hcmin).1
  obtain ⟨p', hp'⟩ := intervalSegment_surjective_interval a₀ a₁ ha c
    ⟨(intervalSegment_between a₀ a₁ p ha.le).1.trans huc.le, hctop.le⟩
  obtain ⟨q', hq'⟩ := intervalSegment_surjective_interval b₀ b₁ hb t
    ⟨(intervalSegment_between b₀ b₁ q hb.le).1.trans ht.1.le, ht.2.le⟩
  have hpp : p < p' := (intervalSegment_lt_iff ha).mp (by simpa [hp'] using huc)
  have hqq : q < q' := (intervalSegment_lt_iff hb).mp (by simpa [hq'] using ht.1)
  have hpoint' : Paper170.segmentPoint A B p'.val =
      Paper170.segmentPoint C D q'.val := by
    rw [← hγseg, ← hηseg, hp', hq', ← hft, heval]
  have heq : (p'.val-p.val) • (B-A) = (q'.val-q.val) • (D-C) := by
    rw [← segmentPoint_sub_segmentPoint, ← segmentPoint_sub_segmentPoint,
      hpoint, hpoint']
  have hα : 0 < p'.val-p.val := sub_pos.mpr hpp
  have hβ : 0 < q'.val-q.val := sub_pos.mpr hqq
  refine ⟨(q'.val-q.val)⁻¹ * (p'.val-p.val), mul_pos (inv_pos.mpr hβ) hα, ?_⟩
  calc
    D-C = (q'.val-q.val)⁻¹ • ((q'.val-q.val) • (D-C)) := by
      rw [smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
    _ = (q'.val-q.val)⁻¹ • ((p'.val-p.val) • (B-A)) := by rw [heq]
    _ = _ := by rw [smul_smul]

/-- Interior overlap is sufficient for the positive direction comparison. -/
theorem path_segments_direction_of_mem {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (x : Plane) (hx : x ∈ openSegmentTrace A B) (hy : x ∈ openSegmentTrace C D) :
    ∃ r : ℝ, 0 < r ∧ D-C = r • (B-A) := by
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨q, hq, hqx⟩ := hy
  exact path_segments_direction γ η hγ hη hrange a₀ a₁ b₀ b₁ ha hb A B C D
    hγseg hηseg ⟨p, hp.1.le, hp.2.le⟩ ⟨q, hq.1.le, hq.2.le⟩ hp.2 hq.2
    (hpx.trans hqx.symm)

end Paper170

end
end

section

noncomputable section
open Set Zarankiewicz
namespace Paper170

lemma reverse_affine_piece {a b : Plane} (γ : Path a b)
    (a₀ a₁ : unitInterval) (A B : Plane)
    (hseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val) :
    ∀t, γ.symm (intervalSegment (unitInterval.symm a₁) (unitInterval.symm a₀) t) =
      Paper170.segmentPoint B A t.val := by
  intro t
  have hi : unitInterval.symm
      (intervalSegment (unitInterval.symm a₁) (unitInterval.symm a₀) t) =
      intervalSegment a₀ a₁ (unitInterval.symm t) := by
    apply Subtype.ext
    simp only [unitInterval.symm, intervalSegment]
    ring
  rw [Path.symm_apply, Function.comp_apply, hi, hseg]
  ext <;> simp [Paper170.segmentPoint, unitInterval.symm] <;> ring

theorem path_final_segments_direction {a b : Plane} (γ η : Path a b)
    (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hrange : Set.range γ = Set.range η)
    (a₀ a₁ b₀ b₁ : unitInterval) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (A B C D : Plane)
    (hγseg : ∀t, γ (intervalSegment a₀ a₁ t) = Paper170.segmentPoint A B t.val)
    (hηseg : ∀t, η (intervalSegment b₀ b₁ t) = Paper170.segmentPoint C D t.val)
    (hpoint : B = D) :
    ∃ r : ℝ, 0 < r ∧ C-D = r • (A-B) := by
  apply path_segments_direction γ.symm η.symm
    (hγ.comp unitInterval.symmHomeomorph.injective)
    (hη.comp unitInterval.symmHomeomorph.injective)
    (by simpa only [Path.symm_range] using hrange)
    (unitInterval.symm a₁) (unitInterval.symm a₀)
    (unitInterval.symm b₁) (unitInterval.symm b₀)
    (unitInterval.symm_lt_symm.mpr ha) (unitInterval.symm_lt_symm.mpr hb)
    B A D C (reverse_affine_piece γ a₀ a₁ A B hγseg)
    (reverse_affine_piece η b₀ b₁ C D hηseg) 0 0
    (by norm_num) (by norm_num)
  simpa [Paper170.segmentPoint] using hpoint

end Paper170

end
end

end OAI
