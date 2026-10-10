import OAI.Combinatorics.CompleteCrossing.Plane
import OAI.Combinatorics.Crossing.FiniteAffineCover

namespace OAI

/-! Affine polygonal subdivisions and chain parametrizations. -/

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

/-- An affine cover retaining its actual interval endpoints. -/
structure AffineCoverData {a b : Plane} (γ : Path a b) where
  intervals : Finset (unitInterval × unitInterval)
  ordered : ∀ ab ∈ intervals, ab.1 < ab.2
  cover : ∀ t : unitInterval, ∃ ab ∈ intervals, ab.1 ≤ t ∧ t ≤ ab.2
  affine : ∀ ab ∈ intervals, ∀ t : unitInterval,
    γ (intervalSegment ab.1 ab.2 t) = Zarankiewicz.segmentPoint (γ ab.1) (γ ab.2) t.val

def AffineCoverData.segment (a b : Plane) : AffineCoverData (Path.segment a b) where
  intervals := {(0,1)}
  ordered := by
    intro ab hab
    have h : ab = (0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  cover := fun t => ⟨(0,1), Finset.mem_singleton_self _, t.property⟩
  affine := by
    intro ab hab t
    have h : ab = (0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one, Path.source, Path.target, Path.segment_apply,
      AffineMap.lineMap_apply_module, Zarankiewicz.segmentPoint]

def AffineCoverData.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (S : AffineCoverData γ) (T : AffineCoverData η) : AffineCoverData (γ.trans η) where
  intervals := S.intervals.image (fun ab => (intervalLeft ab.1, intervalLeft ab.2)) ∪
    T.intervals.image (fun ab => (intervalRight ab.1, intervalRight ab.2))
  ordered := by
    intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (S.ordered cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (T.ordered cd hcd)
  cover := by
    intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val, by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := S.cover u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨(intervalLeft ab.1,intervalLeft ab.2),
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩), ?_, ?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [←hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [←hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1, by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := T.cover u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨(intervalRight ab.1,intervalRight ab.2),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩), ?_, ?_⟩
      · change intervalRight ab.1 ≤ t
        rw [←hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [←hu]
        exact intervalRight_strictMono.monotone hb
  affine := by
    intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      rw [intervalSegment_left, path_trans_intervalLeft, path_trans_intervalLeft, path_trans_intervalLeft]
      exact S.affine cd hcd t
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      rw [intervalSegment_right, path_trans_intervalRight, path_trans_intervalRight, path_trans_intervalRight]
      exact T.affine cd hcd t

lemma AffineCoverData.trans_endpoints {a b c : Plane} {γ : Path a b} {η : Path b c}
    (S : AffineCoverData γ) (T : AffineCoverData η) (B : Set Plane)
    (hS : ∀ ab ∈ S.intervals, γ ab.1 ∈ B ∧ γ ab.2 ∈ B)
    (hT : ∀ ab ∈ T.intervals, η ab.1 ∈ B ∧ η ab.2 ∈ B) :
    ∀ ab ∈ (S.trans T).intervals, (γ.trans η) ab.1 ∈ B ∧ (γ.trans η) ab.2 ∈ B := by
  intro ab hab
  rcases Finset.mem_union.mp hab with hab | hab
  · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
    simpa only [path_trans_intervalLeft] using hS cd hcd
  · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
    simpa only [path_trans_intervalRight] using hT cd hcd

lemma AffineCoverData.subdivision {a b : Plane} {γ : Path a b}
    (S : AffineCoverData γ) (B : Set Plane) (ha : a ∈ B) (hb : b ∈ B)
    (hS : ∀ ab ∈ S.intervals, γ ab.1 ∈ B ∧ γ ab.2 ∈ B) :
    ∃ P : PolygonalParametrization γ, ∀ i, γ (P.knot i) ∈ B := by
  let T : Finset unitInterval := insert 0 (insert 1 (S.intervals.image Prod.fst ∪ S.intervals.image Prod.snd))
  obtain ⟨k, _, t, ht, h0, h1, hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S.intervals) : ab.1 ∈ range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S.intervals) : ab.2 ∈ range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩)))
  let P : Zarankiewicz.PolygonalParametrization γ := {
    pieces := k
    knot := t
    increasing := ht
    first := h0
    last := h1
    affine := by
      intro i u
      let mid : unitInterval := ⟨1/2, by norm_num⟩
      let z := intervalSegment (t i.castSucc) (t i.succ) mid
      have hz : t i.castSucc < z ∧ z < t i.succ :=
        intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
          constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
      obtain ⟨ab,hab,ha,hb⟩ := S.cover z
      have hlo : ab.1 ≤ t i.castSucc := by
        by_contra hn
        obtain ⟨j,hj⟩ := hleft ab hab
        exact strictMono_no_between_successors t ht i j
          ⟨by rw [hj]; exact lt_of_not_ge hn, by rw [hj]; exact ha.trans_lt hz.2⟩
      have hhi : t i.succ ≤ ab.2 := by
        by_contra hn
        obtain ⟨j,hj⟩ := hright ab hab
        exact strictMono_no_between_successors t ht i j
          ⟨by rw [hj]; exact hz.1.trans_le hb, by rw [hj]; exact lt_of_not_ge hn⟩
      have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
      exact path_affine_restrict γ ab.1 ab.2 (S.ordered ab hab) (S.affine ab hab)
        (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u }
  refine ⟨ofZarankiewiczParametrization P, ?_⟩
  intro i
  have hi : t i ∈ T := by
    change t i ∈ (T : Set unitInterval)
    rw [←hR]
    exact ⟨i,rfl⟩
  simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with hi | hi | ⟨ab,hab,hi⟩ | ⟨ab,hab,hi⟩
  · change γ (t i) ∈ B
    simpa [hi] using ha
  · change γ (t i) ∈ B
    simpa [hi] using hb
  · change γ (t i) ∈ B
    simpa only [←hi] using (hS ab hab).1
  · change γ (t i) ∈ B
    simpa only [←hi] using (hS ab hab).2

end Paper170

end
end

section

noncomputable section
open Set
open Zarankiewicz
open scoped Classical
namespace Paper170

lemma polygonalArcPath_safe_cover (v : ℕ → Plane) (B : Set Plane) (n : ℕ)
    (hn : 0 < n) (hv : ∀ i, i ≤ n → v i ∈ B) :
    ∃ S : AffineCoverData (polygonalArcPath v n),
      ∀ ab ∈ S.intervals, polygonalArcPath v n ab.1 ∈ B ∧ polygonalArcPath v n ab.2 ∈ B := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        refine ⟨AffineCoverData.segment (v 0) (v 1), ?_⟩
        intro ab hab
        have he : ab = (0,1) := Finset.mem_singleton.mp hab
        subst ab
        exact ⟨by simpa only [polygonalArcPath, Path.source] using hv 0 (by omega),
          by simpa only [polygonalArcPath, Path.target] using hv 1 le_rfl⟩
      | succ n =>
        obtain ⟨S,hS⟩ := ih (n+1) (by omega) (by omega) (fun i hi => hv i (by omega))
        let T := AffineCoverData.segment (v (n+1)) (v (n+2))
        refine ⟨S.trans T, S.trans_endpoints T B hS ?_⟩
        intro ab hab
        have he : ab = (0,1) := Finset.mem_singleton.mp hab
        subst ab
        exact ⟨by simpa only [Path.source] using hv (n+1) (by omega),
          by simpa only [Path.target] using hv (n+2) le_rfl⟩

def PolygonalParametrization.cast {a b c d : Plane} {γ : Path a b}
    (P : PolygonalParametrization γ) (ha : c = a) (hb : d = b) :
    PolygonalParametrization (γ.cast ha hb) where
  pieces := P.pieces
  positive := P.positive
  knot := P.knot
  increasing := P.increasing
  first := P.first
  last := P.last
  affine := P.affine

lemma chain_subdivision_avoiding {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) (hP : 0 < P.pieces) (B : Set Plane)
    (hv : ∀ i, i ≤ P.pieces → P.vertices i ∈ B) :
    ∃ Q : PolygonalParametrization P.path, ∀ i, P.path (Q.knot i) ∈ B := by
  obtain ⟨S,hS⟩ := polygonalArcPath_safe_cover P.vertices B P.pieces hP hv
  obtain ⟨Q,hQ⟩ := S.subdivision B (hv 0 (Nat.zero_le _)) (hv _ le_rfl) hS
  exact ⟨Q.cast P.first.symm P.last.symm, hQ⟩

end Paper170

end
end

end OAI
