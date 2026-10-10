import Mathlib
import OAI.Geometry.HyperbolicGroups.FiniteLaw

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace MetricHexagon
variable {X : Type*} [MetricSpace X] {z : Fin 6 → X}

/-- Central log comparison is equality for every pair of hexagon vertices.
This proves the exact flatness used by the obstruction without assuming a
flat-sector theorem or treating the tangent cone as a vector space. -/
theorem log_dist (D : MetricHexagon z) (h : CATZero X) (i j : Fin 6) :
    dist (TangentCone.log h (CATZero.mid h (z 0) (z 3)) (z i))
      (TangentCone.log h (CATZero.mid h (z 0) (z 3)) (z j)) = dist (z i) (z j) := by
  let c := CATZero.mid h (z 0) (z 3)
  let T := TangentCone.coneData h c
  let L := TangentCone.log h c
  obtain ⟨hd, hc⟩ := D.rigidity h
  have hr (k : Fin 6) : dist c (z k) ^ 2 = 3 / 4 := D.radius h k
  have hop : T.Opposite (L (z j)) (L (z (j + 3))) := by
    have hh := TangentCone.opposite_mid_logs h (z j) (z (j + 3))
    rw [hc j] at hh
    exact hh
  have hupper := T.opposite_pairing (TangentCone.catZero h c) hop (L (z i))
  rw [T.pairing_comm (L (z j)), T.pairing_comm (L (z (j + 3)))] at hupper
  have hl := TangentCone.pairing_log_ge h c (z i) (z j)
  have hl' := TangentCone.pairing_log_ge h c (z i) (z (j + 3))
  have hsum : dist (z i) (z j) ^ 2 + dist (z i) (z (j + 3)) ^ 2 = 3 := by
    rw [hd, hd]
    exact_mod_cast hexDistSq_opposite_sum i j
  rw [hr i, hr j] at hl
  rw [hr i, hr (j + 3)] at hl'
  change (3 / 4 + 3 / 4 - dist (z i) (z j) ^ 2) / 2 ≤
    T.pairing (L (z i)) (L (z j)) at hl
  change (3 / 4 + 3 / 4 - dist (z i) (z (j + 3)) ^ 2) / 2 ≤
    T.pairing (L (z i)) (L (z (j + 3))) at hl'
  have hp : T.pairing (L (z i)) (L (z j)) =
      (3 / 2 - dist (z i) (z j) ^ 2) / 2 := by linarith
  have hn (k : Fin 6) : T.normSq (L (z k)) = 3 / 4 := by
    exact (TangentCone.normSq_log h c (z k)).trans (hr k)
  unfold ConeData.pairing at hp
  rw [hn i, hn j] at hp
  change dist (L (z i)) (L (z j)) = dist (z i) (z j)
  nlinarith [dist_nonneg (x := L (z i)) (y := L (z j)), dist_nonneg (x := z i) (y := z j)]

/-- Every central midpoint comparison in the core hexagon is an equality. -/
theorem central_mid (D : MetricHexagon z) (h : CATZero X) (i j : Fin 6) :
    dist (CATZero.mid h (z 0) (z 3)) (CATZero.mid h (z i) (z j)) ^ 2 =
      3 / 4 - (hexDistSq i j : ℝ) / 4 := by
  have he := TangentCone.cn_eq_of_log_dist h (CATZero.mid h (z 0) (z 3)) (z i) (z j)
    (D.log_dist h i j) (t := 1 / 2) (by norm_num)
  rw [D.radius h i, D.radius h j, (D.rigidity h).1 i j] at he
  change dist _ (CATZero.mid h (z i) (z j)) ^ 2 = _ at he
  linarith

end MetricHexagon
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators

/-- Points A,B,C,D followed by the three remaining nonzero vectors. -/
def vector : Fin 7 → Fin 3 → ZMod 2 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,1], ![1,1,0], ![1,0,1], ![0,1,1]]

/-- Lines are the kernels of the seven nonzero linear functionals. -/
def Incident (i l : Fin 7) : Prop := ∑ j, vector i j * vector l j = 0

instance (i l : Fin 7) : Decidable (Incident i l) := inferInstanceAs (Decidable (_ = _))

/-- X representatives occupy 0,...,6 and the four Y representatives 7,...,10. -/
def pointOfRepresentative (r : Fin 11) : Fin 7 :=
  if h : r.val < 7 then ⟨r.val, h⟩ else ⟨r.val - 7, by omega⟩

end IncidenceTemplate
namespace CoreGeometry
open IncidenceTemplate
abbrev Vertex := Fin 11 ⊕ Fin 7
instance : DecidableEq Vertex := instDecidableEqSum

def Adjacent : Vertex → Vertex → Prop
  | .inl r, .inr l => Incident (pointOfRepresentative r) l ∧ (r,l) ≠ (10,4)
  | .inr l, .inl r => Incident (pointOfRepresentative r) l ∧ (r,l) ≠ (10,4)
  | _, _ => False
instance (v w : Vertex) : Decidable (Adjacent v w) := by
  cases v <;> cases w <;> unfold Adjacent <;> infer_instance

def Opposite : Vertex → Vertex → Prop
  | .inl r, .inr l => ¬Incident (pointOfRepresentative r) l
  | .inr l, .inl r => ¬Incident (pointOfRepresentative r) l
  | _, _ => False
instance (v w : Vertex) : Decidable (Opposite v w) := by
  cases v <;> cases w <;> unfold Opposite <;> infer_instance

structure HexagonCode where
  a : Fin 11
  ab : Fin 7
  b : Fin 11
  bc : Fin 7
  c : Fin 11
  ca : Fin 7

def HexagonCode.vertices (H : HexagonCode) : Fin 6 → Vertex :=
  ![.inl H.a, .inr H.ab, .inl H.b, .inr H.bc, .inl H.c, .inr H.ca]

def Valid (H : HexagonCode) : Prop :=
  (∀ i : Fin 6, Adjacent (H.vertices i) (H.vertices (i+1))) ∧
  (∀ i : Fin 6, H.vertices i ≠ H.vertices (i+2)) ∧
  (∀ i : Fin 6, Opposite (H.vertices i) (H.vertices (i+3)))
instance (H : HexagonCode) : Decidable (Valid H) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def centerPair : Fin 44 → Fin 11 × Fin 7 :=
  ![(0,0), (1,1), (1,6), (2,2), (2,6), (2,5), (3,2), (3,0), (3,1), (4,1), (4,0), (4,6), (4,5), (5,2), (5,0), (5,4), (5,6), (6,2), (6,1), (6,5), (6,4), (7,0), (7,5), (7,4), (7,3), (8,1), (8,6), (8,4), (8,3), (9,2), (9,6), (9,5), (9,3), (10,2), (10,0), (10,1), (10,3), (0,5), (0,4), (0,3), (1,4), (1,3), (2,3), (3,3)]

def centerParent : Fin 44 → Fin 44 :=
  ![0, 0, 0, 0, 0, 1, 2, 2, 4, 3, 3, 6, 6, 1, 1, 5, 8, 0, 0, 2, 4, 1, 2, 4, 9, 0, 0, 5, 12, 0, 0, 1, 9, 2, 2, 16, 16, 2, 4, 9, 5, 12, 9, 12]

def centerHex : Fin 44 → HexagonCode :=
  ![⟨0, 2, 1, 0, 2, 1⟩, ⟨1, 2, 0, 1, 2, 0⟩, ⟨1, 2, 0, 6, 6, 0⟩, ⟨2, 1, 0, 2, 1, 0⟩, ⟨2, 1, 0, 6, 6, 0⟩, ⟨2, 0, 1, 5, 5, 1⟩, ⟨3, 5, 1, 2, 0, 6⟩, ⟨3, 5, 1, 0, 6, 6⟩, ⟨3, 4, 2, 1, 0, 6⟩, ⟨4, 4, 2, 1, 0, 2⟩, ⟨4, 4, 2, 0, 1, 2⟩, ⟨4, 4, 3, 6, 0, 2⟩, ⟨4, 4, 3, 5, 1, 2⟩, ⟨5, 5, 1, 2, 0, 1⟩, ⟨5, 5, 1, 0, 2, 1⟩, ⟨5, 1, 2, 4, 3, 5⟩, ⟨5, 5, 3, 6, 0, 1⟩, ⟨6, 6, 0, 2, 1, 0⟩, ⟨6, 6, 0, 1, 2, 0⟩, ⟨6, 0, 1, 5, 3, 6⟩, ⟨6, 0, 2, 4, 3, 6⟩, ⟨7, 2, 1, 0, 2, 1⟩, ⟨7, 2, 1, 5, 3, 6⟩, ⟨7, 1, 2, 4, 3, 6⟩, ⟨7, 2, 4, 3, 5, 1⟩, ⟨8, 2, 0, 1, 2, 0⟩, ⟨8, 2, 0, 6, 6, 0⟩, ⟨8, 0, 2, 4, 3, 5⟩, ⟨8, 2, 4, 3, 5, 5⟩, ⟨9, 1, 0, 2, 1, 0⟩, ⟨9, 1, 0, 6, 6, 0⟩, ⟨9, 0, 1, 5, 5, 1⟩, ⟨9, 4, 4, 3, 5, 1⟩, ⟨10, 5, 1, 2, 0, 6⟩, ⟨10, 5, 1, 0, 6, 6⟩, ⟨10, 5, 5, 1, 0, 6⟩, ⟨10, 5, 5, 3, 6, 6⟩, ⟨0, 2, 1, 5, 3, 6⟩, ⟨0, 1, 2, 4, 3, 6⟩, ⟨0, 2, 4, 3, 5, 1⟩, ⟨1, 0, 2, 4, 3, 5⟩, ⟨1, 2, 4, 3, 5, 5⟩, ⟨2, 4, 4, 3, 5, 1⟩, ⟨3, 4, 4, 3, 5, 5⟩]

def pointIndex : Fin 11 → Fin 44 :=
  ![0, 1, 3, 6, 9, 13, 17, 21, 25, 29, 33]

def lineIndex : Fin 7 → Fin 44 :=
  ![0, 1, 3, 24, 15, 5, 2]

def lineHex : Fin 7 → Fin 7 → HexagonCode :=
  ![![⟨0, 2, 1, 0, 2, 1⟩, ⟨2, 0, 1, 2, 0, 1⟩, ⟨1, 0, 2, 1, 0, 2⟩, ⟨6, 0, 1, 2, 4, 3⟩, ⟨2, 0, 1, 5, 3, 4⟩, ⟨1, 0, 2, 4, 3, 5⟩, ⟨6, 0, 1, 2, 0, 6⟩], ![⟨2, 1, 0, 2, 1, 0⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨0, 1, 2, 0, 1, 2⟩, ⟨5, 1, 0, 2, 4, 3⟩, ⟨2, 1, 0, 6, 3, 4⟩, ⟨5, 1, 0, 2, 1, 5⟩, ⟨0, 1, 2, 4, 3, 6⟩], ![⟨1, 2, 0, 1, 2, 0⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨4, 2, 0, 1, 5, 3⟩, ⟨4, 2, 0, 1, 2, 4⟩, ⟨1, 2, 0, 6, 3, 5⟩, ⟨0, 2, 1, 5, 3, 6⟩], ![⟨6, 3, 4, 2, 1, 0⟩, ⟨5, 3, 4, 2, 0, 1⟩, ⟨4, 3, 5, 1, 0, 2⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨4, 3, 5, 1, 2, 4⟩, ⟨5, 3, 4, 2, 1, 5⟩, ⟨6, 3, 4, 2, 0, 6⟩], ![⟨2, 4, 3, 5, 1, 0⟩, ⟨2, 4, 3, 6, 0, 1⟩, ⟨4, 4, 2, 1, 0, 2⟩, ⟨4, 4, 2, 1, 5, 3⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨3, 4, 2, 0, 1, 5⟩, ⟨3, 4, 2, 1, 0, 6⟩], ![⟨1, 5, 3, 4, 2, 0⟩, ⟨5, 5, 1, 2, 0, 1⟩, ⟨1, 5, 3, 6, 0, 2⟩, ⟨5, 5, 1, 2, 4, 3⟩, ⟨3, 5, 1, 0, 2, 4⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨3, 5, 1, 2, 0, 6⟩], ![⟨6, 6, 0, 2, 1, 0⟩, ⟨0, 6, 3, 4, 2, 1⟩, ⟨0, 6, 3, 5, 1, 2⟩, ⟨6, 6, 0, 2, 4, 3⟩, ⟨3, 6, 0, 1, 2, 4⟩, ⟨3, 6, 0, 2, 1, 5⟩, ⟨0, 2, 1, 0, 2, 1⟩]]


lemma centerHex_valid (n : Fin 44) : Valid (centerHex n) := by
  fin_cases n <;> decide

lemma centerHex_pair (n : Fin 44) :
    (centerHex n).a = (centerPair n).1 ∧ (centerHex n).bc = (centerPair n).2 := by
  fin_cases n <;> decide

lemma centerHex_parent (n : Fin 44) (hn : n ≠ 0) :
    centerParent n < n ∧ (centerHex n).b = (centerPair (centerParent n)).1 ∧
      (centerHex n).ca = (centerPair (centerParent n)).2 := by
  fin_cases n <;> first | contradiction | decide

lemma centerPair_complete : ∀ r l, ¬Incident (pointOfRepresentative r) l →
    ∃ n : Fin 44, centerPair n = (r,l) := by
  decide

lemma pointIndex_correct : ∀ r, (centerPair (pointIndex r)).1 = r := by decide
lemma lineIndex_correct : ∀ l, (centerPair (lineIndex l)).2 = l := by decide

lemma lineHex_valid (l m : Fin 7) (hne : l ≠ m) : Valid (lineHex l m) := by
  fin_cases l <;> fin_cases m <;> first | contradiction | decide

lemma lineHex_coordinates (l m : Fin 7) (hne : l ≠ m) :
    (lineHex l m).ab = l ∧ (lineHex l m).ca = m := by
  fin_cases l <;> fin_cases m <;> first | contradiction | decide

end CoreGeometry
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

/-- Membership of an (unoriented) core edge in the fan over `i`. Adjacency is
imposed separately. The exceptional loose edge belongs to no fan. -/
def InFan (i : Fin 7) : Vertex → Vertex → Prop
  | .inl r, .inr l => pointOfRepresentative r = i ∧ (r,l) ≠ (3,4)
  | .inr l, .inl r => pointOfRepresentative r = i ∧ (r,l) ≠ (3,4)
  | _, _ => False

instance (i : Fin 7) (a b : Vertex) : Decidable (InFan i a b) := by
  cases a <;> cases b <;> unfold InFan <;> infer_instance

lemma Adjacent.symm {a b : Vertex} (hab : Adjacent a b) : Adjacent b a := by
  cases a <;> cases b <;> exact hab

lemma Opposite.symm {a b : Vertex} (hab : Opposite a b) : Opposite b a := by
  cases a <;> cases b <;> exact hab

lemma Adjacent.not_opposite {a b : Vertex} (hab : Adjacent a b) : ¬ Opposite a b := by
  cases a <;> cases b <;> simp_all [Adjacent, Opposite]

/-- The three-edge fan quota, expressed without choosing an orientation for
its fields. With distinct successive fields this says at most two per fan. -/
def ThreeQuota (a b c d : Vertex) : Prop :=
  ∀ i, ¬ (InFan i a b ∧ InFan i b c ∧ InFan i c d)

instance (a b c d : Vertex) : Decidable (ThreeQuota a b c d) :=
  inferInstanceAs (Decidable (∀ _i, ¬ (_ ∧ _ ∧ _)))

lemma threeQuota_of_opposite {a b c d : Vertex}
    (hab : Adjacent a b) (hbc : Adjacent b c) (hcd : Adjacent c d)
    (had : Opposite a d) : ThreeQuota a b c d := by
  intro i hi
  rcases hi with ⟨hi₁, hi₂, hi₃⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Adjacent, Opposite, InFan]

/-- Exactly the core path distances in Proposition `configuration` (i).
The third condition uses distinct fields and the actual fan quota; the
exceptional loose edge is not charged to the D fan. -/
structure MetricCore {X : Type*} [MetricSpace X] (z : Vertex → X) : Prop where
  side : ∀ a b, Adjacent a b → dist (z a) (z b) ^ 2 = 1
  twoStep : ∀ a b c, Adjacent a b → Adjacent b c → a ≠ c →
    dist (z a) (z c) ^ 2 = 2
  threeStep : ∀ a b c d, Adjacent a b → Adjacent b c → Adjacent c d →
    a ≠ c → b ≠ d → ThreeQuota a b c d → 3 ≤ dist (z a) (z d) ^ 2

namespace MetricCore
variable {X : Type*} [MetricSpace X] {z : Vertex → X} (D : MetricCore z)
include D

theorem three_of_opposite {a b c d : Vertex}
    (hab : Adjacent a b) (hbc : Adjacent b c) (hcd : Adjacent c d)
    (had : Opposite a d) : 3 ≤ dist (z a) (z d) ^ 2 := by
  apply D.threeStep a b c d hab hbc hcd
  · intro he
    subst c
    exact hcd.not_opposite had
  · intro he
    subst d
    exact hab.not_opposite had
  · exact threeQuota_of_opposite hab hbc hcd had

theorem hexagon (H : HexagonCode) (hH : Valid H) : MetricHexagon (z ∘ H.vertices) := by
  constructor
  · intro i
    exact D.side _ _ (hH.1 i)
  · intro i
    apply D.twoStep _ (H.vertices (i + 1)) _ (hH.1 i)
    · simpa [add_assoc] using hH.1 (i + 1)
    · exact hH.2.1 i
  · intro i
    apply D.three_of_opposite (hH.1 i)
    · exact hH.1 (i + 1)
    · convert hH.1 (i + 2) using 1 <;> fin_cases i <;> rfl
    · exact hH.2.2 i

/-- A fixed actual opposite pair defines the common center. -/
def center (h : CATZero X) : X := CATZero.mid h (z (.inl 0)) (z (.inr 0))

theorem centerPairs (h : CATZero X) (n : Fin 44) :
    CATZero.mid h (z (.inl (centerPair n).1)) (z (.inr (centerPair n).2)) =
      center (z := z) h := by
  induction n using WellFoundedLT.induction with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rfl
    · obtain ⟨hlt, ha, hb⟩ := centerHex_parent n hn
      have hh := ((D.hexagon (centerHex n) (centerHex_valid n)).rigidity h).2 (2 : Fin 6)
      change CATZero.mid h (z (.inl (centerHex n).b)) (z (.inr (centerHex n).ca)) =
        CATZero.mid h (z (.inl (centerHex n).a)) (z (.inr (centerHex n).bc)) at hh
      rw [ha, hb, (centerHex_pair n).1, (centerHex_pair n).2] at hh
      exact hh.symm.trans (ih (centerParent n) hlt)

theorem hexagon_center (h : CATZero X) (H : HexagonCode) (hH : Valid H) :
    CATZero.mid h (z (H.vertices 0)) (z (H.vertices 3)) = center (z := z) h := by
  have ho := hH.2.2 (0 : Fin 6)
  change ¬ Incident (pointOfRepresentative H.a) H.bc at ho
  obtain ⟨n, hn⟩ := centerPair_complete H.a H.bc ho
  have he := D.centerPairs h n
  rw [hn] at he
  exact he

theorem radius_point (h : CATZero X) (r : Fin 11) :
    dist (center (z := z) h) (z (.inl r)) ^ 2 = 3 / 4 := by
  let H := centerHex (pointIndex r)
  have he := (D.hexagon H (centerHex_valid _)).radius h (0 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (centerHex_valid _)] at he
  change dist (center (z := z) h) (z (.inl (centerHex (pointIndex r)).a)) ^ 2 = _ at he
  rw [(centerHex_pair _).1, pointIndex_correct] at he
  exact he

theorem radius_line (h : CATZero X) (l : Fin 7) :
    dist (center (z := z) h) (z (.inr l)) ^ 2 = 3 / 4 := by
  let H := centerHex (lineIndex l)
  have he := (D.hexagon H (centerHex_valid _)).radius h (3 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (centerHex_valid _)] at he
  change dist (center (z := z) h) (z (.inr (centerHex (lineIndex l)).bc)) ^ 2 = _ at he
  rw [(centerHex_pair _).2, lineIndex_correct] at he
  exact he

theorem line_dist (h : CATZero X) (l m : Fin 7) (hne : l ≠ m) :
    dist (z (.inr l)) (z (.inr m)) ^ 2 = 2 := by
  have he := ((D.hexagon (lineHex l m) (lineHex_valid l m hne)).rigidity h).1
    (1 : Fin 6) (5 : Fin 6)
  change dist (z (.inr (lineHex l m).ab)) (z (.inr (lineHex l m).ca)) ^ 2 = (2 : ℕ) at he
  rw [(lineHex_coordinates _ _ hne).1, (lineHex_coordinates _ _ hne).2] at he
  exact_mod_cast he

theorem line_flat (h : CATZero X) (l m : Fin 7) (hne : l ≠ m) :
    dist (center (z := z) h) (CATZero.mid h (z (.inr l)) (z (.inr m))) ^ 2 = 1 / 4 := by
  let H := lineHex l m
  have he := (D.hexagon H (lineHex_valid l m hne)).central_mid h (1 : Fin 6) (5 : Fin 6)
  simp only [Function.comp_apply] at he
  rw [D.hexagon_center h H (lineHex_valid l m hne)] at he
  change dist (center (z := z) h)
    (CATZero.mid h (z (.inr (lineHex l m).ab)) (z (.inr (lineHex l m).ca))) ^ 2 =
      3 / 4 - (2 : ℕ) / 4 at he
  rw [(lineHex_coordinates _ _ hne).1, (lineHex_coordinates _ _ hne).2] at he
  norm_num at he ⊢
  exact he

end MetricCore
end CoreGeometry
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

def xRep : Fin 4 → Fin 11 := ![0,1,2,3]
def yRep : Fin 4 → Fin 11 := ![7,8,9,10]
/-- AB, AC, AD, BC, BD, CD in the fixed linear-functional indexing. -/
def sixLine : Fin 6 → Fin 7 := ![2,1,6,0,5,4]

lemma sixLine_injective : Function.Injective sixLine := by decide
lemma xy_distinct (i : Fin 4) : xRep i ≠ yRep i := by fin_cases i <;> decide
lemma fullLines_x (i : Fin 4) (a : Fin 6) (ha : a ∈ fullLines i) :
    Adjacent (.inl (xRep i)) (.inr (sixLine a)) := by
  fin_cases i <;> fin_cases a <;> first | (solve | simp [fullLines] at ha) | decide
lemma fullLines_y (i : Fin 4) (a : Fin 6) (ha : a ∈ fullLines i) :
    Adjacent (.inl (yRep i)) (.inr (sixLine a)) := by
  fin_cases i <;> fin_cases a <;> first | (solve | simp [fullLines] at ha) | decide

/-- The three-field, two-fractional-geodesic inequality in the source's
configuration proposition, at the exceptional missing incidence. -/
def ExceptionalTest {X : Type*} [MetricSpace X] (h : CATZero X) (z : Vertex → X) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    t ^ 2 * (1 / 2 + 1) ≤
      dist (CATZero.segment h (z (.inr 4)) (CATZero.mid h (z (.inl 2)) (z (.inl 9))) t)
        (CATZero.segment h (z (.inr 4)) (z (.inl 3)) t) ^ 2

namespace MetricCore
variable {X : Type*} [MetricSpace X] {z : Vertex → X} (D : MetricCore z)

/-- Assemble the source's actual graph configuration, rather than assuming
common centers or tangent-cone distances, into the proved obstruction. -/
def toObstruction (h : CATZero X) (he : ExceptionalTest h z) : FiniteObstructionData h where
  c := center (z := z) h
  x := fun i => z (.inl (xRep i))
  y := fun i => z (.inl (yRep i))
  line := fun i => z (.inr (sixLine i))
  radiusX := fun i => D.radius_point h (xRep i)
  radiusY := fun i => D.radius_point h (yRep i)
  radiusLine := fun i => D.radius_line h (sixLine i)
  lineDist := fun a b hab => D.line_dist h _ _ (sixLine_injective.ne hab)
  lineFlat := fun a b hab => D.line_flat h _ _ (sixLine_injective.ne hab)
  square := by
    intro i a b ha hb hab
    constructor
    · exact D.side _ _ (fullLines_x i a ha)
    · exact D.side _ _ (fullLines_y i a ha).symm
    · exact D.side _ _ (fullLines_y i b hb)
    · exact D.side _ _ (fullLines_x i b hb).symm
    · exact D.twoStep _ _ _ (fullLines_x i a ha) (fullLines_y i a ha).symm
        (by simpa only [ne_eq, Sum.inl.injEq] using xy_distinct i)
    · exact D.line_dist h _ _ (sixLine_injective.ne hab)
  twoStepX := D.twoStep (.inl 2) (.inr 4) (.inl 3) (by decide) (by decide) (by decide)
  twoStepY := D.twoStep (.inl 9) (.inr 4) (.inl 3) (by decide) (by decide) (by decide)
  loose := D.side (.inr 4) (.inl 3) (by decide)
  missing := D.threeStep (.inl 10) (.inr 6) (.inl 3) (.inr 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  fractional := he

include D

/-- No CAT(0) space contains the exact limiting core configuration of
Proposition `configuration`, including its exceptional fractional test. -/
theorem impossible (h : CATZero X) (he : ExceptionalTest h z) : False :=
  no_finite_obstruction h (D.toObstruction h he)

end MetricCore
end CoreGeometry
end HyperbolicObstruction


noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction
namespace MetricScale
universe u
@[ext] structure Space (r : ℝ) (hr : 0 < r) (X : Type u) where
  val : X

variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

instance : MetricSpace (Space r hr X) where
  dist x y := r * dist x.val y.val
  dist_self x := by simp
  dist_comm x y := by simp only [dist_comm]
  dist_triangle x y z := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left
      (dist_triangle x.val y.val z.val) hr.le
  eq_of_dist_eq_zero {x y} h := by
    apply Space.ext
    exact dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hr.ne')

lemma dist_eq (x y : Space r hr X) : dist x y = r * dist x.val y.val := rfl

variable (h : CATZero X)
include h

theorem catZero : CATZero (Space r hr X) := by
  intro x y
  refine ⟨fun t => ⟨CATZero.segment h x.val y.val t⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).1
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).2.1
  · intro s hs t ht
    change r * dist (CATZero.segment h x.val y.val s) (CATZero.segment h x.val y.val t) =
      |s - t| * (r * dist x.val y.val)
    rw [CATZero.segment_dist h _ _ hs ht]
    ring
  · intro z t ht
    have hi := mul_le_mul_of_nonneg_left (CATZero.segment_cn h x.val y.val z.val ht)
      (sq_nonneg r)
    simp only [dist_eq]
    nlinarith only [hi]

lemma val_segment (x y : Space r hr X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (CATZero.segment (catZero h) x y t).val = CATZero.segment h x.val y.val t := by
  let z : Space r hr X := ⟨CATZero.segment h x.val y.val t⟩
  have he : z = CATZero.segment (catZero h) x y t := by
    apply CATZero.eq_segment_of_dist (catZero h) ht
    · change r * dist x.val (CATZero.segment h x.val y.val t) = t * (r * dist x.val y.val)
      rw [CATZero.segment_left h _ _ ht]
      ring
    · change r * dist (CATZero.segment h x.val y.val t) y.val = (1 - t) * (r * dist x.val y.val)
      rw [CATZero.segment_right h _ _ ht]
      ring
  exact congrArg Space.val he.symm

end MetricScale


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
