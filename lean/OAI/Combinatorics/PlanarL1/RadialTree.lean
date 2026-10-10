import OAI.Combinatorics.PlanarL1.Distance
import OAI.Combinatorics.PlanarL1.Interpolation

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)

namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-! ### The actual radial-node tree and its interpolation formulas
The geometric data below use precisely the thin-band constants. Nodes and their
parent maps are induced-graph components, not an assumed abstract hierarchy. -/

structure RadialTree where
  base : M.Point J root
  δ : ℝ
  a : ℝ
  ζ : ℝ
  delta_pos : 0 < δ
  width_pos : 0 < a
  zeta_pos : 0 < ζ
  zeta_lt_one : ζ < 1
  width_bound : a ≤ ζ * δ / 1000000
  half_width : ∀ T ∈ J, |base.height - T| ≤ a / 2
  closed_band : IsClosed J
  interval_band : Set.OrdConnected J

namespace RadialTree

variable (R : RadialTree (M := M) (J := J) (root := root))

def Node (k : ℕ) :=
  ((M.activeGraph J).induce
    (R.base.superlevel R.base.height R.base.inBand (k * R.δ))).ConnectedComponent

lemma width_small : R.a < R.δ / 1000 := by
  have h := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  nlinarith [R.width_bound, R.delta_pos]

lemma superlevel_antitone {k m : ℕ} (hkm : k ≤ m) :
    R.base.superlevel R.base.height R.base.inBand (m * R.δ) ⊆
      R.base.superlevel R.base.height R.base.inBand (k * R.δ) := by
  rintro i ⟨hr, hi⟩
  refine ⟨hr, le_trans ?_ hi⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) R.delta_pos.le

def parent {k : ℕ} (C : R.Node (k + 1)) : R.Node k :=
  ColumnOrder.componentAbove (R.superlevel_antitone (Nat.le_succ k)) C

lemma mem_parent {k : ℕ} (C : R.Node (k + 1)) :
    ColumnOrder.componentColumns C ⊆ ColumnOrder.componentColumns (R.parent C) :=
  ColumnOrder.componentColumns_above _ C

noncomputable def portals {k : ℕ} (C : R.Node k) :
    R.base.PortalData R.base.height R.base.inBand R.a (k * R.δ) C :=
  Classical.choice (R.base.portalData_nonempty R.closed_band R.base.inBand rfl
    R.width_pos R.half_width (by
      by_cases hk : k = 0
      · left; simp [hk]
      · right
        have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
        have hw := R.width_small
        nlinarith [mul_le_mul_of_nonneg_right hk' R.delta_pos.le, R.delta_pos]) C)

lemma parent_near {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    min (dist v (R.portals (R.parent C)).left)
      (dist v (R.portals (R.parent C)).right) ≤ R.δ + 220 * R.a := by
  have hm : v.column ∈ ColumnOrder.componentColumns (R.parent C) := by
    apply R.mem_parent C
    rcases hv with rfl | rfl
    · exact (R.portals C).left_mem
    · exact (R.portals C).right_mem
  have hr : dist R.base v < (k : ℝ) * R.δ + R.δ + R.a := by
    rcases hv with rfl | rfl
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).left_radial.2
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).right_radial.2
  linarith [(R.portals (R.parent C)).near_of_radial v hm hr.le, R.width_pos]

lemma parent_separated {k : ℕ} (C : R.Node (k + 1)) (u v : M.Point J root)
    (hu : u = (R.portals (R.parent C)).left ∨ u = (R.portals (R.parent C)).right)
    (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    R.δ - 10 * R.a ≤ dist u v := by
  have hr : dist R.base u < (k : ℝ) * R.δ + R.a := by
    rcases hu with rfl | rfl
    · exact (R.portals (R.parent C)).left_radial.2
    · exact (R.portals (R.parent C)).right_radial.2
  have hs : (k : ℝ) * R.δ + R.δ ≤ dist R.base v := by
    rcases hv with rfl | rfl
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).left_radial.1
    · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        (R.portals C).right_radial.1
  linarith [dist_triangle R.base u v, R.width_pos]

/-- Atom names use depth, portal column and type. Equal portals therefore have
one name and one noise, including the root's single tentative atom. -/
def atomName (k : ℕ) (v : M.Point J root) (j : Fin 3) : ℕ :=
  3 * (n * k + v.column.val) + j.val

lemma atomName_bounds (k : ℕ) (v : M.Point J root) (j : Fin 3) :
    3 * n * k ≤ atomName k v j ∧ atomName k v j < 3 * n * (k + 1) := by
  simp only [atomName, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  have := v.column.isLt
  have := j.isLt
  constructor <;> omega

/-- A complete noise assignment. Bounds and independence are imposed on the
actual probability space later, not assumed properties of the output. -/
abbrev Noise := ℕ → Fin n → Fin 3 → ℝ

open Interpolation

noncomputable def tentative (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  minNamed
    ⟨atomName k (R.portals C).left 0,
      p (R.portals C).left + dist (R.portals C).left v + α k (R.portals C).left.column 0⟩
    ⟨atomName k (R.portals C).right 0,
      p (R.portals C).right + dist (R.portals C).right v + α k (R.portals C).right.column 0⟩

noncomputable def upperCone (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  minNamed
    ⟨atomName k (R.portals C).left 1,
      (F (R.portals C).left).value + dist (R.portals C).left v - α k (R.portals C).left.column 1⟩
    ⟨atomName k (R.portals C).right 1,
      (F (R.portals C).right).value + dist (R.portals C).right v - α k (R.portals C).right.column 1⟩

noncomputable def lowerCone (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) : NamedValue :=
  maxNamed
    ⟨atomName k (R.portals C).left 2,
      (F (R.portals C).left).value - dist (R.portals C).left v + α k (R.portals C).left.column 2⟩
    ⟨atomName k (R.portals C).right 2,
      (F (R.portals C).right).value - dist (R.portals C).right v + α k (R.portals C).right.column 2⟩

/-- The manuscript's recursive named formulas, on the whole metric component. -/
noncomputable def formula (p : M.Point J root → ℝ) (α : Noise (n := n)) :
    (k : ℕ) → R.Node k → M.Point J root → NamedValue
  | 0, C, v => R.tentative p α C v
  | k + 1, C, v =>
    let F := formula p α k (R.parent C)
    nodeNamed (F v) (R.upperCone F α C v) (R.lowerCone F α C v) (R.tentative p α C v)

lemma tentative_names (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.tentative p α C v).name ∧
      (R.tentative p α C v).name < 3 * n * (k + 1) := by
  rcases minNamed_mem _ _ with h | h
  · rw [tentative, h]
    exact atomName_bounds k (R.portals C).left 0
  · rw [tentative, h]
    exact atomName_bounds k (R.portals C).right 0

lemma upperCone_names (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.upperCone F α C v).name ∧
      (R.upperCone F α C v).name < 3 * n * (k + 1) := by
  rcases minNamed_mem _ _ with h | h
  · rw [upperCone, h]
    exact atomName_bounds k (R.portals C).left 1
  · rw [upperCone, h]
    exact atomName_bounds k (R.portals C).right 1

lemma lowerCone_names (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    3 * n * k ≤ (R.lowerCone F α C v).name ∧
      (R.lowerCone F α C v).name < 3 * n * (k + 1) := by
  rcases maxNamed_mem _ _ with h | h
  · rw [lowerCone, h]
    exact atomName_bounds k (R.portals C).left 2
  · rw [lowerCone, h]
    exact atomName_bounds k (R.portals C).right 2

lemma formula_name_bound (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    (R.formula p α k C v).name < 3 * n * (k + 1) := by
  induction k with
  | zero => exact (R.tentative_names p α C v).2
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · rw [h]
      exact (ih (R.parent C)).trans_le (Nat.mul_le_mul_left (3 * n) (Nat.le_succ (k + 1)))
    · rw [h]
      exact (R.upperCone_names _ _ _ _).2
    · rw [h]
      exact (R.lowerCone_names _ _ _ _).2
    · rw [h]
      exact (R.tentative_names _ _ _ _).2

lemma tentative_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.tentative p α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l (p l + α k l.column 0)).1
  have hr := (distance_cone_lipschitz r (p r + α k r.column 0)).1
  simpa only [tentative, minNamed_value, max_self, add_right_comm] using hl.min hr

lemma upperCone_lipschitz (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.upperCone F α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l ((F l).value - α k l.column 1)).1
  have hr := (distance_cone_lipschitz r ((F r).value - α k r.column 1)).1
  simpa only [upperCone, minNamed_value, max_self, sub_add_eq_add_sub] using hl.min hr

lemma lowerCone_lipschitz (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) : LipschitzWith 1 (fun v => (R.lowerCone F α C v).value) := by
  let l := (R.portals C).left
  let r := (R.portals C).right
  have hl := (distance_cone_lipschitz l ((F l).value + α k l.column 2)).2
  have hr := (distance_cone_lipschitz r ((F r).value + α k r.column 2)).2
  simpa only [lowerCone, maxNamed_value, max_self, sub_add_eq_add_sub] using hl.max hr

lemma formula_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) : LipschitzWith 1 (fun v => (R.formula p α k C v).value) := by
  induction k with
  | zero => exact R.tentative_lipschitz p α C
  | succ k ih =>
    simpa only [formula, nodeNamed_value] using
      nodeValue_lipschitz (ih (R.parent C)) (R.upperCone_lipschitz _ _ _)
        (R.lowerCone_lipschitz _ _ _) (R.tentative_lipschitz _ _ _)

noncomputable def q : ℝ := R.ζ * R.δ / 20

lemma q_pos : 0 < R.q := div_pos (mul_pos R.zeta_pos R.delta_pos) (by norm_num)

lemma q_small : 2 * R.q ≤ R.δ / 10 := by
  have h := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  dsimp [q]
  linarith

def NoiseBounds (α : Noise (n := n)) : Prop :=
  ∀ k i j, R.q ≤ α k i j ∧ α k i j ≤ 2 * R.q

def InputLip (p : M.Point J root → ℝ) : Prop :=
  ∀ x y, |p x - p y| ≤ (1 - R.ζ) * dist x y

noncomputable def portalDistance {k : ℕ} (C : R.Node k) (v : M.Point J root) : ℝ :=
  min (dist (R.portals C).left v) (dist (R.portals C).right v)

lemma portalDistance_nonneg {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    0 ≤ R.portalDistance C v := le_min dist_nonneg dist_nonneg

lemma tentative_bounds {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    p v + R.ζ * R.portalDistance C v + R.q ≤ (R.tentative p α C v).value ∧
    (R.tentative p α C v).value ≤ p v + (2 - R.ζ) * R.portalDistance C v + 2 * R.q := by
  have atom (w : M.Point J root) :
      p v + R.ζ * dist w v + R.q ≤ p w + dist w v + α k w.column 0 ∧
      p w + dist w v + α k w.column 0 ≤ p v + (2 - R.ζ) * dist w v + 2 * R.q := by
    have hlip := abs_le.mp (hp w v)
    have hn := hα k w.column 0
    constructor <;> nlinarith
  have hleft := atom (R.portals C).left
  have hright := atom (R.portals C).right
  simp only [tentative, minNamed_value]
  constructor
  · apply le_min
    · have hd := mul_le_mul_of_nonneg_left
        (min_le_left (dist (R.portals C).left v) (dist (R.portals C).right v)) R.zeta_pos.le
      dsimp [portalDistance]
      linarith
    · have hd := mul_le_mul_of_nonneg_left
        (min_le_right (dist (R.portals C).left v) (dist (R.portals C).right v)) R.zeta_pos.le
      dsimp [portalDistance]
      linarith
  · rcases le_total (dist (R.portals C).left v) (dist (R.portals C).right v) with h | h
    · rw [portalDistance, min_eq_left h]
      exact (min_le_left _ _).trans hleft.2
    · rw [portalDistance, min_eq_right h]
      exact (min_le_right _ _).trans hright.2

lemma cone_bounds {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k)
    (F : M.Point J root → NamedValue)
    (hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
      |(F w).value - p w| ≤ 5 * R.δ) (v : M.Point J root) :
    p v - 5 * R.δ + R.ζ * R.portalDistance C v - 2 * R.q ≤ (R.upperCone F α C v).value ∧
    (R.lowerCone F α C v).value ≤ p v + 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q := by
  have atom (w : M.Point J root) (hw : w = (R.portals C).left ∨ w = (R.portals C).right)
      (hd : R.portalDistance C v ≤ dist w v) :
      p v - 5 * R.δ + R.ζ * R.portalDistance C v - 2 * R.q ≤
        (F w).value + dist w v - α k w.column 1 ∧
      (F w).value - dist w v + α k w.column 2 ≤
        p v + 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q := by
    have hlip := abs_le.mp (hp w v)
    have ha := abs_le.mp (hF w hw)
    have hn₁ := hα k w.column 1
    have hn₂ := hα k w.column 2
    have hz := mul_le_mul_of_nonneg_left hd R.zeta_pos.le
    constructor <;> nlinarith
  have hl := atom (R.portals C).left (Or.inl rfl) (min_le_left _ _)
  have hr := atom (R.portals C).right (Or.inr rfl) (min_le_right _ _)
  exact ⟨by simpa only [upperCone, minNamed_value, le_min_iff] using And.intro hl.1 hr.1,
    by simpa only [lowerCone, maxNamed_value, max_le_iff] using And.intro hl.2 hr.2⟩

/-- With the thin-band constants, every nearby tentative value lies in the
same three-delta window used in the manuscript's induction. -/
lemma tentative_near {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hn : R.portalDistance C v ≤ R.δ + 220 * R.a) :
    p v ≤ (R.tentative p α C v).value ∧ (R.tentative p α C v).value ≤ p v + 3 * R.δ := by
  obtain ⟨hl, hu⟩ := R.tentative_bounds hp hα C v
  have hd := R.portalDistance_nonneg C v
  have hz := R.zeta_pos
  have hδ := R.delta_pos
  constructor
  · nlinarith [R.q_pos]
  · have h := mul_le_mul_of_nonneg_left hn (by linarith [R.zeta_lt_one] : 0 ≤ 2 - R.ζ)
    have hw := R.width_small
    have hq := R.q_small
    nlinarith [R.width_pos, mul_nonneg hz.le hd]

/-- Exact named inheritance on the genuine entrance collar. -/
lemma formula_collar (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hc : R.portalDistance C v ≤ R.ζ * R.δ / 50) :
    R.formula p α (k + 1) C v = R.formula p α k (R.parent C) v := by
  let F := R.formula p α k (R.parent C)
  have hF := R.formula_lipschitz p α k (R.parent C)
  have hcq : 2 * (R.ζ * R.δ / 50) < R.q := by
    dsimp [q]
    nlinarith [mul_pos R.zeta_pos R.delta_pos]
  have single (w : M.Point J root) (hw : dist w v ≤ R.ζ * R.δ / 50) :
      (F w).value + dist w v - α (k + 1) w.column 1 < (F v).value ∧
      (F v).value < (F w).value - dist w v + α (k + 1) w.column 2 := by
    have hlip := hF.dist_le_mul w v
    change |(F w).value - (F v).value| ≤ (1 : ℝ) * dist w v at hlip
    simp only [one_mul, abs_le] at hlip
    have hn₁ := hα (k + 1) w.column 1
    have hn₂ := hα (k + 1) w.column 2
    constructor <;> linarith
  have hcones : (R.upperCone F α C v).value < (F v).value ∧
      (F v).value < (R.lowerCone F α C v).value := by
    simp only [upperCone, lowerCone, minNamed_value, maxNamed_value]
    rcases min_le_iff.mp hc with h | h
    · have hs := single (R.portals C).left h
      exact ⟨lt_of_le_of_lt (min_le_left _ _) hs.1,
        lt_of_lt_of_le hs.2 (le_max_left _ _)⟩
    · have hs := single (R.portals C).right h
      exact ⟨lt_of_le_of_lt (min_le_right _ _) hs.1,
        lt_of_lt_of_le hs.2 (le_max_right _ _)⟩
  change nodeNamed (F v) _ _ _ = F v
  apply nodeNamed_collar hcones.1 hcones.2
  exact (R.formula_name_bound p α k (R.parent C) v).le.trans
    (R.tentative_names p α C v).1


lemma portal_spacing : 2 * R.q ≤ R.ζ * (R.δ - 10 * R.a) := by
  have hw : R.δ / 10 ≤ R.δ - 10 * R.a := by linarith [R.width_small, R.delta_pos]
  have hh := mul_le_mul_of_nonneg_left hw R.zeta_pos.le
  dsimp [q]
  nlinarith

/-- The complete quantitative induction on the ACTUAL component hierarchy.
The second bound applies to child portals; the first applies on the own layer. -/
lemma formula_near_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hn : R.portalDistance C v ≤ R.δ + 220 * R.a) :
    |(R.formula p α k C v).value - p v| ≤ 5 * R.δ + 2 * R.q ∧
    (2 * R.q ≤ R.ζ * R.portalDistance C v →
      |(R.formula p α k C v).value - p v| ≤ 5 * R.δ) := by
  induction k generalizing v with
  | zero =>
    have hT := R.tentative_near hp hα C v hn
    simp only [formula, abs_le]
    constructor
    · constructor <;> linarith [R.delta_pos, R.q_pos]
    · intro _
      constructor <;> linarith [R.delta_pos]
  | succ k ih =>
    let F := R.formula p α k (R.parent C)
    have hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
        |(F w).value - p w| ≤ 5 * R.δ := by
      intro w hw
      have hn' : R.portalDistance (R.parent C) w ≤ R.δ + 220 * R.a := by
        simpa only [portalDistance, dist_comm w] using R.parent_near C w hw
      have hd : R.δ - 10 * R.a ≤ R.portalDistance (R.parent C) w :=
        le_min (R.parent_separated C _ w (Or.inl rfl) hw)
          (R.parent_separated C _ w (Or.inr rfl) hw)
      have hs := R.portal_spacing.trans (mul_le_mul_of_nonneg_left hd R.zeta_pos.le)
      exact (ih (R.parent C) w hn').2 hs
    obtain ⟨hA, hB⟩ := R.cone_bounds hp hα C F hF v
    obtain ⟨hTlo, hThi⟩ := R.tentative_near hp hα C v hn
    have hval : (R.formula p α (k + 1) C v).value =
        nodeValue (F v).value (R.upperCone F α C v).value
          (R.lowerCone F α C v).value (R.tentative p α C v).value := by
      simp only [formula, nodeNamed_value, F]
    have bound (e : ℝ) (he : 3 * R.δ ≤ e)
        (hu : 5 * R.δ - R.ζ * R.portalDistance C v + 2 * R.q ≤ e) :
        |(R.formula p α (k + 1) C v).value - p v| ≤ e := by
      have hb := nodeValue_bounds (parent := (F v).value)
        (lo := p v - e) (hi := p v + e)
        (show p v - e ≤ (R.upperCone F α C v).value by linarith)
        (show (R.lowerCone F α C v).value ≤ p v + e by linarith)
        (show p v - e ≤ (R.tentative p α C v).value by linarith [R.delta_pos])
        (show (R.tentative p α C v).value ≤ p v + e by linarith)
      rw [hval, abs_le]
      constructor <;> linarith
    constructor
    · apply bound (5 * R.δ + 2 * R.q)
      · linarith [R.delta_pos, R.q_pos]
      · nlinarith [mul_nonneg R.zeta_pos.le (R.portalDistance_nonneg C v)]
    · intro hs
      exact bound (5 * R.δ) (by linarith [R.delta_pos]) (by linarith)

lemma formula_child_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1))
    (v : M.Point J root) (hv : v = (R.portals C).left ∨ v = (R.portals C).right) :
    |(R.formula p α k (R.parent C) v).value - p v| ≤ 5 * R.δ := by
  have hn : R.portalDistance (R.parent C) v ≤ R.δ + 220 * R.a := by
    simpa only [portalDistance, dist_comm v] using R.parent_near C v hv
  have hd : R.δ - 10 * R.a ≤ R.portalDistance (R.parent C) v :=
    le_min (R.parent_separated C _ v (Or.inl rfl) hv)
      (R.parent_separated C _ v (Or.inr rfl) hv)
  exact (R.formula_near_accuracy hp hα k (R.parent C) v hn).2
    (R.portal_spacing.trans (mul_le_mul_of_nonneg_left hd R.zeta_pos.le))

lemma formula_layer_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hv : v.column ∈ ColumnOrder.componentColumns C)
    (hr : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    |(R.formula p α k C v).value - p v| ≤ 6 * R.δ := by
  have hn : R.portalDistance C v ≤ R.δ + 220 * R.a := by
    have hh : dist R.base (v.withHeight R.base.height R.base.inBand) < (k : ℝ) * R.δ + R.δ := by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hr
    simpa only [portalDistance, dist_comm v] using
      (R.portals C).near_layer R.half_width R.width_pos.le v hv hh
  have ha := (R.formula_near_accuracy hp hα k C v hn).1
  linarith [R.q_small, R.delta_pos]


/-- The unique depth of the layer assigned to a column. -/
noncomputable def layerDepth (v : M.Point J root) : ℕ :=
  ⌊dist R.base (v.withHeight R.base.height R.base.inBand) / R.δ⌋₊

lemma layerDepth_bounds (v : M.Point J root) :
    (R.layerDepth v : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand) ∧
    dist R.base (v.withHeight R.base.height R.base.inBand) < (R.layerDepth v + 1 : ℕ) * R.δ := by
  have hl := Nat.floor_le (div_nonneg (dist_nonneg (x := R.base)
    (y := v.withHeight R.base.height R.base.inBand)) R.delta_pos.le)
  have hu := Nat.lt_floor_add_one
    (dist R.base (v.withHeight R.base.height R.base.inBand) / R.δ)
  constructor
  · exact (le_div_iff₀ R.delta_pos).mp hl
  · simpa only [layerDepth, Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ R.delta_pos).mp hu

lemma layerDepth_eq {k : ℕ} (v : M.Point J root)
    (hl : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (hu : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    R.layerDepth v = k := by
  apply (Nat.floor_eq_iff (div_nonneg dist_nonneg R.delta_pos.le)).mpr
  refine ⟨(le_div_iff₀ R.delta_pos).mpr hl, ?_⟩
  apply (div_lt_iff₀ R.delta_pos).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using hu

noncomputable def nodeOf (k : ℕ) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) : R.Node k :=
  ((M.activeGraph J).induce _).connectedComponentMk
    ⟨v.column, (R.base.mem_superlevel_iff v R.base.height R.base.inBand (k * R.δ)).mpr hv⟩

lemma mem_nodeOf (k : ℕ) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    v.column ∈ ColumnOrder.componentColumns (R.nodeOf k v hv) :=
  ⟨⟨v.column, (R.base.mem_superlevel_iff v R.base.height R.base.inBand (k * R.δ)).mpr hv⟩, rfl, rfl⟩

noncomputable def layerNode (v : M.Point J root) : R.Node (R.layerDepth v) :=
  R.nodeOf (R.layerDepth v) v (R.layerDepth_bounds v).1

lemma mem_layerNode (v : M.Point J root) :
    v.column ∈ ColumnOrder.componentColumns (R.layerNode v) :=
  R.mem_nodeOf (R.layerDepth v) v (R.layerDepth_bounds v).1

/-- The actual pasted named output on representatives. -/
noncomputable def pasted (p : M.Point J root → ℝ) (α : Noise (n := n)) (v : M.Point J root) : NamedValue :=
  R.formula p α (R.layerDepth v) (R.layerNode v) v

lemma pasted_eq_of_layer (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root)
    (hm : v.column ∈ ColumnOrder.componentColumns C)
    (hl : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (hu : dist R.base (v.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ) :
    R.pasted p α v = R.formula p α k C v := by
  have hd := R.layerDepth_eq v hl hu
  subst k
  have he : R.layerNode v = C := ColumnOrder.component_eq_of_column (R.mem_layerNode v) hm
  simp only [pasted, he]

lemma pasted_accuracy {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (v : M.Point J root) :
    |(R.pasted p α v).value - p v| ≤ 6 * R.δ :=
  R.formula_layer_accuracy hp hα (R.layerNode v) v (R.mem_layerNode v) (R.layerDepth_bounds v).2

noncomputable def radius : ℝ := R.ζ * R.δ / 1000

lemma radius_pos : 0 < R.radius := div_pos (mul_pos R.zeta_pos R.delta_pos) (by norm_num)

lemma radius_bounds {ρ : ℝ} (hρ : ρ ≤ R.radius) :
    2 * ρ + R.a < R.δ ∧ 2 * ρ + 200 * R.a ≤ R.ζ * R.δ / 50 := by
  have hw := R.width_bound
  have hd := mul_lt_mul_of_pos_right R.zeta_lt_one R.delta_pos
  have hz := mul_pos R.zeta_pos R.delta_pos
  dsimp [radius] at hρ
  constructor <;> nlinarith

/-- One deterministic node formula, with identical atom names, represents the
pasted output on the whole small ball (including every zero-distance copy).
The node exists independently of the noises and the input. -/
lemma common_formula (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius) :
    ∃ k : ℕ, ∃ C : R.Node k,
      (∀ z : M.Point J root, dist x z ≤ ρ →
        (k : ℝ) * R.δ ≤ dist R.base (z.withHeight R.base.height R.base.inBand)) ∧
      (∀ (p : M.Point J root → ℝ) (α : Noise (n := n)), R.NoiseBounds α →
        ∀ z : M.Point J root, dist x z ≤ ρ → R.pasted p α z = R.formula p α k C z) := by
  obtain ⟨k, y, C, hy, hylo, hC⟩ := R.base.ball_two_layers R.closed_band x R.base.inBand
    hρ R.delta_pos R.half_width (R.radius_bounds hs).1
  refine ⟨k, C, fun z hz => (hC z hz).2.1, ?_⟩
  intro p α hα z hz
  obtain ⟨hzm, hzl, hzu⟩ := hC z hz
  by_cases hlo : dist R.base (z.withHeight R.base.height R.base.inBand) < (k + 1 : ℕ) * R.δ
  · exact R.pasted_eq_of_layer p α C z hzm hzl hlo
  · have hzl' := le_of_not_gt hlo
    let D := R.nodeOf (k + 1) z hzl'
    have hD := R.mem_nodeOf (k + 1) z hzl'
    have hparent : R.parent D = C :=
      ColumnOrder.component_eq_of_column (R.mem_parent D hD) hzm
    have hyout : y.column ∉ ColumnOrder.componentColumns D := by
      intro hym
      have hry := (R.base.mem_superlevel_iff y R.base.height R.base.inBand (((k + 1 : ℕ) : ℝ) * R.δ)).mp
        (ColumnOrder.componentColumns_subset D hym)
      have hyp : dist R.base (y.withHeight R.base.height R.base.inBand) < ((k + 1 : ℕ) : ℝ) * R.δ := by
        simpa only [Nat.cast_add, Nat.cast_one] using hylo
      exact hyp.not_ge hry
    have hexit := (R.portals D).near_exit R.closed_band z y hD hyout
    have hzy : dist z y ≤ 2 * ρ := by
      have ht := dist_triangle z x y
      rw [dist_comm z x] at ht
      linarith
    have hcollar : R.portalDistance D z ≤ R.ζ * R.δ / 50 := by
      dsimp only [portalDistance]
      simp only [dist_comm z] at hexit
      rw [dist_comm y z] at hexit
      linarith [(R.radius_bounds hs).2]
    have hupper : dist R.base (z.withHeight R.base.height R.base.inBand) < ((k + 1 + 1 : ℕ) : ℝ) * R.δ := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hzu
    rw [R.pasted_eq_of_layer p α D z hD hzl' hupper,
      R.formula_collar p hα D z hcollar, hparent]

lemma formula_congr_zero (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (x y : M.Point J root) (hxy : dist x y = 0) :
    R.formula p α k C x = R.formula p α k C y := by
  have hd (w : M.Point J root) : dist w x = dist w y := by
    apply le_antisymm
    · have ht := dist_triangle w y x
      rw [dist_comm y x, hxy, add_zero] at ht
      exact ht
    · have ht := dist_triangle w x y
      rw [hxy, add_zero] at ht
      exact ht
  induction k with
  | zero => simp only [formula, tentative, hd]
  | succ k ih => simp only [formula, tentative, upperCone, lowerCone, hd, ih]

lemma pasted_congr_zero (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) (x y : M.Point J root) (hxy : dist x y = 0) :
    R.pasted p α x = R.pasted p α y := by
  obtain ⟨k, C, _, hC⟩ := R.common_formula x R.radius_pos.le le_rfl
  rw [hC p α hα x (by simpa using R.radius_pos.le), hC p α hα y (by simpa [hxy] using R.radius_pos.le)]
  exact R.formula_congr_zero p α k C x y hxy

lemma pasted_local_lipschitz (p : M.Point J root → ℝ) {α : Noise (n := n)}
    (hα : R.NoiseBounds α) (x y : M.Point J root) (hxy : dist x y ≤ R.radius) :
    |(R.pasted p α x).value - (R.pasted p α y).value| ≤ dist x y := by
  obtain ⟨k, C, _, hC⟩ := R.common_formula x R.radius_pos.le le_rfl
  rw [hC p α hα x (by simpa using R.radius_pos.le), hC p α hα y hxy]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using (R.formula_lipschitz p α k C).dist_le_mul x y

/-- Uniform local unit bounds extend globally by genuine shortest-path
interpolation. No length-space axiom has been added. -/
lemma pasted_lipschitz (p : M.Point J root → ℝ) {α : Noise (n := n)} (hα : R.NoiseBounds α) :
    LipschitzWith 1 (fun v => (R.pasted p α v).value) := by
  have bound (m : ℕ) : ∀ x y : M.Point J root, dist x y ≤ m * R.radius →
      |(R.pasted p α x).value - (R.pasted p α y).value| ≤ dist x y := by
    induction m with
    | zero =>
      intro x y hxy
      have hzero : dist x y ≤ 0 := by simpa only [Nat.cast_zero, zero_mul] using hxy
      exact R.pasted_local_lipschitz p hα x y (hzero.trans R.radius_pos.le)
    | succ m ih =>
      intro x y hxy
      by_cases hsmall : dist x y ≤ R.radius
      · exact R.pasted_local_lipschitz p hα x y hsmall
      · obtain ⟨z, hxz, hzy⟩ := x.exists_between R.closed_band R.interval_band y
          R.radius_pos.le (le_of_not_ge hsmall)
        have hzsmall : dist z y ≤ m * R.radius := by
          simp only [Nat.cast_succ, add_mul, one_mul] at hxy
          linarith
        have h₁ := R.pasted_local_lipschitz p hα x z hxz.le
        have h₂ := ih z y hzsmall
        have htri := abs_sub_le (R.pasted p α x).value (R.pasted p α z).value (R.pasted p α y).value
        linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨m, hm⟩ := exists_nat_ge (dist x y / R.radius)
  have hdist := bound m x y ((div_le_iff₀ R.radius_pos).mp hm)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hdist


/-- Ancestors are constructed by inclusion of actual superlevel components. -/
def ancestor {k : ℕ} (C : R.Node k) (j : ℕ) (hj : j ≤ k) : R.Node j :=
  ColumnOrder.componentAbove (R.superlevel_antitone hj) C

lemma mem_ancestor {k : ℕ} (C : R.Node k) (j : ℕ) (hj : j ≤ k) :
    ColumnOrder.componentColumns C ⊆ ColumnOrder.componentColumns (R.ancestor C j hj) :=
  ColumnOrder.componentColumns_above _ C

lemma ancestor_self {k : ℕ} (C : R.Node k) (h : k ≤ k) : R.ancestor C k h = C := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  exact ColumnOrder.component_eq_of_column (R.mem_ancestor C k h ⟨i, hi, rfl⟩) ⟨i, hi, rfl⟩

lemma ancestor_parent {k j : ℕ} (C : R.Node (k + 1)) (hj : j ≤ k) :
    R.ancestor (R.parent C) j hj = R.ancestor C j (hj.trans (Nat.le_succ k)) := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hm : i.val ∈ ColumnOrder.componentColumns C := ⟨i, hi, rfl⟩
  exact ColumnOrder.component_eq_of_column
    (R.mem_ancestor (R.parent C) j hj (R.mem_parent C hm)) (R.mem_ancestor C j _ hm)

lemma parent_ancestor {k j : ℕ} (C : R.Node k) (hj : j + 1 ≤ k) :
    R.parent (R.ancestor C (j + 1) hj) = R.ancestor C j (by omega) := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hm : i.val ∈ ColumnOrder.componentColumns C := ⟨i, hi, rfl⟩
  exact ColumnOrder.component_eq_of_column
    (R.mem_parent _ (R.mem_ancestor C (j + 1) hj hm)) (R.mem_ancestor C j _ hm)

/-- A name older than a chosen depth is inherited literally all the way back
through the actual hierarchy. Intercepts are not re-evaluated or renamed. -/
lemma formula_inherits (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (j : ℕ) (hj : j ≤ k) (v : M.Point J root)
    (hname : (R.formula p α k C v).name < 3 * n * j) :
    R.formula p α k C v = R.formula p α j (R.ancestor C j hj) v := by
  induction k generalizing j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    rw [R.ancestor_self]
  | succ k ih =>
    by_cases hlast : j = k + 1
    · subst j
      rw [R.ancestor_self]
    · have hjk : j ≤ k := by omega
      have hstep : R.formula p α (k + 1) C v = R.formula p α k (R.parent C) v := by
        change nodeNamed _ _ _ _ = _
        apply nodeNamed_old (cutoff := 3 * n * j)
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.upperCone_names _ _ C v).1
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.lowerCone_names _ _ C v).1
        · exact (Nat.mul_le_mul_left (3 * n) hj).trans (R.tentative_names p α C v).1
        · exact hname
      have hi := ih (R.parent C) j hjk (by simpa only [hstep] using hname)
      rw [R.ancestor_parent C hjk] at hi
      exact hstep.trans hi

/-- A far node cannot output an accurate value carrying an earlier name. -/
lemma formula_far_name {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root)
    (hfar : 13 * R.δ < R.ζ * R.portalDistance C v)
    (hacc : |(R.formula p α (k + 1) C v).value - p v| ≤ 6 * R.δ) :
    3 * n * (k + 1) ≤ (R.formula p α (k + 1) C v).name := by
  by_contra hn
  have hn' := lt_of_not_ge hn
  let F := R.formula p α k (R.parent C)
  have hF : ∀ w, w = (R.portals C).left ∨ w = (R.portals C).right →
      |(F w).value - p w| ≤ 5 * R.δ := R.formula_child_accuracy hp hα C
  obtain ⟨hA, hB⟩ := R.cone_bounds hp hα C F hF v
  have hT := (R.tentative_bounds hp hα C v).1
  have hsame : R.formula p α (k + 1) C v = F v := by
    apply nodeNamed_old (R.upperCone_names F α C v).1 (R.lowerCone_names F α C v).1
      (R.tentative_names p α C v).1 hn'
  have hparent : |(F v).value - p v| ≤ 6 * R.δ := by simpa only [hsame] using hacc
  have hneq := (distant_node_overwrites R.delta_pos hparent
    (show p v + 7 * R.δ < (R.upperCone F α C v).value by linarith [R.q_small, R.delta_pos])
    (show (R.lowerCone F α C v).value < p v - 7 * R.δ by linarith [R.q_small, R.delta_pos])
    (show p v + 13 * R.δ < (R.tentative p α C v).value by linarith [R.q_pos])).2
  apply hneq
  have heq := congrArg NamedValue.value hsame
  simpa only [formula, nodeNamed_value, F] using heq

/-- The source's lookback constant, independent of diameter and tree depth. -/
noncomputable def lookback : ℕ := ⌈15 / R.ζ⌉₊ + 3

lemma lookback_large : 15 ≤ R.ζ * (R.lookback : ℝ) := by
  have hh := Nat.le_ceil (15 / R.ζ)
  have hb : 15 / R.ζ ≤ (R.lookback : ℝ) := by
    dsimp [lookback]
    push_cast
    linarith
  have h := (div_le_iff₀ R.zeta_pos).mp hb
  nlinarith

lemma ancestor_distance {k j : ℕ} (C : R.Node k) (hj : j ≤ k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    ((k : ℝ) - j) * R.δ - 3 * R.a ≤ R.portalDistance (R.ancestor C j hj) v := by
  let D := R.ancestor C j hj
  have hver : dist v (v.withHeight R.base.height R.base.inBand) ≤ R.a / 2 := by
    rw [v.dist_withHeight, abs_sub_comm]
    exact R.half_width v.height v.inBand
  have hrad := dist_triangle R.base v (v.withHeight R.base.height R.base.inBand)
  have single (w : M.Point J root) (hw : dist R.base w < (j : ℝ) * R.δ + R.a) :
      ((k : ℝ) - j) * R.δ - 3 * R.a ≤ dist w v := by
    nlinarith [dist_triangle R.base w v, R.width_pos]
  exact le_min (single (R.portals D).left (R.portals D).left_radial.2)
    (single (R.portals D).right (R.portals D).right_radial.2)

lemma far_after_lookback {r : ℝ} (hr : (R.lookback : ℝ) * R.δ - 3 * R.a ≤ r) :
    13 * R.δ < R.ζ * r := by
  have h₁ := mul_le_mul_of_nonneg_left hr R.zeta_pos.le
  have h₂ := mul_le_mul_of_nonneg_right R.lookback_large R.delta_pos.le
  have h₃ : R.ζ * R.a ≤ R.a := by
    have hh := mul_lt_mul_of_pos_right R.zeta_lt_one R.width_pos
    linarith
  nlinarith [R.width_small, R.delta_pos]

/-- Selected names of an accurate node at high radial points originate no
more than `lookback` generations earlier. This is not an assumed depth bound. -/
lemma formula_recent_bound {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    3 * n * (k - R.lookback) ≤ (R.formula p α k C v).name := by
  by_cases hk : k ≤ R.lookback
  · simp only [Nat.sub_eq_zero_of_le hk, Nat.mul_zero, Nat.zero_le]
  · have hmk : k - R.lookback ≤ k := Nat.sub_le _ _
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
      (show k - R.lookback ≠ 0 by omega)
    have hjk : j + 1 ≤ k := by omega
    by_contra hname
    have hn : (R.formula p α k C v).name < 3 * n * (j + 1) := by
      simpa only [hj] using lt_of_not_ge hname
    have heq := R.formula_inherits p α k C (j + 1) hjk v hn
    let D := R.ancestor C (j + 1) hjk
    have hacc : |(R.formula p α (j + 1) D v).value - p v| ≤ 6 * R.δ := by
      simpa only [heq] using ha
    have hfar := R.ancestor_distance C hjk v hv
    have hcast : (k : ℝ) - (j + 1 : ℕ) = R.lookback := by
      have hn : k = j + 1 + R.lookback := by omega
      exact_mod_cast (show (k : ℤ) - (j + 1) = R.lookback by omega)
    rw [hcast] at hfar
    have hnew := R.formula_far_name hp hα D v (R.far_after_lookback hfar) hacc
    rw [heq] at hn
    exact hn.not_ge hnew


/-- The fixed enumeration remembers whichever portal occurrence generated a
name. Duplicated portals still produce the same name. -/
noncomputable def portalAt {k : ℕ} (C : R.Node k) (i : Fin 2) : M.Point J root :=
  if i = 0 then (R.portals C).left else (R.portals C).right

noncomputable def nodeNames {k : ℕ} (C : R.Node k) : Finset ℕ :=
  Finset.univ.image (fun ij : Fin 2 × Fin 3 => atomName k (R.portalAt C ij.1) ij.2)

lemma nodeNames_card {k : ℕ} (C : R.Node k) : (R.nodeNames C).card ≤ 6 := by
  calc
    (R.nodeNames C).card ≤ (Finset.univ : Finset (Fin 2 × Fin 3)).card := Finset.card_image_le
    _ = 6 := by simp

lemma nodeNames_mem {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) :
    atomName k (R.portalAt C i) t ∈ R.nodeNames C := by
  exact Finset.mem_image.mpr ⟨(i, t), Finset.mem_univ _, rfl⟩

lemma nodeNames_left {k : ℕ} (C : R.Node k) (t : Fin 3) :
    atomName k (R.portals C).left t ∈ R.nodeNames C := by
  simpa [portalAt] using R.nodeNames_mem C 0 t

lemma nodeNames_right {k : ℕ} (C : R.Node k) (t : Fin 3) :
    atomName k (R.portals C).right t ∈ R.nodeNames C := by
  simpa only [portalAt, show (1 : Fin 2) ≠ 0 by decide, ite_false] using R.nodeNames_mem C 1 t

lemma nodeNames_bounds {k : ℕ} (C : R.Node k) {m : ℕ} (hm : m ∈ R.nodeNames C) :
    3 * n * k ≤ m ∧ m < 3 * n * (k + 1) := by
  obtain ⟨⟨i,t⟩, _, rfl⟩ := Finset.mem_image.mp hm
  exact atomName_bounds k (R.portalAt C i) t

lemma tentative_name_mem (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.tentative p α C v).name ∈ R.nodeNames C := by
  rcases minNamed_mem _ _ with h | h
  · rw [tentative, h]; exact R.nodeNames_left C 0
  · rw [tentative, h]; exact R.nodeNames_right C 0

lemma upperCone_name_mem (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.upperCone F α C v).name ∈ R.nodeNames C := by
  rcases minNamed_mem _ _ with h | h
  · rw [upperCone, h]; exact R.nodeNames_left C 1
  · rw [upperCone, h]; exact R.nodeNames_right C 1

lemma lowerCone_name_mem (F : M.Point J root → NamedValue) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    (R.lowerCone F α C v).name ∈ R.nodeNames C := by
  rcases maxNamed_mem _ _ with h | h
  · rw [lowerCone, h]; exact R.nodeNames_left C 2
  · rw [lowerCone, h]; exact R.nodeNames_right C 2

lemma formula_name_origin (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    ∃ j : ℕ, ∃ hj : j ≤ k,
      (R.formula p α k C v).name ∈ R.nodeNames (R.ancestor C j hj) := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    rw [R.ancestor_self]
    exact R.tentative_name_mem p α C v
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · obtain ⟨j, hj, hm⟩ := ih (R.parent C)
      refine ⟨j, hj.trans (Nat.le_succ k), ?_⟩
      rw [h, ← R.ancestor_parent C hj]
      exact hm
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.upperCone_name_mem _ _ C v
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.lowerCone_name_mem _ _ C v
    · refine ⟨k + 1, le_rfl, ?_⟩
      rw [h, R.ancestor_self]
      exact R.tentative_name_mem _ _ C v

/-- The deterministic, diameter-independent list at a node. -/
noncomputable def recentNames {k : ℕ} (C : R.Node k) (L : ℕ) : Finset ℕ :=
  (Finset.Icc (k - L) k).attach.biUnion
    (fun j => R.nodeNames (R.ancestor C j (Finset.mem_Icc.mp j.property).2))

lemma recentNames_card {k : ℕ} (C : R.Node k) (L : ℕ) :
    (R.recentNames C L).card ≤ 6 * (L + 1) := by
  calc
    (R.recentNames C L).card ≤
        ∑ j ∈ (Finset.Icc (k - L) k).attach,
          (R.nodeNames (R.ancestor C j (Finset.mem_Icc.mp j.property).2)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ (Finset.Icc (k - L) k).attach, 6 :=
      Finset.sum_le_sum (fun _ _ => R.nodeNames_card _)
    _ = (k + 1 - (k - L)) * 6 := by simp
    _ ≤ 6 * (L + 1) := by omega

lemma mem_recentNames {k j : ℕ} (C : R.Node k) (L : ℕ) (hj : j ≤ k) (hl : k - L ≤ j)
    {m : ℕ} (hm : m ∈ R.nodeNames (R.ancestor C j hj)) : m ∈ R.recentNames C L := by
  apply Finset.mem_biUnion.mpr
  exact ⟨⟨j, Finset.mem_Icc.mpr ⟨hl, hj⟩⟩, Finset.mem_attach _ _, hm⟩

lemma formula_name_recent {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    (R.formula p α k C v).name ∈ R.recentNames C R.lookback := by
  obtain ⟨j, hj, hm⟩ := R.formula_name_origin p α k C v
  have hlow := R.formula_recent_bound hp hα k C v hv ha
  have hu := (R.nodeNames_bounds _ hm).2
  have hn : 0 < n := Nat.zero_lt_of_lt v.column.isLt
  have hmul : 0 < 3 * n := by omega
  have hjlow : k - R.lookback ≤ j := by
    by_contra h
    have hj' : j + 1 ≤ k - R.lookback := by omega
    have hle := Nat.mul_le_mul_left (3 * n) hj'
    omega
  exact R.mem_recentNames C R.lookback hj hjlow hm

/-- The source's bounded local name theorem, derived from the actual tree and
from actual metric balls. Its list is fixed before input/noise sampling. -/
lemma local_name_list (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius) :
    ∃ S : Finset ℕ, S.card ≤ 6 * (R.lookback + 1) ∧
      ∀ (p : M.Point J root → ℝ) (α : Noise (n := n)),
        R.InputLip p → R.NoiseBounds α →
        ∀ z : M.Point J root, dist x z ≤ ρ → (R.pasted p α z).name ∈ S := by
  obtain ⟨k, C, hlo, heq⟩ := R.common_formula x hρ hs
  refine ⟨R.recentNames C R.lookback, R.recentNames_card C R.lookback, ?_⟩
  intro p α hp hα z hz
  rw [heq p α hα z hz]
  apply R.formula_name_recent hp hα k C z (hlo z hz)
  rw [← heq p α hα z hz]
  exact R.pasted_accuracy hp hα z

lemma portalAt_height {k : ℕ} (C : R.Node k) (i : Fin 2) :
    (R.portalAt C i).height = R.base.height := by
  dsimp only [portalAt]
  split
  · exact (R.portals C).left_height
  · exact (R.portals C).right_height

lemma portalAt_eq_of_column {k : ℕ} (C : R.Node k) (i i' : Fin 2)
    (h : (R.portalAt C i).column = (R.portalAt C i').column) :
    R.portalAt C i = R.portalAt C i' := by
  have hh := (R.portalAt_height C i).trans (R.portalAt_height C i').symm
  have hext : ∀ x y : M.Point J root, x.column = y.column → x.height = y.height → x = y := by
    rintro ⟨xc, xh, xb, xr⟩ ⟨yc, yh, yb, yr⟩ hc hh
    cases hc
    cases hh
    rfl
  exact hext _ _ h hh

lemma atomName_same_depth {k : ℕ} (u v : M.Point J root) (t t' : Fin 3)
    (h : atomName k u t = atomName k v t') : u.column = v.column ∧ t = t' := by
  have ht := t.isLt
  have ht' := t'.isLt
  simp only [atomName] at h
  constructor <;> apply Fin.ext <;> omega

/-- A node's parent intercept uses no noise from the current depth. The
root convention below merely fills unused clamping slots with the fixed input. -/
noncomputable def parentValue (p : M.Point J root → ℝ) (α : Noise (n := n)) :
    (k : ℕ) → R.Node k → M.Point J root → ℝ
  | 0, _, v => p v
  | k + 1, C, v => (R.formula p α k (R.parent C) v).value

noncomputable def atomIntercept (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) : ℝ :=
  (if t = 0 then p (R.portalAt C i) else R.parentValue p α k C (R.portalAt C i)) +
    (if t = 2 then -dist (R.portalAt C i) v else dist (R.portalAt C i) v)

noncomputable def nodeAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) : NamedValue :=
  ⟨atomName k (R.portalAt C i) t,
    R.atomIntercept p α C i t v +
      (if t = 1 then -α k (R.portalAt C i).column t else α k (R.portalAt C i).column t)⟩

lemma tentative_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (v : M.Point J root) :
    ∃ i : Fin 2, R.tentative p α C v = R.nodeAtom p α C i 0 v := by
  rcases minNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [tentative, h]
    simp [nodeAtom, atomIntercept, portalAt]
  · refine ⟨1, ?_⟩
    rw [tentative, h]
    simp [nodeAtom, atomIntercept, portalAt]

lemma upperCone_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root) :
    ∃ i : Fin 2, R.upperCone (R.formula p α k (R.parent C)) α C v = R.nodeAtom p α C i 1 v := by
  rcases minNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [upperCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]
  · refine ⟨1, ?_⟩
    rw [upperCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]

lemma lowerCone_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node (k + 1)) (v : M.Point J root) :
    ∃ i : Fin 2, R.lowerCone (R.formula p α k (R.parent C)) α C v = R.nodeAtom p α C i 2 v := by
  rcases maxNamed_mem _ _ with h | h
  · refine ⟨0, ?_⟩
    rw [lowerCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]
  · refine ⟨1, ?_⟩
    rw [lowerCone, h]
    simp [nodeAtom, atomIntercept, portalAt, parentValue, sub_eq_add_neg]

/-- Selection is of literal named functions, not just numerical atom names. -/
lemma formula_eq_atom (p : M.Point J root → ℝ) (α : Noise (n := n))
    (k : ℕ) (C : R.Node k) (v : M.Point J root) :
    ∃ j : ℕ, ∃ hj : j ≤ k, ∃ i : Fin 2, ∃ t : Fin 3,
      R.formula p α k C v = R.nodeAtom p α (R.ancestor C j hj) i t v := by
  induction k with
  | zero =>
    obtain ⟨i, hi⟩ := R.tentative_eq_atom p α C v
    exact ⟨0, le_rfl, i, 0, by simpa only [formula, R.ancestor_self] using hi⟩
  | succ k ih =>
    rw [formula]
    rcases nodeNamed_mem _ _ _ _ with h | h | h | h
    · obtain ⟨j, hj, i, t, heq⟩ := ih (R.parent C)
      refine ⟨j, hj.trans (Nat.le_succ k), i, t, ?_⟩
      rw [h, ← R.ancestor_parent C hj]
      exact heq
    · obtain ⟨i, hi⟩ := R.upperCone_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 1, by simpa only [h, R.ancestor_self] using hi⟩
    · obtain ⟨i, hi⟩ := R.lowerCone_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 2, by simpa only [h, R.ancestor_self] using hi⟩
    · obtain ⟨i, hi⟩ := R.tentative_eq_atom p α C v
      exact ⟨k + 1, le_rfl, i, 0, by simpa only [h, R.ancestor_self] using hi⟩

lemma formula_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j ≤ k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (v : M.Point J root) : R.formula p α k C v = R.formula p β k C v := by
  induction k generalizing v with
  | zero => simp only [formula, tentative, h 0 le_rfl]
  | succ k ih =>
    have he : R.formula p α k (R.parent C) = R.formula p β k (R.parent C) :=
      funext (fun w => ih (fun j hj => h j (hj.trans (Nat.le_succ k))) (R.parent C) w)
    simp only [formula, he, upperCone, lowerCone, tentative, h (k + 1) le_rfl]

lemma parentValue_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j < k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (v : M.Point J root) : R.parentValue p α k C v = R.parentValue p β k C v := by
  cases k with
  | zero => rfl
  | succ k => exact congrArg NamedValue.value (R.formula_noise_congr p α β k
      (fun j hj => h j (Nat.lt_succ_of_le hj)) (R.parent C) v)

lemma atomIntercept_noise_congr (p : M.Point J root → ℝ) (α β : Noise (n := n))
    (k : ℕ) (h : ∀ j < k, ∀ i t, α j i t = β j i t)
    (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) :
    R.atomIntercept p α C i t v = R.atomIntercept p β C i t v := by
  simp only [atomIntercept, R.parentValue_noise_congr p α β k h]

lemma nodeAtom_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) :
    LipschitzWith 1 (fun v => (R.nodeAtom p α C i t v).value) := by
  let c := (if t = 0 then p (R.portalAt C i) else R.parentValue p α k C (R.portalAt C i)) +
    (if t = 1 then -α k (R.portalAt C i).column t else α k (R.portalAt C i).column t)
  by_cases ht : t = 2
  · have he : (fun v => (R.nodeAtom p α C i t v).value) = (fun v => c - dist (R.portalAt C i) v) := by
      funext v
      simp only [nodeAtom, atomIntercept, ite_eq_left ht]
      dsimp only [c]
      ring
    rw [he]
    exact (distance_cone_lipschitz (R.portalAt C i) c).2
  · have he : (fun v => (R.nodeAtom p α C i t v).value) = (fun v => c + dist (R.portalAt C i) v) := by
      funext v
      simp only [nodeAtom, atomIntercept, ite_eq_right ht]
      dsimp only [c]
      ring
    rw [he]
    exact (distance_cone_lipschitz (R.portalAt C i) c).1

lemma nodeAtom_eq_of_name (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i i' : Fin 2) (t t' : Fin 3)
    (h : atomName k (R.portalAt C i) t = atomName k (R.portalAt C i') t') :
    R.nodeAtom p α C i t = R.nodeAtom p α C i' t' := by
  obtain ⟨hc, rfl⟩ := atomName_same_depth _ _ _ _ h
  have he := R.portalAt_eq_of_column C i i' hc
  funext v
  simp only [nodeAtom, atomIntercept, he]

/-- Explicit positions in the ancestor chain. The name, not this occurrence,
is the randomized identity; opposite portal occurrences may coincide. -/
abbrev ChainIndex (k : ℕ) := Fin (k + 1) × Fin 2 × Fin 3

noncomputable def chainName {k : ℕ} (C : R.Node k) (u : ChainIndex k) : ℕ :=
  atomName u.1 (R.portalAt (R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)) u.2.1) u.2.2

noncomputable def chainAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (u : ChainIndex k) : M.Point J root → NamedValue :=
  R.nodeAtom p α (R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)) u.2.1 u.2.2

lemma chainName_bounds {k : ℕ} (C : R.Node k) (u : ChainIndex k) :
    3 * n * u.1.val ≤ R.chainName C u ∧ R.chainName C u < 3 * n * (u.1.val + 1) :=
  atomName_bounds _ _ _

lemma chainAtom_eq_of_name (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (u u' : ChainIndex k) (h : R.chainName C u = R.chainName C u') :
    R.chainAtom p α C u = R.chainAtom p α C u' := by
  have h₁ := R.chainName_bounds C u
  have h₂ := R.chainName_bounds C u'
  have hd : u.1.val = u'.1.val := by
    rcases lt_trichotomy u.1.val u'.1.val with hl | he | hr
    · have hb := Nat.mul_le_mul_left (3 * n) (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one] at hb
      omega
    · exact he
    · have hb := Nat.mul_le_mul_left (3 * n) (Nat.succ_le_of_lt hr)
      simp only [Nat.succ_eq_add_one] at hb
      omega
  rcases u with ⟨j, i, t⟩
  rcases u' with ⟨j', i', t'⟩
  have hj : j = j' := Fin.ext hd
  subst j'
  exact R.nodeAtom_eq_of_name p α _ i i' t t' h

lemma recentNames_representation {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : ∃ u : ChainIndex k, R.chainName C u = m := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨⟨i,t⟩, _, he⟩ := Finset.mem_image.mp hj
  exact ⟨(⟨j.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp j.property).2⟩, i, t), he⟩

noncomputable def representative {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : ChainIndex k :=
  (R.recentNames_representation C L m hm).choose

lemma representative_name {k : ℕ} (C : R.Node k) (L m : ℕ)
    (hm : m ∈ R.recentNames C L) : R.chainName C (R.representative C L m hm) = m :=
  (R.recentNames_representation C L m hm).choose_spec

/-- A fixed representation for each name, chosen from geometry before noises.
Off the list the harmless zero branch makes this a total function. -/
noncomputable def listedAtom (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (L m : ℕ) (v : M.Point J root) : NamedValue :=
  if hm : m ∈ R.recentNames C L then R.chainAtom p α C (R.representative C L m hm) v
  else ⟨m, 0⟩

lemma listedAtom_name (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (L m : ℕ) (v : M.Point J root) :
    (R.listedAtom p α C L m v).name = m := by
  unfold listedAtom
  split_ifs with hm
  · exact R.representative_name C L m hm
  · rfl

lemma listedAtom_lipschitz (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (L m : ℕ) :
    LipschitzWith 1 (fun v => (R.listedAtom p α C L m v).value) := by
  unfold listedAtom
  split_ifs with hm
  · exact R.nodeAtom_lipschitz p α _ _ _
  · exact (LipschitzWith.const (0 : ℝ)).weaken (by simp)

lemma formula_eq_listed {p : M.Point J root → ℝ} {α : Noise (n := n)}
    (hp : R.InputLip p) (hα : R.NoiseBounds α) (k : ℕ) (C : R.Node k) (v : M.Point J root)
    (hv : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand))
    (ha : |(R.formula p α k C v).value - p v| ≤ 6 * R.δ) :
    R.formula p α k C v = R.listedAtom p α C R.lookback (R.formula p α k C v).name v := by
  have hm := R.formula_name_recent hp hα k C v hv ha
  obtain ⟨j, hj, i, t, he⟩ := R.formula_eq_atom p α k C v
  rw [listedAtom, dite_eq_left hm]
  let u : ChainIndex k := (⟨j, Nat.lt_succ_of_le hj⟩, i, t)
  have hu : R.chainName C u = (R.formula p α k C v).name := (congrArg NamedValue.name he).symm
  have hn := R.representative_name C R.lookback (R.formula p α k C v).name hm
  have heq := congrFun (R.chainAtom_eq_of_name p α C u _ (hu.trans hn.symm)) v
  exact he.trans heq

/-- The complete local list, including the actual named Lipschitz functions.
At most six atoms per recent ancestor survive. -/
lemma local_atom_list (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius) :
    ∃ k : ℕ, ∃ C : R.Node k,
      ∀ (p : M.Point J root → ℝ) (α : Noise (n := n)),
        R.InputLip p → R.NoiseBounds α → ∀ z : M.Point J root, dist x z ≤ ρ →
          (R.pasted p α z).name ∈ R.recentNames C R.lookback ∧
          R.pasted p α z = R.listedAtom p α C R.lookback (R.pasted p α z).name z := by
  obtain ⟨k, C, hlo, heq⟩ := R.common_formula x hρ hs
  refine ⟨k, C, ?_⟩
  intro p α hp hα z hz
  have ha : |(R.formula p α k C z).value - p z| ≤ 6 * R.δ := by
    rw [← heq p α hα z hz]
    exact R.pasted_accuracy hp hα z
  rw [heq p α hα z hz]
  exact ⟨R.formula_name_recent hp hα k C z (hlo z hz) ha,
    R.formula_eq_listed hp hα k C z (hlo z hz) ha⟩

/-- Off the finite near-tie event the selected name is constant. Direct
Lipschitz comparison proves this on the entire ball without a topological
selection argument, and also covers zero-distance representatives. -/
lemma stable_names_of_no_tie (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {k : ℕ} (C : R.Node k) (p : M.Point J root → ℝ) (α : Noise (n := n))
    (hα : R.NoiseBounds α)
    (hlist : ∀ z : M.Point J root, dist x z ≤ ρ →
      (R.pasted p α z).name ∈ R.recentNames C R.lookback ∧
      R.pasted p α z = R.listedAtom p α C R.lookback (R.pasted p α z).name z)
    (hgap : ∀ m ∈ R.recentNames C R.lookback, ∀ m' ∈ R.recentNames C R.lookback, m ≠ m' →
      2 * ρ < |(R.listedAtom p α C R.lookback m x).value -
        (R.listedAtom p α C R.lookback m' x).value|) :
    ∀ z : M.Point J root, dist x z ≤ ρ → (R.pasted p α z).name = (R.pasted p α x).name := by
  intro z hz
  have hx := hlist x (by simpa using hρ)
  have hz' := hlist z hz
  by_contra hn
  have hg := hgap (R.pasted p α x).name hx.1 (R.pasted p α z).name hz'.1 (Ne.symm hn)
  have hl₁ := (R.pasted_lipschitz p hα).dist_le_mul x z
  have hl₂ := (R.listedAtom_lipschitz p α C R.lookback (R.pasted p α z).name).dist_le_mul z x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl₁ hl₂
  rw [dist_comm z x] at hl₂
  have he₁ := congrArg NamedValue.value hx.2
  have he₂ := congrArg NamedValue.value hz'.2
  have ht := abs_sub_le (R.pasted p α x).value (R.pasted p α z).value
    (R.listedAtom p α C R.lookback (R.pasted p α z).name x).value
  rw [← he₂] at hl₂
  rw [← he₁] at hg
  linarith

/-- Replacement of exactly one current interpolation noise. -/
noncomputable def replaceNoise (α : Noise (n := n)) (d : ℕ) (c : Fin n) (t : Fin 3) (r : ℝ) :
    Noise (n := n) := fun j i s => if j = d ∧ i = c ∧ s = t then r else α j i s

lemma replaceNoise_self (α : Noise (n := n)) (d : ℕ) (c : Fin n) (t : Fin 3) (r : ℝ) :
    replaceNoise α d c t r d c t = r := by simp [replaceNoise]

lemma replaceNoise_other (α : Noise (n := n)) (d j : ℕ) (c i : Fin n) (t s : Fin 3) (r : ℝ)
    (h : ¬ (j = d ∧ i = c ∧ s = t)) : replaceNoise α d c t r j i s = α j i s := by
  simp only [replaceNoise, ite_eq_right h]

lemma atomIntercept_replace (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k d : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root)
    (hd : k ≤ d) (c : Fin n) (s : Fin 3) (r : ℝ) :
    R.atomIntercept p (replaceNoise α d c s r) C i t v = R.atomIntercept p α C i t v := by
  apply R.atomIntercept_noise_congr
  intro j hj u w
  exact replaceNoise_other α d j c u s w r (by omega)

lemma nodeAtom_replace_self (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root) (r : ℝ) :
    (R.nodeAtom p (replaceNoise α k (R.portalAt C i).column t r) C i t v).value =
      R.atomIntercept p α C i t v + (if t = 1 then -r else r) := by
  simp only [nodeAtom, R.atomIntercept_replace p α C i t v le_rfl,
    replaceNoise_self]

lemma nodeAtom_replace_other (p : M.Point J root → ℝ) (α : Noise (n := n))
    {k d : ℕ} (C : R.Node k) (i : Fin 2) (t : Fin 3) (v : M.Point J root)
    (hd : k ≤ d) (c : Fin n) (s : Fin 3) (r : ℝ)
    (h : ¬ (k = d ∧ (R.portalAt C i).column = c ∧ t = s)) :
    R.nodeAtom p (replaceNoise α d c s r) C i t v = R.nodeAtom p α C i t v := by
  simp only [nodeAtom, R.atomIntercept_replace p α C i t v hd,
    replaceNoise_other α d k c (R.portalAt C i).column s t r h]

/-- Every distinct pair on the ancestor chain has a fresh coordinate: after
all other noises are fixed, their difference is affine with slope ±1 in it. -/
lemma chainPair_fresh (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (u u' : ChainIndex k) (hne : R.chainName C u ≠ R.chainName C u') (v : M.Point J root) :
    ∃ d ≤ k, ∃ c : Fin n, ∃ s : Fin 3,
      ∀ α : Noise (n := n), ∃ b : ℝ,
        (∀ r : ℝ, (R.chainAtom p (replaceNoise α d c s r) C u v).value -
          (R.chainAtom p (replaceNoise α d c s r) C u' v).value = b + r) ∨
        (∀ r : ℝ, (R.chainAtom p (replaceNoise α d c s r) C u v).value -
          (R.chainAtom p (replaceNoise α d c s r) C u' v).value = b - r) := by
  let D := R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)
  let D' := R.ancestor C u'.1 (Nat.le_of_lt_succ u'.1.isLt)
  have hcoord : ¬ (u.1.val = u'.1.val ∧
      (R.portalAt D u.2.1).column = (R.portalAt D' u'.2.1).column ∧ u.2.2 = u'.2.2) := by
    rintro ⟨hd, hc, ht⟩
    apply hne
    simp only [chainName, atomName]
    change 3 * (n * u.1.val + (R.portalAt D u.2.1).column.val) + u.2.2.val =
      3 * (n * u'.1.val + (R.portalAt D' u'.2.1).column.val) + u'.2.2.val
    simp only [hd, hc, ht]
  by_cases hd : u.1.val ≤ u'.1.val
  · refine ⟨u'.1, Nat.le_of_lt_succ u'.1.isLt, (R.portalAt D' u'.2.1).column, u'.2.2, ?_⟩
    intro α
    refine ⟨(R.chainAtom p α C u v).value - R.atomIntercept p α D' u'.2.1 u'.2.2 v, ?_⟩
    by_cases hs : u'.2.2 = 1
    · left
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D _ _ v hd _ _ r hcoord,
        R.nodeAtom_replace_self p α D' _ _ v r, ite_eq_left hs]
      ring
    · right
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D _ _ v hd _ _ r hcoord,
        R.nodeAtom_replace_self p α D' _ _ v r, ite_eq_right hs]
      ring
  · have hd' : u'.1.val ≤ u.1.val := by omega
    have hcoord' : ¬ (u'.1.val = u.1.val ∧
        (R.portalAt D' u'.2.1).column = (R.portalAt D u.2.1).column ∧ u'.2.2 = u.2.2) := by
      rintro ⟨he, hc, ht⟩
      exact hcoord ⟨he.symm, hc.symm, ht.symm⟩
    refine ⟨u.1, Nat.le_of_lt_succ u.1.isLt, (R.portalAt D u.2.1).column, u.2.2, ?_⟩
    intro α
    refine ⟨R.atomIntercept p α D u.2.1 u.2.2 v - (R.chainAtom p α C u' v).value, ?_⟩
    by_cases hs : u.2.2 = 1
    · right
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D' _ _ v hd' _ _ r hcoord',
        R.nodeAtom_replace_self p α D _ _ v r, ite_eq_left hs]
      ring
    · left
      intro r
      dsimp only [chainAtom]
      rw [R.nodeAtom_replace_other p α D' _ _ v hd' _ _ r hcoord',
        R.nodeAtom_replace_self p α D _ _ v r, ite_eq_right hs]
      ring

/-- The finite noise sample space used by the construction. -/
abbrev GridSample (cap m : ℕ) := (Fin cap × Fin n × Fin 3) → Fin (m + 1)

noncomputable def gridNoise (cap m : ℕ) (ω : GridSample (n := n) cap m) : Noise (n := n) :=
  fun j i t => if hj : j < cap then R.q + R.q / m * (ω (⟨j,hj⟩,i,t)).val else R.q

lemma gridNoise_bounds (cap m : ℕ) (hm : 0 < m) (ω : GridSample (n := n) cap m) :
    R.NoiseBounds (R.gridNoise cap m ω) := by
  intro j i t
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hstep : 0 < R.q / m := div_pos R.q_pos hm'
  have hmul : R.q / (m : ℝ) * m = R.q := div_mul_cancel₀ R.q (ne_of_gt hm')
  simp only [gridNoise]
  split_ifs with hj
  · have hval : ((ω (⟨j,hj⟩,i,t)).val : ℝ) ≤ m := by
      exact_mod_cast Nat.le_of_lt_succ (ω (⟨j,hj⟩,i,t)).isLt
    have hhi := mul_le_mul_of_nonneg_left hval hstep.le
    rw [hmul] at hhi
    have hlo := mul_nonneg hstep.le (Nat.cast_nonneg (ω (⟨j,hj⟩,i,t)).val)
    constructor <;> linarith
  · constructor <;> linarith [R.q_pos]

lemma gridNoise_update (cap m : ℕ) (ω : GridSample (n := n) cap m)
    (d : ℕ) (hd : d < cap) (c : Fin n) (s : Fin 3) (r : Fin (m + 1)) :
    R.gridNoise cap m (Function.update ω (⟨d,hd⟩,c,s) r) =
      replaceNoise (R.gridNoise cap m ω) d c s (R.q + R.q / m * r.val) := by
  funext j i t
  by_cases hj : j < cap
  · by_cases he : (⟨j,hj⟩,i,t) = ((⟨d,hd⟩ : Fin cap),c,s)
    · have hparts := Prod.mk.inj he
      have hjd : j = d := congrArg Fin.val hparts.1
      obtain ⟨hic, hts⟩ := Prod.mk.inj hparts.2
      subst j
      subst i
      subst t
      simp only [gridNoise, dite_eq_left hd, Function.update_self, replaceNoise_self]
    · have hne : ¬ (j = d ∧ i = c ∧ t = s) := by
        rintro ⟨hjd, hic, hts⟩
        exact he (by subst j; subst i; subst t; rfl)
      rw [replaceNoise_other _ d j c i s t _ hne]
      simp only [gridNoise, dite_eq_left hj, Function.update_of_ne he]
  · have hne : ¬ (j = d ∧ i = c ∧ t = s) := fun h => hj (h.1 ▸ hd)
    rw [replaceNoise_other _ d j c i s t _ hne]
    simp only [gridNoise, dite_eq_right hj]

/-- The radial profile has only finitely many values, one per reachable column.
This explicit cap bounds every node ever used by the pasted field. -/
noncomputable def depthCap : ℕ := by
  classical
  exact 1 + ∑ i : Fin n,
    if hi : (M.activeGraph J).Reachable root i then
      ⌊dist R.base (⟨i, R.base.height, R.base.inBand, hi⟩ : M.Point J root) / R.δ⌋₊ else 0

lemma layerDepth_lt_cap (v : M.Point J root) : R.layerDepth v < R.depthCap := by
  classical
  let g : Fin n → ℕ := fun i => if hi : (M.activeGraph J).Reachable root i then
    ⌊dist R.base (⟨i, R.base.height, R.base.inBand, hi⟩ : M.Point J root) / R.δ⌋₊ else 0
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := g) (fun i _ => Nat.zero_le (g i))
    (Finset.mem_univ v.column)
  have he : R.layerDepth v = g v.column := by
    simp only [g, dite_eq_left v.reachable, layerDepth, withHeight]
  dsimp only [depthCap]
  change R.layerDepth v < 1 + ∑ i, g i
  omega

lemma depth_le_layerDepth {k : ℕ} (v : M.Point J root)
    (hk : (k : ℝ) * R.δ ≤ dist R.base (v.withHeight R.base.height R.base.inBand)) :
    k ≤ R.layerDepth v := by
  apply Nat.le_floor
  exact (le_div_iff₀ R.delta_pos).mpr hk


lemma chainPair_probability (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (u u' : ChainIndex k) (hne : R.chainName C u ≠ R.chainName C u')
    (v : M.Point J root) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.chainAtom p (R.gridNoise cap m ω) C u v).value -
        (R.chainAtom p (R.gridNoise cap m ω) C u' v).value| ≤ t) ≤
      (2 * t + R.q / m) / R.q := by
  classical
  obtain ⟨d, hd, c, s, hf⟩ := R.chainPair_fresh p C u u' hne v
  have hdc : d < cap := hd.trans_lt hk
  apply FiniteRandom.coordinate_probability (⟨d,hdc⟩,c,s) m hm R.q_pos ht
  intro ω
  obtain ⟨b, hb⟩ := hf (R.gridNoise cap m ω)
  rcases hb with hb | hb
  · refine ⟨b + R.q, Or.inl ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω d hdc c s r, hb]
    ring
  · refine ⟨b - R.q, Or.inr ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω d hdc c s r, hb]
    ring

lemma listedPair_probability (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k)
    (L i j : ℕ) (hi : i ∈ R.recentNames C L) (hj : j ∈ R.recentNames C L) (hne : i ≠ j)
    (v : M.Point J root) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.listedAtom p (R.gridNoise cap m ω) C L i v).value -
        (R.listedAtom p (R.gridNoise cap m ω) C L j v).value| ≤ t) ≤
      (2 * t + R.q / m) / R.q := by
  have hn : R.chainName C (R.representative C L i hi) ≠
      R.chainName C (R.representative C L j hj) := by
    simpa only [R.representative_name] using hne
  simpa only [listedAtom, dite_eq_left hi, dite_eq_left hj] using
    R.chainPair_probability p C _ _ hn v cap m hk hm ht

/-- Actual finite-grid anti-concentration for a changed interpolation atom name
anywhere on the closed ball. Its list and depth cap were constructed strictly
from the geometry before sampling the fresh independent coordinates. -/
lemma local_name_probability (p : M.Point J root → ℝ) (hp : R.InputLip p)
    (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : ρ ≤ R.radius)
    (m : ℕ) (hm : 0 < m) :
    FiniteRandom.prob (fun ω : GridSample (n := n) R.depthCap m =>
      ∃ z : M.Point J root, dist x z ≤ ρ ∧
        (R.pasted p (R.gridNoise R.depthCap m ω) z).name ≠
          (R.pasted p (R.gridNoise R.depthCap m ω) x).name) ≤
      (6 * (R.lookback + 1) : ℕ)^2 * ((4 * ρ + R.q / m) / R.q) := by
  classical
  obtain ⟨k, C, hlo, heq⟩ := R.common_formula x hρ hs
  have hk : k < R.depthCap :=
    (R.depth_le_layerDepth x (hlo x (by simpa using hρ))).trans_lt (R.layerDepth_lt_cap x)
  have hlist (ω : GridSample (n := n) R.depthCap m) (z : M.Point J root) (hz : dist x z ≤ ρ) :
      (R.pasted p (R.gridNoise R.depthCap m ω) z).name ∈ R.recentNames C R.lookback ∧
      R.pasted p (R.gridNoise R.depthCap m ω) z =
        R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback
          (R.pasted p (R.gridNoise R.depthCap m ω) z).name z := by
    have hα := R.gridNoise_bounds R.depthCap m hm ω
    have ha : |(R.formula p (R.gridNoise R.depthCap m ω) k C z).value - p z| ≤ 6 * R.δ := by
      rw [← heq p _ hα z hz]
      exact R.pasted_accuracy hp hα z
    rw [heq p _ hα z hz]
    exact ⟨R.formula_name_recent hp hα k C z (hlo z hz) ha,
      R.formula_eq_listed hp hα k C z (hlo z hz) ha⟩
  have hsub : ∀ ω : GridSample (n := n) R.depthCap m,
      (∃ z : M.Point J root, dist x z ≤ ρ ∧
        (R.pasted p (R.gridNoise R.depthCap m ω) z).name ≠
          (R.pasted p (R.gridNoise R.depthCap m ω) x).name) →
      ∃ i ∈ R.recentNames C R.lookback, ∃ j ∈ R.recentNames C R.lookback,
        i ≠ j ∧ |(R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback i x).value -
          (R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback j x).value| ≤ 2 * ρ := by
    intro ω hbad
    by_contra hn
    have hgap : ∀ i ∈ R.recentNames C R.lookback, ∀ j ∈ R.recentNames C R.lookback, i ≠ j →
        2 * ρ < |(R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback i x).value -
          (R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback j x).value| := by
      intro i hi j hj hij
      exact lt_of_not_ge (fun ht => hn ⟨i,hi,j,hj,hij,ht⟩)
    obtain ⟨z, hz, hne⟩ := hbad
    exact hne (R.stable_names_of_no_tie x hρ C p _ (R.gridNoise_bounds _ _ hm ω)
      (hlist ω) hgap z hz)
  have hb : 0 ≤ (4 * ρ + R.q / m) / R.q := by
    have hq := R.q_pos
    positivity
  have hprob := FiniteRandom.prob_pair_bound (R.recentNames C R.lookback)
    (fun i j (ω : GridSample (n := n) R.depthCap m) =>
      |(R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback i x).value -
        (R.listedAtom p (R.gridNoise R.depthCap m ω) C R.lookback j x).value| ≤ 2 * ρ) hb
    (fun i hi j hj hij => by
      simpa only [show 2 * (2 * ρ) = 4 * ρ by ring] using
        R.listedPair_probability p C R.lookback i j hi hj hij x R.depthCap m hk hm
          (t := 2 * ρ) (by positivity))
  refine (FiniteRandom.prob_mono hsub).trans (hprob.trans ?_)
  apply mul_le_mul_of_nonneg_right _ hb
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast R.recentNames_card C R.lookback) _

end RadialTree


end Point

end Model
end Columns
end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Point.RadialTree
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : RadialTree (M := M) (J := J) (root := root))

/-- Comparison with a fixed old field uses the current atom's own offset, not
an unjustified independence assertion about its inherited intercept. -/
lemma chainConstant_probability (p : M.Point J root → ℝ) {k : ℕ}
    (C : R.Node k) (u : ChainIndex k) (v : M.Point J root) (c : ℝ)
    (cap m : ℕ) (hk : k < cap) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.chainAtom p (R.gridNoise cap m ω) C u v).value-c| ≤ t) ≤
      (2*t+R.q/m)/R.q := by
  let D := R.ancestor C u.1 (Nat.le_of_lt_succ u.1.isLt)
  have hd : u.1.val < cap := (Nat.le_of_lt_succ u.1.isLt).trans_lt hk
  apply FiniteRandom.coordinate_probability
    (⟨u.1,hd⟩,(R.portalAt D u.2.1).column,u.2.2) m hm R.q_pos ht
  intro ω
  by_cases hs : u.2.2 = 1
  · refine ⟨R.atomIntercept p (R.gridNoise cap m ω) D u.2.1 u.2.2 v-c-R.q,Or.inr ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω u.1 hd (R.portalAt D u.2.1).column u.2.2 r]
    dsimp only [chainAtom]
    rw [R.nodeAtom_replace_self p _ D _ _ v _,ite_eq_left hs]
    ring
  · refine ⟨R.atomIntercept p (R.gridNoise cap m ω) D u.2.1 u.2.2 v-c+R.q,Or.inl ?_⟩
    intro r
    rw [R.gridNoise_update cap m ω u.1 hd (R.portalAt D u.2.1).column u.2.2 r]
    dsimp only [chainAtom]
    rw [R.nodeAtom_replace_self p _ D _ _ v _,ite_eq_right hs]
    ring

lemma listedConstant_probability (p : M.Point J root → ℝ) {k : ℕ}
    (C : R.Node k) (L i : ℕ) (hi : i ∈ R.recentNames C L)
    (v : M.Point J root) (c : ℝ) (cap m : ℕ) (hk : k < cap) (hm : 0 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m =>
      |(R.listedAtom p (R.gridNoise cap m ω) C L i v).value-c| ≤ t) ≤
      (2*t+R.q/m)/R.q := by
  simpa only [listedAtom,dite_eq_left hi] using
    R.chainConstant_probability p C (R.representative C L i hi) v c cap m hk hm ht

/-- Between independent interpolations, conditioning on the other full sample
still leaves the chosen atom's fresh coordinate available. -/
lemma listedIndependent_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : M.Point J root → ℝ) {k : ℕ} (C : R.Node k) (L i : ℕ)
    (hi : i ∈ R.recentNames C L) (v : M.Point J root) (other : Ω → ℝ)
    (cap m : ℕ) (hk : k < cap) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    FiniteRandom.prob (fun ω : GridSample (n := n) cap m × Ω =>
      |(R.listedAtom p (R.gridNoise cap m ω.1) C L i v).value-other ω.2| ≤ t) ≤
      (2*t+R.q/m)/R.q := by
  apply FiniteRandom.prob_prod_bound_left
  intro z
  exact R.listedConstant_probability p C L i hi v (other z) cap m hk hm ht

end PlanarL1.Columns.Model.Point.RadialTree




end

end OAI
