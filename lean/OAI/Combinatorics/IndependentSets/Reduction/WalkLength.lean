import Mathlib

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

def walkLength {X : Type*} (w : X → X → ℝ≥0∞) (x : X) : List X → X → ℝ≥0∞
  | [], y => w x y
  | z :: zs, y => w x z + walkLength w z zs y

noncomputable def pathDistance {X : Type*} (w : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ :=
  ⨅ zs : List X, walkLength w x zs y

lemma pathDistance_le_link {X : Type*} (w : X → X → ℝ≥0∞) (x y : X) :
    pathDistance w x y ≤ w x y :=
  iInf_le_of_le [] le_rfl

lemma walkLength_append {X : Type*} (w : X → X → ℝ≥0∞) (x y z : X)
    (p q : List X) :
    walkLength w x (p ++ y :: q) z = walkLength w x p y + walkLength w y q z := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, walkLength, ih, add_assoc]

lemma pathDistance_self {X : Type*} (w : X → X → ℝ≥0∞)
    (hrefl : ∀ x, w x x = 0) (x : X) : pathDistance w x x = 0 := by
  exact le_antisymm ((pathDistance_le_link w x x).trans_eq (hrefl x)) bot_le

lemma pathDistance_triangle {X : Type*} (w : X → X → ℝ≥0∞) (x y z : X) :
    pathDistance w x z ≤ pathDistance w x y + pathDistance w y z := by
  unfold pathDistance
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro p
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro q
  exact iInf_le_of_le (p ++ y :: q) (le_of_eq (walkLength_append w x y z p q))

lemma walkLength_map {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (hw : ∀ x y, w (T x) (T y) = w x y) (x y : X) (p : List X) :
    walkLength w (T x) (p.map T) (T y) = walkLength w x p y := by
  induction p generalizing x with
  | nil => exact hw x y
  | cons a p ih => simp only [List.map_cons, walkLength, hw, ih]

lemma pathDistance_invariant {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (hT : Function.Involutive T) (hw : ∀ x y, w (T x) (T y) = w x y)
    (x y : X) : pathDistance w (T x) (T y) = pathDistance w x y := by
  have hle (x y : X) : pathDistance w (T x) (T y) ≤ pathDistance w x y := by
    apply le_iInf
    intro p
    exact iInf_le_of_le (p.map T) (le_of_eq (walkLength_map w T hw x y p))
  apply le_antisymm (hle x y)
  simpa only [hT x, hT y] using hle (T x) (T y)

lemma nonexpanding_path {X Y : Type*} [PseudoEMetricSpace Y]
    (w : X → X → ℝ≥0∞) (φ : X → Y)
    (hφ : ∀ x y, edist (φ x) (φ y) ≤ w x y) (x y : X) :
    edist (φ x) (φ y) ≤ pathDistance w x y := by
  apply le_iInf
  intro p
  induction p generalizing x with
  | nil => exact hφ x y
  | cons a p ih =>
      exact (edist_triangle (φ x) (φ a) (φ y)).trans (add_le_add (hφ x a) (ih a))

lemma walkLength_reverse {X : Type*} (w : X → X → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (x y : X) (p : List X) :
    walkLength w y p.reverse x = walkLength w x p y := by
  induction p generalizing x y with
  | nil => exact hsymm y x
  | cons a p ih =>
      rw [List.reverse_cons, walkLength_append, ih, walkLength, walkLength,
        hsymm a x, add_comm]

lemma pathDistance_symm {X : Type*} (w : X → X → ℝ≥0∞)
    (hsymm : ∀ x y, w x y = w y x) (x y : X) :
    pathDistance w x y = pathDistance w y x := by
  have hle (x y : X) : pathDistance w x y ≤ pathDistance w y x := by
    apply le_iInf
    intro p
    exact iInf_le_of_le p.reverse (le_of_eq (walkLength_reverse w hsymm y x p))
  exact le_antisymm (hle x y) (hle y x)

noncomputable abbrev linkPseudoEMetric {X : Type*} (w : X → X → ℝ≥0∞)
    (hrefl : ∀ x, w x x = 0) (hsymm : ∀ x y, w x y = w y x) :
    PseudoEMetricSpace X :=
  PseudoEMetricSpace.ofEDist (pathDistance w) (pathDistance_self w hrefl)
    (pathDistance_symm w hsymm) (pathDistance_triangle w)

noncomputable def circleRep (z : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 z).val

lemma circleRep_nonneg (z : UnitAddCircle) : 0 ≤ circleRep z :=
  (AddCircle.equivIco (1 : ℝ) 0 z).property.1

lemma circleRep_lt_one (z : UnitAddCircle) : circleRep z < 1 := by
  simpa only [circleRep, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).property.2

lemma circleRep_coe (z : UnitAddCircle) : (circleRep z : UnitAddCircle) = z :=
  AddCircle.coe_equivIco

noncomputable def circleColor (z : UnitAddCircle) : Fin 3 :=
  if circleRep z < 1 / 3 then 0 else if circleRep z < 2 / 3 then 1 else 2

lemma circleColor_bounds (z : UnitAddCircle) :
    ((circleColor z).val : ℝ) / 3 ≤ circleRep z ∧
      circleRep z < ((circleColor z).val + 1 : ℝ) / 3 := by
  unfold circleColor
  split_ifs with h1 h2
  · norm_num only [Fin.val_zero, Nat.cast_zero, zero_div, zero_add]
    exact ⟨circleRep_nonneg z, h1⟩
  · norm_num only [Fin.val_one, Nat.cast_one]
    exact ⟨le_of_not_gt h1, by linarith⟩
  · change (2 : ℝ) / 3 ≤ circleRep z ∧ circleRep z < (2 + 1) / 3
    exact ⟨le_of_not_gt h2, by linarith [circleRep_lt_one z]⟩

lemma circle_dist_le_reps (x y : UnitAddCircle) :
    dist x y ≤ |circleRep x - circleRep y| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (1 : ℝ)) (m := circleRep x - circleRep y)
  calc
    dist x y = ‖((circleRep x - circleRep y : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub, circleRep_coe, circleRep_coe, dist_eq_norm]
    _ ≤ ‖circleRep x - circleRep y‖ := h
    _ = |circleRep x - circleRep y| := Real.norm_eq_abs _

lemma circle_same_color_close {x y : UnitAddCircle}
    (h : circleColor x = circleColor y) : dist x y < 1 / 3 := by
  have hx := circleColor_bounds x
  have hy := circleColor_bounds y
  rw [h] at hx
  apply (circle_dist_le_reps x y).trans_lt
  rw [abs_lt]
  constructor <;> linarith

lemma circle_antipode_distance (x : UnitAddCircle) :
    dist x (x + ((1 / 2 : ℝ) : UnitAddCircle)) = 1 / 2 := by
  rw [dist_self_add_right]
  simpa only [abs_one] using AddCircle.norm_half_period_eq (1 : ℝ)

theorem phase_completeness {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (φ : X → UnitAddCircle)
    (hφ : ∀ x y, edist (φ x) (φ y) ≤ w x y)
    (hhalf : ∀ x, φ (T x) = φ x + ((1 / 2 : ℝ) : UnitAddCircle)) :
    (∀ x, ¬pathDistance w x (T x) ≤ ENNReal.ofReal (1 / 8)) ∧
    (∀ (V : Type*) (location : V → X), ∀ u v,
      pathDistance w (location u) (T (location v)) ≤ ENNReal.ofReal (1 / 8) →
      circleColor (φ (location u)) ≠ circleColor (φ (location v))) := by
  constructor
  · intro x hx
    have h := (nonexpanding_path w φ hφ x (T x)).trans hx
    rw [hhalf, edist_dist, circle_antipode_distance] at h
    norm_num at h
  · intro V location u v hedge hcolor
    have h := (nonexpanding_path w φ hφ (location u) (T (location v))).trans hedge
    rw [hhalf, edist_dist, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h
    have hclose := circle_same_color_close hcolor
    have htri := dist_triangle (φ (location v)) (φ (location u))
      (φ (location v) + ((1 / 2 : ℝ) : UnitAddCircle))
    rw [circle_antipode_distance, dist_comm (φ (location v)) (φ (location u))] at htri
    linarith

structure ProjectionSystem (Q : Type*) (M : Q → Type*) where
  imposed : ∀ q q', (M q → M q') → Prop

abbrev GridLocation {Q : Type*} (M : Q → Type*) (D : ℕ) :=
  Σ q, M q → ZMod D

def ProjectionSystem.Consistent {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (a : ∀ q, M q) : Prop :=
  ∀ q q' π, S.imposed q q' π → π (a q) = a q'

inductive ProjectionSystem.ForwardZero {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (D : ℕ) : GridLocation M D → GridLocation M D → Prop
  | link (q q' : Q) (π : M q → M q') (hπ : S.imposed q q' π) (v : M q' → ZMod D) :
    S.ForwardZero D ⟨q, v ∘ π⟩ ⟨q', v⟩

def ProjectionSystem.ZeroLink {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) (D : ℕ) (x y : GridLocation M D) : Prop :=
  S.ForwardZero D x y ∨ S.ForwardZero D y x

noncomputable def copyLength {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : ℝ≥0∞ := by
  classical
  exact if h : x.1 = y.1 then
    ⨆ k : M x.1, edist (ZMod.toAddCircle (x.2 k)) (ZMod.toAddCircle (y.2 (h ▸ k)))
  else ⊤

@[simp] lemma copyLength_same {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (q : Q) (f g : M q → ZMod D) :
    copyLength (⟨q, f⟩ : GridLocation M D) ⟨q, g⟩ =
      ⨆ k, edist (ZMod.toAddCircle (f k)) (ZMod.toAddCircle (g k)) := by
  simp [copyLength]

noncomputable def ProjectionSystem.linkLength {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : ℝ≥0∞ := by
  classical
  exact if S.ZeroLink D x y then 0 else copyLength x y

noncomputable def gridPhase {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (a : ∀ q, M q) (x : GridLocation M D) : UnitAddCircle :=
  ZMod.toAddCircle (x.2 (a x.1))

lemma forwardZero_phase {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    {x y : GridLocation M D} (h : S.ForwardZero D x y) :
    gridPhase a x = gridPhase a y := by
  cases h with
  | link q q' π hπ v => simp only [gridPhase, Function.comp_apply, ha q q' π hπ]

lemma zeroLink_phase {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    {x y : GridLocation M D} (h : S.ZeroLink D x y) :
    gridPhase a x = gridPhase a y := by
  rcases h with h | h
  · exact forwardZero_phase S a ha h
  · exact (forwardZero_phase S a ha h).symm

lemma gridPhase_nonexpanding {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    (x y : GridLocation M D) :
    edist (gridPhase a x) (gridPhase a y) ≤ S.linkLength x y := by
  classical
  unfold ProjectionSystem.linkLength
  split_ifs with hz
  · rw [zeroLink_phase S a ha hz, edist_self]
  · rcases x with ⟨q, f⟩
    rcases y with ⟨q', g⟩
    by_cases hq : q = q'
    · subst q'
      rw [copyLength_same]
      exact le_iSup_of_le (a q) le_rfl
    · simp [copyLength, hq]

def gridAntipode {Q : Type*} {M : Q → Type*} {D : ℕ}
    (x : GridLocation M D) : GridLocation M D :=
  ⟨x.1, fun k => x.2 k + ((D / 2 : ℕ) : ZMod D)⟩

lemma grid_half_real (D : ℕ) [NeZero D] (hD : Even D) :
    ((D / 2 : ℕ) : ℝ) / D = 1 / 2 := by
  have htwo : (D / 2) + (D / 2) = D := by
    obtain ⟨n, hn⟩ := hD
    omega
  have htwoR : ((D / 2 : ℕ) : ℝ) + ((D / 2 : ℕ) : ℝ) = D := by exact_mod_cast htwo
  apply (div_eq_iff (show (D : ℝ) ≠ 0 by exact_mod_cast NeZero.ne D)).mpr
  linarith

lemma gridPhase_antipode {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (hD : Even D) (a : ∀ q, M q) (x : GridLocation M D) :
    gridPhase a (gridAntipode x) = gridPhase a x + ((1 / 2 : ℝ) : UnitAddCircle) := by
  simp only [gridPhase, gridAntipode, map_add, ZMod.toAddCircle_natCast, grid_half_real D hD]

lemma gridAntipode_involutive {Q : Type*} {M : Q → Type*} {D : ℕ} (hD : Even D) :
    Function.Involutive (gridAntipode : GridLocation M D → GridLocation M D) := by
  have htwo : (D / 2) + (D / 2) = D := by
    obtain ⟨n, hn⟩ := hD
    omega
  have hzero : ((D / 2 : ℕ) : ZMod D) + ((D / 2 : ℕ) : ZMod D) = 0 := by
    rw [← Nat.cast_add, htwo]
    exact ZMod.natCast_self D
  rintro ⟨q, f⟩
  simp only [gridAntipode, add_assoc, hzero, add_zero]

theorem projection_grid_completeness {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (a : ∀ q, M q) (ha : S.Consistent a) :
    (∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8)) ∧
    (∀ (V : Type*) (location : V → GridLocation M D), ∀ u v,
      pathDistance S.linkLength (location u) (gridAntipode (location v)) ≤
        ENNReal.ofReal (1 / 8) →
      circleColor (gridPhase a (location u)) ≠ circleColor (gridPhase a (location v))) :=
  phase_completeness S.linkLength gridAntipode (gridPhase a)
    (gridPhase_nonexpanding S a ha) (gridPhase_antipode hD a)

lemma copyLength_self {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x : GridLocation M D) : copyLength x x = 0 := by
  rcases x with ⟨q, f⟩
  simp [copyLength_same]

lemma copyLength_symm {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : copyLength x y = copyLength y x := by
  classical
  rcases x with ⟨q, f⟩
  rcases y with ⟨q', g⟩
  by_cases h : q = q'
  · subst q'
    simp only [copyLength_same, edist_comm]
  · simp [copyLength, h, Ne.symm h]

lemma zeroLink_symm {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (x y : GridLocation M D) : S.ZeroLink D x y ↔ S.ZeroLink D y x :=
  or_comm

lemma linkLength_self {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (x : GridLocation M D) : S.linkLength x x = 0 := by
  classical
  simp [ProjectionSystem.linkLength, copyLength_self]

lemma linkLength_symm {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (x y : GridLocation M D) :
    S.linkLength x y = S.linkLength y x := by
  classical
  simp only [ProjectionSystem.linkLength, zeroLink_symm S x y, copyLength_symm x y]

lemma forwardZero_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} {x y : GridLocation M D} (h : S.ForwardZero D x y) :
    S.ForwardZero D (gridAntipode x) (gridAntipode y) := by
  cases h with
  | link q q' π hπ v =>
      exact .link q q' π hπ (fun k => v k + ((D / 2 : ℕ) : ZMod D))

lemma zeroLink_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} {x y : GridLocation M D} (h : S.ZeroLink D x y) :
    S.ZeroLink D (gridAntipode x) (gridAntipode y) := by
  rcases h with h | h
  · exact Or.inl (forwardZero_antipode S h)
  · exact Or.inr (forwardZero_antipode S h)

lemma zeroLink_antipode_iff {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} (hD : Even D) (x y : GridLocation M D) :
    S.ZeroLink D (gridAntipode x) (gridAntipode y) ↔ S.ZeroLink D x y := by
  constructor
  · intro h
    simpa only [gridAntipode_involutive hD x, gridAntipode_involutive hD y]
      using zeroLink_antipode S h
  · exact zeroLink_antipode S

lemma copyLength_antipode {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (x y : GridLocation M D) : copyLength (gridAntipode x) (gridAntipode y) =
      copyLength x y := by
  classical
  rcases x with ⟨q, f⟩
  rcases y with ⟨q', g⟩
  by_cases h : q = q'
  · subst q'
    simp only [gridAntipode, copyLength_same, map_add, edist_add_right]
  · simp [copyLength, gridAntipode, h]

lemma linkLength_antipode {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (hD : Even D) (x y : GridLocation M D) :
    S.linkLength (gridAntipode x) (gridAntipode y) = S.linkLength x y := by
  classical
  simp only [ProjectionSystem.linkLength, zeroLink_antipode_iff S hD,
    copyLength_antipode]

lemma twisted_pathDistance_symm {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (x y : GridLocation M D) :
    pathDistance S.linkLength x (gridAntipode y) =
      pathDistance S.linkLength y (gridAntipode x) := by
  calc
    _ = pathDistance S.linkLength (gridAntipode x) y := by
      simpa only [gridAntipode_involutive hD y] using
        (pathDistance_invariant S.linkLength gridAntipode (gridAntipode_involutive hD)
          (linkLength_antipode S hD) x (gridAntipode y)).symm
    _ = _ := pathDistance_symm S.linkLength (linkLength_symm S) _ _

noncomputable def gridGraph {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    {V : Type*} (location : V → GridLocation M D) : SimpleGraph V where
  Adj u v := u ≠ v ∧ pathDistance S.linkLength (location u) (gridAntipode (location v)) ≤
    ENNReal.ofReal (1 / 8)
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, by
      rw [twisted_pathDistance_symm S hD]
      exact h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

theorem gridGraph_three_coloring {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (a : ∀ q, M q) (ha : S.Consistent a)
    {V : Type*} (location : V → GridLocation M D) :
    ∃ color : V → Fin 3, ∀ u v, (gridGraph S hD location).Adj u v →
      color u ≠ color v := by
  refine ⟨fun v => circleColor (gridPhase a (location v)), ?_⟩
  intro u v h
  exact (projection_grid_completeness S hD a ha).2 V location u v h.2

end LargeIndependentSets

end OAI
