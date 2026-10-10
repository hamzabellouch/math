import Mathlib

namespace OAI

/-! Solid-box geometry and compactly supported solenoidal extensions of diagonal affine fields. -/

namespace BoxTransport

noncomputable section
open scoped BigOperators ContDiff

abbrev Space := Fin 3 → ℝ
abbrev Spacetime := Fin 4 → ℝ
abbrev RationalPoint := Fin 3 → ℚ
abbrev Velocity := ℝ → Space → Space

def solidBox (c h : Space) : Set Space :=
  {x | ∀ j, |x j - c j| ≤ h j}

def ofRat (q : RationalPoint) : Space := fun j => (q j : ℝ)

def rationalBox (c h : RationalPoint) : Set Space :=
  solidBox (ofRat c) (ofRat h)

def assignedMap (a b h k : RationalPoint) (x : Space) : Space :=
  fun j => (b j : ℝ) + ((k j / h j : ℚ) : ℝ) * (x j - (a j : ℝ))

def inCoordinates (V : Velocity) : Spacetime → Space :=
  fun z => V (z 0) (fun j => z j.succ)

noncomputable def mixedPartial : List (Fin 4) → (Spacetime → Space) → Spacetime → Space
  | [], F => F
  | j :: js, F => fun z => fderiv ℝ (mixedPartial js F) z (Pi.single j 1)

abbrev RationalCode := ℤ × ℕ
abbrev PointCode := RationalCode × RationalCode × RationalCode × RationalCode
abbrev DerivativeQuery := List (Fin 4) × Fin 3 × PointCode × ℕ

def decodeRational (q : RationalCode) : ℝ :=
  (q.1 : ℝ) / ((q.2 : ℝ) + 1)

def decodePoint (q : PointCode) : Spacetime :=
  ![decodeRational q.1, decodeRational q.2.1,
    decodeRational q.2.2.1, decodeRational q.2.2.2]

def dyadicError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def EffectiveField (V : Velocity) : Prop :=
  ∃ evaluate : DerivativeQuery → RationalCode,
  ∃ precision : List (Fin 4) × ℕ → ℕ,
  ∃ bound : List (Fin 4) → ℕ,
    Computable evaluate ∧ Computable precision ∧ Computable bound ∧
    (∀ d j q n z,
      (∀ l, |z l - decodePoint q l| ≤ dyadicError (precision (d, n))) →
      |mixedPartial d (inCoordinates V) z j - decodeRational (evaluate (d, j, q, n))|
        ≤ dyadicError n) ∧
    (∀ d z j, |mixedPartial d (inCoordinates V) z j| ≤ (bound d : ℝ))

noncomputable def divergence (V : Velocity) (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, (fderiv ℝ (V t) x (Pi.single j 1)) j

def Solenoidal (V : Velocity) : Prop := ∀ t x, divergence V t x = 0

def IsMaterialFlow (V : Velocity) (Φ : ℝ → Space → Space) : Prop :=
  (∀ x, Φ 0 x = x) ∧
  ∀ x t, HasDerivAt (fun s => Φ s x) (V t (Φ t x)) t

def RoutingConclusion {N : ℕ} (a b h k : Fin N → RationalPoint) : Prop :=
  ∃ V : Velocity, ∃ Φ : ℝ → Space → Space,
    ContDiff ℝ ∞ (inCoordinates V) ∧
    HasCompactSupport (inCoordinates V) ∧
    Solenoidal V ∧
    (∀ t, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → ∀ x, V t x = 0) ∧
    EffectiveField V ∧
    IsMaterialFlow V Φ ∧
    ∀ i, ∃ U : Set Space, IsOpen U ∧ rationalBox (a i) (h i) ⊆ U ∧
      ∀ x ∈ U, Φ 1 x = assignedMap (a i) (b i) (h i) (k i) x

@[simp] theorem mem_solidBox {c h x : Space} :
    x ∈ solidBox c h ↔ ∀ j, |x j - c j| ≤ h j := Iff.rfl

theorem center_mem_solidBox (c h : Space) (hh : ∀ j, 0 ≤ h j) :
    c ∈ solidBox c h := by
  simpa only [mem_solidBox, sub_self, abs_zero] using hh

theorem solidBox_eq_pi (c h : Space) :
    solidBox c h = Set.univ.pi (fun j => Set.Icc (c j - h j) (c j + h j)) := by
  ext x
  simp only [mem_solidBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  apply forall_congr'
  intro j
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem isCompact_solidBox (c h : Space) : IsCompact (solidBox c h) := by
  rw [solidBox_eq_pi]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem disjoint_solidBox_of_gap {a b h k : Space} {j : Fin 3}
    (hgap : h j + k j < |a j - b j|) :
    Disjoint (solidBox a h) (solidBox b k) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  have ha := (abs_le.mp (hxa j))
  have hb := (abs_le.mp (hxb j))
  have : |a j - b j| ≤ h j + k j := abs_le.mpr (by constructor <;> linarith)
  exact (not_lt_of_ge this) hgap

theorem disjoint_solidBox_iff {a b h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (solidBox a h) (solidBox b k) ↔
      ∃ j, h j + k j < |a j - b j| := by
  constructor
  · intro hd
    by_contra! hgap
    let x : Space := fun j => max (a j - h j) (b j - k j)
    have hxa : x ∈ solidBox a h := by
      intro j
      have hj := abs_le.mp (hgap j)
      have hl : a j - h j ≤ x j := le_max_left _ _
      have hu : x j ≤ a j + h j := max_le (by linarith [hh j]) (by linarith)
      exact abs_le.mpr (by constructor <;> linarith)
    have hxb : x ∈ solidBox b k := by
      intro j
      have hj := abs_le.mp (hgap j)
      have hl : b j - k j ≤ x j := le_max_right _ _
      have hu : x j ≤ b j + k j := max_le (by linarith) (by linarith [hk j])
      exact abs_le.mpr (by constructor <;> linarith)
    exact Set.disjoint_left.mp hd hxa hxb
  · rintro ⟨j, hj⟩
    exact disjoint_solidBox_of_gap hj

theorem centers_ne_of_disjoint {a b h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j)
    (hd : Disjoint (solidBox a h) (solidBox b k)) : a ≠ b := by
  intro hab
  subst b
  exact Set.disjoint_left.mp hd (center_mem_solidBox a h hh)
    (center_mem_solidBox a k hk)

theorem gap_le_expanded_gap (a b h k : Space) (j : Fin 3) {lam : ℝ}
    (hlam : 1 ≤ lam) :
    |a j - b j| - h j - k j ≤ |lam * a j - lam * b j| - h j - k j := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ lam)]
  nlinarith [abs_nonneg (a j - b j)]

theorem disjoint_solidBox_expand {a b h k : Space} {lam : ℝ}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) (hlam : 1 ≤ lam)
    (hd : Disjoint (solidBox a h) (solidBox b k)) :
    Disjoint (solidBox (fun j => lam * a j) h) (solidBox (fun j => lam * b j) k) := by
  obtain ⟨j, hj⟩ := (disjoint_solidBox_iff hh hk).mp hd
  apply disjoint_solidBox_of_gap (j := j)
  have hg := gap_le_expanded_gap a b h k j hlam
  linarith

theorem disjoint_padded_solidBox {a b h k : Space} {η : ℝ} {j : Fin 3}
    (hgap : 4 * η < |a j - b j| - h j - k j) :
    Disjoint (solidBox a (fun j => h j + 2 * η))
      (solidBox b (fun j => k j + 2 * η)) := by
  apply disjoint_solidBox_of_gap (j := j)
  linarith

def diagonalAffine (a b s : Space) (x : Space) : Space :=
  fun j => b j + s j * (x j - a j)

theorem diagonalAffine_mem_iff {a b h s x : Space} (hs : ∀ j, 0 < s j) :
    diagonalAffine a b s x ∈ solidBox b (fun j => s j * h j) ↔
      x ∈ solidBox a h := by
  simp only [mem_solidBox, diagonalAffine, add_sub_cancel_left, abs_mul,
    abs_of_pos (hs _), mul_le_mul_iff_right₀ (hs _)]

theorem diagonalAffine_inverse (a b s x : Space) (hs : ∀ j, s j ≠ 0) :
    diagonalAffine b a (fun j => (s j)⁻¹) (diagonalAffine a b s x) = x := by
  ext j
  simp only [diagonalAffine, add_sub_cancel_left]
  rw [← mul_assoc, inv_mul_cancel₀ (hs j), one_mul]
  ring

theorem diagonalAffine_image (a b h s : Space) (hs : ∀ j, 0 < s j) :
    diagonalAffine a b s '' solidBox a h = solidBox b (fun j => s j * h j) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (diagonalAffine_mem_iff hs).mpr hy
  · intro hx
    let y := diagonalAffine b a (fun j => (s j)⁻¹) x
    have hxy : diagonalAffine a b s y = x := by
      ext j
      dsimp [y, diagonalAffine]
      rw [add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hs j)), one_mul]
      ring
    refine ⟨y, ?_, hxy⟩
    exact (diagonalAffine_mem_iff hs).mp (hxy.symm ▸ hx)

theorem assignedMap_image (a b h k : RationalPoint)
    (hh : ∀ j, 0 < h j) (hk : ∀ j, 0 < k j) :
    assignedMap a b h k '' rationalBox a h = rationalBox b k := by
  let s : Space := fun j => (k j : ℝ) / (h j : ℝ)
  have hs : ∀ j, 0 < s j := fun j => div_pos (by exact_mod_cast hk j)
    (by exact_mod_cast hh j)
  have hw : (fun j => s j * ofRat h j) = ofRat k := by
    funext j
    dsimp [s, ofRat]
    exact div_mul_cancel₀ _ (by exact_mod_cast (ne_of_gt (hh j)))
  have hf : assignedMap a b h k = diagonalAffine (ofRat a) (ofRat b) s := by
    ext x j
    simp [assignedMap, diagonalAffine, ofRat, s]
  rw [rationalBox, hf, diagonalAffine_image _ _ _ _ hs, hw]
  rfl

theorem rationalBox_separating_coordinate {a b h k : RationalPoint}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j)
    (hd : Disjoint (rationalBox a h) (rationalBox b k)) :
    ∃ j, 0 < |a j - b j| - h j - k j := by
  obtain ⟨j, hj⟩ := (disjoint_solidBox_iff
    (fun j => show 0 ≤ (h j : ℝ) by exact_mod_cast hh j)
    (fun j => show 0 ≤ (k j : ℝ) by exact_mod_cast hk j)).mp hd
  refine ⟨j, ?_⟩
  change (h j : ℝ) + (k j : ℝ) < |(a j : ℝ) - (b j : ℝ)| at hj
  have hjq : h j + k j < |a j - b j| := by exact_mod_cast hj
  linarith

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ ε : ℚ, 0 < ε ∧ ∀ i ∈ s, ε < f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s has ih =>
      obtain ⟨ε, hε, hεs⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have ha : 0 < f a := hf a (Finset.mem_insert_self _ _)
      refine ⟨min ε (f a / 2), lt_min hε (by linarith), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hεs i his)

theorem exists_uniform_rational_gap {N : ℕ} (a h : Fin N → RationalPoint)
    (hh : ∀ i j, 0 ≤ h i j)
    (hd : Pairwise (fun i l => Disjoint (rationalBox (a i) (h i))
      (rationalBox (a l) (h l)))) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ i l, i ≠ l →
      ∃ j, δ < |a i j - a l j| - h i j - h l j := by
  classical
  let P := {p : Fin N × Fin N // p.1 ≠ p.2}
  have hp : ∀ p : P, ∃ j, 0 < |a p.1.1 j - a p.1.2 j| - h p.1.1 j - h p.1.2 j :=
    fun p => @rationalBox_separating_coordinate (a p.1.1) (a p.1.2) (h p.1.1) (h p.1.2)
      (hh _) (hh _) (hd p.2)
  let j : P → Fin 3 := fun p => Classical.choose (hp p)
  let g : P → ℚ := fun p =>
    |a p.1.1 (j p) - a p.1.2 (j p)| - h p.1.1 (j p) - h p.1.2 (j p)
  have hg : ∀ p : P, 0 < g p := fun p => Classical.choose_spec (hp p)
  obtain ⟨δ, hδ, hδp⟩ := finite_positive_lower_bound Finset.univ g (fun p _ => hg p)
  refine ⟨δ, hδ, ?_⟩
  intro i l hil
  exact ⟨j ⟨(i, l), hil⟩, hδp ⟨(i, l), hil⟩ (Finset.mem_univ _)⟩

theorem exists_common_center_expansion {N : ℕ} (a b : Fin N → RationalPoint)
    (ha : Function.Injective a) (hb : Function.Injective b) (R : ℚ) :
    ∃ L : ℚ, 10 < L ∧
      (∀ i l, i ≠ l → ∃ j, 20 * R < |L * a i j - L * a l j|) ∧
      (∀ i l, i ≠ l → ∃ j, 20 * R < |L * b i j - L * b l j|) := by
  let f : Fin N × Fin N × Fin 3 → ℚ := fun p =>
    max (20 * |R| / |a p.1 p.2.2 - a p.2.1 p.2.2|)
        (20 * |R| / |b p.1 p.2.2 - b p.2.1 p.2.2|)
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  let L := max 11 (M + 1)
  have hL : 10 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hML : M < L := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have bound : ∀ p, f p < L :=
    fun p => lt_of_le_of_lt (hM (Set.mem_range_self p)) hML
  have expand : ∀ c : Fin N → RationalPoint, Function.Injective c →
      (∀ i l j, 20 * |R| / |c i j - c l j| < L) →
      ∀ i l, i ≠ l → ∃ j, 20 * R < |L * c i j - L * c l j| := by
    intro c hc hbound i l hil
    have hne : c i ≠ c l := fun h => hil (hc h)
    have hex : ∃ j, c i j ≠ c l j := by
      by_contra! hall
      exact hne (funext hall)
    obtain ⟨j, hj⟩ := hex
    have hd : 0 < |c i j - c l j| := abs_pos.mpr (sub_ne_zero.mpr hj)
    have hm := (div_lt_iff₀ hd).mp (hbound i l j)
    refine ⟨j, ?_⟩
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith : 0 < L)]
    nlinarith [le_abs_self R]
  refine ⟨L, hL, expand a ha ?_, expand b hb ?_⟩
  · intro i l j
    exact lt_of_le_of_lt (le_max_left _ _) (bound (i, l, j))
  · intro i l j
    exact lt_of_le_of_lt (le_max_right _ _) (bound (i, l, j))

theorem rational_centers_injective {N : ℕ} (a h : Fin N → RationalPoint)
    (hh : ∀ i j, 0 ≤ h i j)
    (hd : Pairwise (fun i l => Disjoint (rationalBox (a i) (h i))
      (rationalBox (a l) (h l)))) : Function.Injective a := by
  intro i l hil
  by_contra hne
  have hn := centers_ne_of_disjoint
    (fun j => show 0 ≤ (h i j : ℝ) by exact_mod_cast hh i j)
    (fun j => show 0 ≤ (h l j : ℝ) by exact_mod_cast hh l j) (hd hne)
  exact hn (congrArg ofRat hil)

theorem disjoint_padded_of_center_clearance {a b h k : Space} {R η : ℝ}
    (hh : ∀ j, h j ≤ R) (hk : ∀ j, k j ≤ R)
    (hη : η < R / 2) (hclear : ∃ j, 4 * R ≤ |a j - b j|) :
    Disjoint (solidBox a (fun j => h j + 2 * η))
      (solidBox b (fun j => k j + 2 * η)) := by
  obtain ⟨j, hj⟩ := hclear
  apply disjoint_padded_solidBox (j := j)
  linarith [hh j, hk j]

def shapeScale (s : Space) (θ : ℝ) : Space :=
  fun j => Real.exp (θ * Real.log (s j))

@[simp] theorem shapeScale_zero (s : Space) : shapeScale s 0 = (fun _ => 1) := by
  ext j
  simp [shapeScale]

@[simp] theorem shapeScale_one (s : Space) (hs : ∀ j, 0 < s j) : shapeScale s 1 = s := by
  ext j
  simp [shapeScale, Real.exp_log (hs j)]

theorem shapeScale_pos (s : Space) (θ : ℝ) (j : Fin 3) : 0 < shapeScale s θ j :=
  Real.exp_pos _

theorem sum_log_eq_zero {s : Space} (hs : ∀ j, 0 < s j)
    (hbal : ∏ j, s j = 1) : ∑ j, Real.log (s j) = 0 := by
  rw [← Real.log_prod (fun j _ => ne_of_gt (hs j)), hbal, Real.log_one]

theorem shapeScale_balanced {s : Space} (hs : ∀ j, 0 < s j)
    (hbal : ∏ j, s j = 1) (θ : ℝ) : ∏ j, shapeScale s θ j = 1 := by
  simp only [shapeScale]
  rw [← Real.exp_sum, ← Finset.mul_sum, sum_log_eq_zero hs hbal, mul_zero, Real.exp_zero]

theorem shapeScale_det_eq_one {s : Space} (hs : ∀ j, 0 < s j)
    (hbal : ∏ j, s j = 1) (θ : ℝ) :
    (Matrix.diagonal (shapeScale s θ)).det = 1 := by
  rw [Matrix.det_diagonal]
  exact shapeScale_balanced hs hbal θ

theorem geometric_width_eq {h k : ℝ} (hh : 0 < h) (hk : 0 < k) (θ : ℝ) :
    h * Real.exp (θ * Real.log (k / h)) =
      Real.exp ((1 - θ) * Real.log h + θ * Real.log k) := by
  rw [Real.log_div (ne_of_gt hk) (ne_of_gt hh)]
  calc
    h * Real.exp (θ * (Real.log k - Real.log h)) =
        Real.exp (Real.log h) * Real.exp (θ * (Real.log k - Real.log h)) := by
          rw [Real.exp_log hh]
    _ = Real.exp ((1 - θ) * Real.log h + θ * Real.log k) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem geometric_width_le_max {h k θ : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    h * Real.exp (θ * Real.log (k / h)) ≤ max h k := by
  rw [geometric_width_eq hh hk]
  have hm : 0 < max h k := lt_of_lt_of_le hh (le_max_left _ _)
  conv_rhs => rw [← Real.exp_log hm]
  apply Real.exp_le_exp.mpr
  have hhlog := Real.log_le_log hh (le_max_left h k)
  have hklog := Real.log_le_log hk (le_max_right h k)
  have h₁ := mul_le_mul_of_nonneg_left hhlog (sub_nonneg.mpr hθ.2)
  have h₂ := mul_le_mul_of_nonneg_left hklog hθ.1
  nlinarith

theorem shapeScale_width_bound {h k : Space} (hh : ∀ j, 0 < h j)
    (hk : ∀ j, 0 < k j) {R θ : ℝ}
    (hhR : ∀ j, h j ≤ R) (hkR : ∀ j, k j ≤ R) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ j, h j * shapeScale (fun l => k l / h l) θ j ≤ R := by
  intro j
  exact le_trans (geometric_width_le_max (hh j) (hk j) hθ) (max_le (hhR j) (hkR j))

theorem real_balance_of_rational {s : RationalPoint} (hs : ∏ j, s j = 1) :
    ∏ j, (s j : ℝ) = 1 := by
  exact_mod_cast hs

@[simp] theorem mixedPartial_zero (d : List (Fin 4)) :
    mixedPartial d (fun _ : Spacetime => (0 : Space)) = (fun _ => 0) := by
  induction d with
  | nil => rfl
  | cons j d ih =>
      funext z
      simp [mixedPartial, ih]

theorem effective_zero : EffectiveField (fun _ _ => 0) := by
  have h0 : inCoordinates (fun _ _ => 0) = (fun _ : Spacetime => (0 : Space)) := rfl
  refine ⟨(fun _ => (0, 0)), (fun _ => 0), (fun _ => 0),
    Computable.const _, Computable.const _, Computable.const _, ?_, ?_⟩
  · intro d j q n z _
    rw [h0, mixedPartial_zero]
    simp only [decodeRational, Int.cast_zero,
      Nat.cast_zero, zero_div, Pi.zero_apply, sub_self, abs_zero]
    exact pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) n
  · intro d z j
    rw [h0, mixedPartial_zero]
    simp only [Nat.cast_zero, Pi.zero_apply, abs_zero,
      le_refl]

theorem solenoidal_zero : Solenoidal (fun _ _ => 0) := by
  intro t x
  simp [divergence]

theorem identity_isMaterialFlow : IsMaterialFlow (fun _ _ => 0) (fun _ x => x) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro x t
  exact hasDerivAt_const t x

theorem routingConclusion_empty (a b h k : Fin 0 → RationalPoint) :
    RoutingConclusion a b h k := by
  refine ⟨(fun _ _ => 0), (fun _ x => x), contDiff_const,
    HasCompactSupport.zero, solenoidal_zero, ?_, effective_zero,
    identity_isMaterialFlow, ?_⟩
  · intro t ht x
    rfl
  · intro i
    exact Fin.elim0 i

theorem assignedMap_self (a h : RationalPoint) (hh : ∀ j, h j ≠ 0) (x : Space) :
    assignedMap a a h h x = x := by
  ext j
  simp [assignedMap, div_self (hh j)]

theorem routingConclusion_reflexive {N : ℕ} (a h : Fin N → RationalPoint)
    (hh : ∀ i j, h i j ≠ 0) : RoutingConclusion a a h h := by
  refine ⟨(fun _ _ => 0), (fun _ x => x), contDiff_const,
    HasCompactSupport.zero, solenoidal_zero, ?_, effective_zero,
    identity_isMaterialFlow, ?_⟩
  · intro t ht x
    rfl
  · intro i
    exact ⟨Set.univ, isOpen_univ, Set.subset_univ _,
      fun x _ => (assignedMap_self _ _ (hh i) x).symm⟩

def direction (j : Fin 3) : Space := Pi.single j 1

def jacobianEntry (i j : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.apply ℝ Space) (direction j))

def curlFromJacobian : (Space →L[ℝ] Space) →L[ℝ] Space :=
  ContinuousLinearMap.pi ![jacobianEntry 2 1 - jacobianEntry 1 2,
    jacobianEntry 0 2 - jacobianEntry 2 0,
    jacobianEntry 1 0 - jacobianEntry 0 1]

noncomputable def curl (A : Space → Space) : Space → Space :=
  curlFromJacobian ∘ fderiv ℝ A

theorem curl_apply (A : Space → Space) (x : Space) :
    curl A x = ![(fderiv ℝ A x (direction 1)) 2 - (fderiv ℝ A x (direction 2)) 1,
      (fderiv ℝ A x (direction 2)) 0 - (fderiv ℝ A x (direction 0)) 2,
      (fderiv ℝ A x (direction 0)) 1 - (fderiv ℝ A x (direction 1)) 0] := by
  ext j
  fin_cases j <;> rfl

theorem contDiff_curl {A : Space → Space} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (curl A) := by
  exact curlFromJacobian.contDiff.comp (hA.fderiv_right (by simp))

theorem hasCompactSupport_curl {A : Space → Space} (hA : HasCompactSupport A) :
    HasCompactSupport (curl A) :=
  (hA.fderiv ℝ).comp_left (map_zero curlFromJacobian)

theorem divergence_curl {A : Space → Space} (hA : ContDiff ℝ ∞ A) (t : ℝ) (x : Space) :
    divergence (fun _ => curl A) t x = 0 := by
  have hdA : Differentiable ℝ (fderiv ℝ A) :=
    (hA.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hder : fderiv ℝ (curl A) x = curlFromJacobian.comp (fderiv ℝ (fderiv ℝ A) x) := by
    exact (curlFromJacobian.hasFDerivAt.comp x (hdA x).hasFDerivAt).fderiv
  have hsym := hA.contDiffAt (x := x) |>.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  unfold divergence
  rw [hder, Fin.sum_univ_three]
  change
    ((fderiv ℝ (fderiv ℝ A) x (direction 0)) (direction 1)) 2 -
      ((fderiv ℝ (fderiv ℝ A) x (direction 0)) (direction 2)) 1 +
      (((fderiv ℝ (fderiv ℝ A) x (direction 1)) (direction 2)) 0 -
      ((fderiv ℝ (fderiv ℝ A) x (direction 1)) (direction 0)) 2) +
      (((fderiv ℝ (fderiv ℝ A) x (direction 2)) (direction 0)) 1 -
      ((fderiv ℝ (fderiv ℝ A) x (direction 2)) (direction 1)) 0) = 0
  rw [hsym.eq (direction 0) (direction 1), hsym.eq (direction 0) (direction 2),
    hsym.eq (direction 1) (direction 2)]
  ring

theorem curl_eq_of_eventuallyEq {A B : Space → Space} {x : Space}
    (hAB : A =ᶠ[nhds x] B) : curl A x = curl B x := by
  simp only [curl, Function.comp_apply, hAB.fderiv_eq]

theorem curl_cutoff_eq {χ : Space → ℝ} (A : Space → Space) {x : Space}
    (hχ : χ =ᶠ[nhds x] (fun _ => 1)) :
    curl (fun y => χ y • A y) x = curl A x := by
  apply curl_eq_of_eventuallyEq
  filter_upwards [hχ] with y hy
  simp [hy]

def potentialComponent (c v l : Space) (i j : Fin 3) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (v i * (x j - c j) - v j * (x i - c i)) +
    ((1 / 3 : ℝ) * (l i - l j)) * (x i - c i) * (x j - c j)

def affinePotential (c v l : Space) (x : Space) : Space :=
  ![potentialComponent c v l 1 2 x, potentialComponent c v l 2 0 x,
    potentialComponent c v l 0 1 x]

theorem affinePotential_eq_cross (c v l x : Space) :
    affinePotential c v l x = (1 / 2 : ℝ) • crossProduct v (x - c) +
      (1 / 3 : ℝ) • crossProduct (fun j => l j * (x j - c j)) (x - c) := by
  ext j
  fin_cases j <;> simp [affinePotential, potentialComponent, cross_apply] <;> ring

theorem contDiff_potentialComponent (c v l : Space) (i j : Fin 3) :
    ContDiff ℝ ∞ (potentialComponent c v l i j) := by
  unfold potentialComponent
  fun_prop

theorem contDiff_affinePotential (c v l : Space) : ContDiff ℝ ∞ (affinePotential c v l) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact contDiff_potentialComponent c v l 1 2
  · exact contDiff_potentialComponent c v l 2 0
  · exact contDiff_potentialComponent c v l 0 1

theorem potentialComponent_fderiv (c v l x z : Space) (i j : Fin 3) :
    fderiv ℝ (potentialComponent c v l i j) x z =
      (1 / 2 : ℝ) * (v i * z j - v j * z i) +
        ((1 / 3 : ℝ) * (l i - l j)) * ((x i - c i) * z j + (x j - c j) * z i) := by
  have hi := HasFDerivAt.sub_const (c i) (hasFDerivAt_apply (𝕜 := ℝ) i x)
  have hj := HasFDerivAt.sub_const (c j) (hasFDerivAt_apply (𝕜 := ℝ) j x)
  have hlin := ((hj.const_mul (v i)).sub (hi.const_mul (v j))).const_mul (1 / 2 : ℝ)
  have hquad := (hi.const_mul ((1 / 3 : ℝ) * (l i - l j))).mul hj
  have hd := hlin.add hquad
  change HasFDerivAt (potentialComponent c v l i j) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, sub_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem curl_affinePotential (c v l x : Space) :
    curl (affinePotential c v l) x =
      fun j => v j + l j * (x j - c j) - (∑ i, l i) / 3 * (x j - c j) := by
  have hentry (i j : Fin 3) :
      (fderiv ℝ (affinePotential c v l) x (direction j)) i =
        fderiv ℝ (fun y => affinePotential c v l y i) x (direction j) := by
    rw [fderiv_apply ((contDiff_affinePotential c v l).differentiable (by simp) x)]
    rfl
  rw [curl_apply]
  ext j
  fin_cases j <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    rw [hentry, hentry] <;>
    simp only [affinePotential, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    rw [potentialComponent_fderiv, potentialComponent_fderiv] <;>
    simp [direction, Fin.sum_univ_three] <;> ring

theorem curl_affinePotential_trace_zero (c v l x : Space) (hl : ∑ j, l j = 0) :
    curl (affinePotential c v l) x = (fun j => v j + l j * (x j - c j)) := by
  simpa only [hl, zero_div, zero_mul, sub_zero] using curl_affinePotential c v l x

theorem localized_affine_extension (c v l : Space) (hl : ∑ j, l j = 0)
    {U : Set Space} (hU : IsOpen U) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hplateau : Set.EqOn χ (fun _ => 1) U) :
    ∃ W : Space → Space, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      Solenoidal (fun _ => W) ∧
      Set.EqOn W (fun x j => v j + l j * (x j - c j)) U := by
  have hA : ContDiff ℝ ∞ (fun y => χ y • affinePotential c v l y) :=
    hχ.smul (contDiff_affinePotential c v l)
  refine ⟨curl (fun y => χ y • affinePotential c v l y), contDiff_curl hA,
    hasCompactSupport_curl hχc.smul_right, ?_, ?_⟩
  · exact divergence_curl hA
  · intro x hx
    have he : χ =ᶠ[nhds x] (fun _ => 1) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hplateau hy
    rw [curl_cutoff_eq _ he, curl_affinePotential_trace_zero c v l x hl]

def openBox (c h : Space) : Set Space := {x | ∀ j, |x j - c j| < h j}

theorem isOpen_openBox (c h : Space) : IsOpen (openBox c h) := by
  change IsOpen {x : Space | ∀ j, |x j - c j| < h j}
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (((continuous_apply j).sub continuous_const).abs) continuous_const

theorem solidBox_subset_openBox_padded (c h : Space) {η : ℝ} (hη : 0 < η) :
    solidBox c h ⊆ openBox c (fun j => h j + η) := by
  intro x hx j
  exact lt_of_le_of_lt (hx j) (lt_add_of_pos_right _ hη)

theorem exists_padded_box_cutoff (c h : Space) (hh : ∀ j, 0 ≤ h j)
    {η : ℝ} (hη : 0 < η) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ solidBox c (fun j => h j + 2 * η) ∧
      Set.EqOn χ (fun _ => 1) (solidBox c (fun j => h j + η)) := by
  let f (j : Fin 3) : ContDiffBump (c j) :=
    { rIn := h j + η
      rOut := h j + 2 * η
      rIn_pos := by linarith [hh j]
      rIn_lt_rOut := by linarith }
  let χ : Space → ℝ := fun x => ∏ j, f j (x j)
  have hs : Function.support χ ⊆ solidBox c (fun j => h j + 2 * η) := by
    intro x hx j
    have hxj : f j (x j) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx) j (Finset.mem_univ _)
    have hj : x j ∈ Metric.ball (c j) (f j).rOut := by
      rw [← (f j).support_eq]
      exact hxj
    exact le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq, f] using hj)
  refine ⟨χ, ?_, HasCompactSupport.of_support_subset_isCompact
    (isCompact_solidBox _ _) hs, closure_minimal hs (isCompact_solidBox _ _).isClosed, ?_⟩
  · exact contDiff_prod (fun j _ => (f j).contDiff.comp (contDiff_apply ℝ ℝ j))
  · intro x hx
    apply Finset.prod_eq_one
    intro j _
    apply (f j).one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, f] using hx j

theorem tsupport_curl_subset (A : Space → Space) : tsupport (curl A) ⊆ tsupport A :=
  (tsupport_comp_subset (map_zero curlFromJacobian) (fderiv ℝ A)).trans
    (tsupport_fderiv_subset ℝ)

theorem affine_extension_on_box (c h v l : Space)
    (hh : ∀ j, 0 ≤ h j) (hl : ∑ j, l j = 0) {η : ℝ} (hη : 0 < η) :
    ∃ W : Space → Space, ∃ U : Set Space,
      IsOpen U ∧ solidBox c h ⊆ U ∧
      ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ solidBox c (fun j => h j + 2 * η) ∧
      Solenoidal (fun _ => W) ∧
      Set.EqOn W (fun x j => v j + l j * (x j - c j)) U := by
  obtain ⟨χ, hχ, hχc, hχs, hχp⟩ := exists_padded_box_cutoff c h hh hη
  let U := openBox c (fun j => h j + η)
  have hU : IsOpen U := isOpen_openBox _ _
  have hplateau : Set.EqOn χ (fun _ => 1) U := by
    intro x hx
    exact hχp (fun j => (hx j).le)
  let A : Space → Space := fun x => χ x • affinePotential c v l x
  have hA : ContDiff ℝ ∞ A := hχ.smul (contDiff_affinePotential c v l)
  refine ⟨curl A, U, hU, solidBox_subset_openBox_padded _ _ hη,
    contDiff_curl hA, hasCompactSupport_curl hχc.smul_right,
    (tsupport_curl_subset A).trans ((tsupport_smul_subset_left χ _).trans hχs),
    divergence_curl hA, ?_⟩
  intro x hx
  have he : χ =ᶠ[nhds x] (fun _ => 1) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hplateau hy
  exact (curl_cutoff_eq _ he).trans (curl_affinePotential_trace_zero c v l x hl)

theorem contDiff_shapeScale (s : Space) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (fun t => shapeScale s (θ t)) := by
  exact contDiff_pi.mpr (fun j => (hθ.mul contDiff_const).exp)

theorem hasDerivAt_shapeScale (s : Space) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun u => shapeScale s (θ u))
      (fun j => θ' * Real.log (s j) * shapeScale s (θ t) j) t := by
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt (fun u => Real.exp (θ u * Real.log (s j)))
    (θ' * Real.log (s j) * Real.exp (θ t * Real.log (s j))) t
  convert (hθ.mul_const (Real.log (s j))).exp using 1
  ring

theorem sum_logarithmic_rate {s : Space} (hs : ∀ j, 0 < s j)
    (hbal : ∏ j, s j = 1) (θ' : ℝ) : ∑ j, θ' * Real.log (s j) = 0 := by
  rw [← Finset.mul_sum, sum_log_eq_zero hs hbal, mul_zero]

def shapeMotion (a : Space) (c : ℝ → Space) (s : Space) (θ : ℝ → ℝ)
    (t : ℝ) (x : Space) : Space :=
  fun j => c t j + shapeScale s (θ t) j * (x j - a j)

theorem shapeMotion_hasDerivAt (a s x : Space) {c : ℝ → Space} {c' : Space}
    {θ : ℝ → ℝ} {θ' t : ℝ} (hc : HasDerivAt c c' t) (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun u => shapeMotion a c s θ u x)
      (fun j => c' j + θ' * Real.log (s j) * (shapeMotion a c s θ t x j - c t j)) t := by
  apply hasDerivAt_pi.mpr
  intro j
  have hD := hasDerivAt_pi.mp (hasDerivAt_shapeScale s hθ) j
  have hd := (hasDerivAt_pi.mp hc j).add (hD.mul_const (x j - a j))
  change HasDerivAt (fun u => c u j + shapeScale s (θ u) j * (x j - a j)) _ t at hd
  simpa only [shapeMotion, add_sub_cancel_left, mul_assoc] using hd

theorem shapeMotion_start (a s x : Space) {c : ℝ → Space} {θ : ℝ → ℝ} {t : ℝ}
    (hc : c t = a) (hθ : θ t = 0) : shapeMotion a c s θ t x = x := by
  ext j
  simp [shapeMotion, hc, hθ]

theorem shapeMotion_finish (a b s x : Space) {c : ℝ → Space} {θ : ℝ → ℝ} {t : ℝ}
    (hs : ∀ j, 0 < s j) (hc : c t = b) (hθ : θ t = 1) :
    shapeMotion a c s θ t x = diagonalAffine a b s x := by
  ext j
  simp [shapeMotion, hc, hθ, shapeScale_one s hs, diagonalAffine]

theorem diagonalAffine_perturbation_bound (a b s x z : Space) {M δ : ℝ}
    (hM : 0 < M) (hsM : ∀ j, |s j| ≤ M) (hxz : ∀ j, |x j - z j| < δ) :
    ∀ j, |diagonalAffine a b s x j - diagonalAffine a b s z j| < M * δ := by
  intro j
  have he : diagonalAffine a b s x j - diagonalAffine a b s z j = s j * (x j - z j) := by
    dsimp [diagonalAffine]
    ring
  rw [he, abs_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hsM j) (abs_nonneg _))
    (mul_lt_mul_of_pos_left (hxz j) hM)

theorem diagonalAffine_openBox_padded {a b s h x : Space} {δ η : ℝ}
    (hs : ∀ j, 0 < s j) (hscale : ∀ j, s j * δ ≤ η)
    (hx : x ∈ openBox a (fun j => h j + δ)) :
    diagonalAffine a b s x ∈ openBox b (fun j => s j * h j + η) := by
  intro j
  simp only [diagonalAffine, add_sub_cancel_left, abs_mul, abs_of_pos (hs j)]
  have hj := mul_lt_mul_of_pos_left (hx j) (hs j)
  rw [mul_add] at hj
  linarith [hscale j]

end

end BoxTransport

end OAI
