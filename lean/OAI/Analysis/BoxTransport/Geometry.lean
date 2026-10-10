import Mathlib
import OAI.Analysis.BoxTransport.Definitions

namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
@[simp] theorem mixedDerivative_zero (ds : List Axis) :
    mixedDerivative ds (fun _ => (0 : Space)) = fun _ => 0 := by
  induction ds with
  | nil => rfl
  | cons j js ih => simp [mixedDerivative, ih]

theorem effective_zero : Effective (fun _ => (0 : Space)) := by
  refine ⟨fun _ => (0, 0, 0), fun _ => 0, fun _ => 0,
    Computable.const (0, 0, 0), Computable.const 0, Computable.const 0, ?_, ?_⟩
  · intro ds q n p hp j
    simp only [mixedDerivative_zero, Pi.zero_apply, rationalValue, Nat.cast_zero,
      sub_self, zero_div, Rat.cast_zero, abs_zero]
    positivity
  · intro ds p j
    simp

theorem admissible_zero : AdmissibleField (fun _ => (0 : Space)) := by
  refine ⟨contDiff_const, ?_, effective_zero, ?_, ?_⟩
  · exact HasCompactSupport.zero
  · intro t x
    simp [spatialDivergence]
  · intro t x ht
    rfl

theorem globalFlow_zero : IsGlobalFlow (fun _ => (0 : Space)) (fun _ x => x) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro t x
    exact hasDerivAt_const t x
  · intro x γ hγ hder t
    have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
      (fun s => (hder s).deriv) t 0
    exact hc.trans hγ

theorem identity_routing {n : ℕ} (a h : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a a h h Φ := by
  refine ⟨fun _ => 0, fun _ x => x, admissible_zero, globalFlow_zero, ?_⟩
  intro i
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
  intro x hx
  ext j
  simp [prescribedAffine, ne_of_gt (hh i j)]

theorem empty_routing (a b h k : Fin 0 → RationalSpace) :
    ∃ U : Field, ∃ Φ : ℝ → Space → Space,
      AdmissibleField U ∧ IsGlobalFlow U Φ ∧ Delivers a b h k Φ := by
  refine ⟨fun _ => 0, fun _ x => x, admissible_zero, globalFlow_zero, ?_⟩
  exact fun i => Fin.elim0 i

theorem center_mem_realBox {c h : Space} (hh : ∀ j, 0 ≤ h j) : c ∈ realBox c h := by
  intro j
  simpa using hh j

theorem realBox_disjoint_of_gap {c d h k : Space}
    (hgap : ∃ j, h j + k j < |c j - d j|) :
    Disjoint (realBox c h) (realBox d k) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, hj⟩ := hgap
  have hle : |c j - d j| ≤ h j + k j := calc
    |c j - d j| = |(c j - x j) + (x j - d j)| := by congr 1; ring
    _ ≤ |c j - x j| + |x j - d j| := abs_add_le _ _
    _ = |x j - c j| + |x j - d j| := by rw [abs_sub_comm (c j) (x j)]
    _ ≤ h j + k j := add_le_add (hx j) (hy j)
  exact (not_lt_of_ge hle) hj

theorem realBox_disjoint_iff {c d h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (realBox c h) (realBox d k) ↔
      ∃ j, h j + k j < |c j - d j| := by
  refine ⟨?_, realBox_disjoint_of_gap⟩
  intro hdis
  by_contra hn
  push Not at hn
  let x : Space := fun j => max (c j - h j) (d j - k j)
  have hx : x ∈ realBox c h := by
    intro j
    have hj := (abs_le.mp (hn j)).1
    have hwidth := hh j
    apply abs_le.mpr
    constructor
    · dsimp [x]
      have := le_max_left (c j - h j) (d j - k j)
      linarith
    · have hup : x j ≤ c j + h j := by
        apply max_le <;> linarith
      linarith
  have hy : x ∈ realBox d k := by
    intro j
    have hj := (abs_le.mp (hn j)).2
    have hwidth := hk j
    apply abs_le.mpr
    constructor
    · dsimp [x]
      have := le_max_right (c j - h j) (d j - k j)
      linarith
    · have hup : x j ≤ d j + k j := by
        apply max_le <;> linarith
      linarith
  exact (Set.disjoint_left.mp hdis) hx hy

theorem solidBox_disjoint_iff {a b h k : RationalSpace}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (solidBox a h) (solidBox b k) ↔
      ∃ j, h j + k j < |a j - b j| := by
  have hh' : ∀ j, 0 ≤ realPoint h j := by
    intro j
    change (0 : ℝ) ≤ (h j : ℝ)
    exact_mod_cast hh j
  have hk' : ∀ j, 0 ≤ realPoint k j := by
    intro j
    change (0 : ℝ) ≤ (k j : ℝ)
    exact_mod_cast hk j
  rw [solidBox, solidBox, realBox_disjoint_iff hh' hk']
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (h j : ℝ) + (k j : ℝ) < |(a j : ℝ) - (b j : ℝ)| at hj
    exact_mod_cast hj
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change (h j : ℝ) + (k j : ℝ) < |(a j : ℝ) - (b j : ℝ)|
    exact_mod_cast hj

theorem centers_ne_of_disjoint {c d h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j)
    (hdis : Disjoint (realBox c h) (realBox d k)) : c ≠ d := by
  intro hcd
  subst d
  exact Set.disjoint_left.mp hdis (center_mem_realBox hh) (center_mem_realBox hk)

theorem expansion_preserves_disjoint {c d h k : Space} {Λ : ℝ}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j)
    (hdis : Disjoint (realBox c h) (realBox d k)) (hΛ : 1 ≤ Λ) :
    Disjoint (realBox (fun j => Λ * c j) h) (realBox (fun j => Λ * d j) k) := by
  obtain ⟨j, hj⟩ := (realBox_disjoint_iff hh hk).mp hdis
  apply realBox_disjoint_of_gap
  refine ⟨j, hj.trans_le ?_⟩
  calc
    |c j - d j| ≤ Λ * |c j - d j| := le_mul_of_one_le_left (abs_nonneg _) hΛ
    _ = |Λ * c j - Λ * d j| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Λ)]

theorem padded_boxes_disjoint_of_clearance {c d h k : Space} {R η : ℝ}
    (hR : 0 < R) (hη : η < R / 8)
    (hh : ∀ j, h j ≤ R) (hk : ∀ j, k j ≤ R)
    (hclear : ∃ j, 4 * R ≤ |c j - d j|) :
    Disjoint (realBox c (fun j => h j + 2 * η))
      (realBox d (fun j => k j + 2 * η)) := by
  obtain ⟨j, hj⟩ := hclear
  apply realBox_disjoint_of_gap
  refine ⟨j, ?_⟩
  have := hh j
  have := hk j
  linarith

def coordinateGap (a b h k : RationalSpace) : ℚ :=
  (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty
    (fun j => |a j - b j| - h j - k j)

theorem coordinateGap_pos_iff (a b h k : RationalSpace) :
    0 < coordinateGap a b h k ↔ ∃ j, h j + k j < |a j - b j| := by
  simp only [coordinateGap, Finset.lt_sup'_iff, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨j, hj⟩ <;> exact ⟨j, by linarith⟩

theorem positive_finset_lower_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ) :
    (∀ i ∈ s, 0 < f i) → ∃ g : ℚ, 0 < g ∧ ∀ i ∈ s, g ≤ f i := by
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨g, hg, hgf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      refine ⟨min g (f i), lt_min hg (hf i (Finset.mem_insert_self _ _)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hgf j hj)

theorem uniform_rational_gap {n : ℕ} (a h : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j)
    (hdis : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j))) :
    ∃ g : ℚ, 0 < g ∧ ∀ i j, i ≠ j →
      ∃ l, h i l + h j l + g ≤ |a i l - a j l| := by
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)
  have hpos : ∀ p ∈ pairs, 0 < coordinateGap (a p.1) (a p.2) (h p.1) (h p.2) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    apply (coordinateGap_pos_iff _ _ _ _).mpr
    exact (solidBox_disjoint_iff (hh _) (hh _)).mp (hdis hne)
  obtain ⟨g, hg, hbound⟩ := positive_finset_lower_bound pairs
    (fun p => coordinateGap (a p.1) (a p.2) (h p.1) (h p.2)) hpos
  refine ⟨g, hg, ?_⟩
  intro i j hij
  have hb := hbound (i, j) (by simp [pairs, hij])
  obtain ⟨l, hlmem, hl⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp hb
  exact ⟨l, by dsimp at hl; linarith⟩

theorem exists_expansion_factor {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j) (hk : ∀ i j, 0 ≤ k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (R : ℚ) (hR : 0 < R) :
    ∃ Λ : ℚ, 10 < Λ ∧
      (∀ i j, i ≠ j → ∃ l, 20 * R < |Λ * a i l - Λ * a j l|) ∧
      (∀ i j, i ≠ j → ∃ l, 20 * R < |Λ * b i l - Λ * b j l|) := by
  obtain ⟨ga, hga, haga⟩ := uniform_rational_gap a h hh ha
  obtain ⟨gb, hgb, hbgb⟩ := uniform_rational_gap b k hk hb
  let g := min ga gb
  have hg : 0 < g := lt_min hga hgb
  let Λ : ℚ := 11 + 20 * R / g
  have hΛ : 10 < Λ := by
    have : 0 < 20 * R / g := by positivity
    dsimp [Λ]
    linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hΛg : 20 * R < Λ * g := by
    dsimp [Λ]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hg)]
    nlinarith
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · intro i j hij
    obtain ⟨l, hl⟩ := haga i j hij
    have hgabs : g ≤ |a i l - a j l| := by
      have := hh i l
      have := hh j l
      have : g ≤ ga := min_le_left _ _
      linarith
    refine ⟨l, hΛg.trans_le ?_⟩
    calc
      Λ * g ≤ Λ * |a i l - a j l| := mul_le_mul_of_nonneg_left hgabs hΛ0
      _ = |Λ * a i l - Λ * a j l| := by rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]
  · intro i j hij
    obtain ⟨l, hl⟩ := hbgb i j hij
    have hgabs : g ≤ |b i l - b j l| := by
      have := hk i l
      have := hk j l
      have : g ≤ gb := min_le_right _ _
      linarith
    refine ⟨l, hΛg.trans_le ?_⟩
    calc
      Λ * g ≤ Λ * |b i l - b j l| := mul_le_mul_of_nonneg_left hgabs hΛ0
      _ = |Λ * b i l - Λ * b j l| := by rw [← mul_sub, abs_mul, abs_of_nonneg hΛ0]

theorem exists_rational_padding {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 ≤ h i j) (hk : ∀ i j, 0 ≤ k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (R : ℚ) (hR : 0 < R) :
    ∃ η : ℚ, 0 < η ∧ η < R / 8 ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
          (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η))) ∧
      (Pairwise fun i j =>
        Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
          (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) := by
  obtain ⟨ga, hga, haga⟩ := uniform_rational_gap a h hh ha
  obtain ⟨gb, hgb, hbgb⟩ := uniform_rational_gap b k hk hb
  let m := min R (min ga gb)
  have hm : 0 < m := lt_min hR (lt_min hga hgb)
  let η := m / 16
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hmR : m ≤ R := min_le_left _ _
  have hmga : m ≤ ga := (min_le_right _ _).trans (min_le_left _ _)
  have hmgb : m ≤ gb := (min_le_right _ _).trans (min_le_right _ _)
  have hηR : η < R / 8 := by dsimp [η]; linarith
  have hηa : 4 * η < ga := by dsimp [η]; linarith
  have hηb : 4 * η < gb := by dsimp [η]; linarith
  refine ⟨η, hη0, hηR, ?_, ?_⟩
  · intro i j hij
    obtain ⟨l, hl⟩ := haga i j hij
    apply realBox_disjoint_of_gap
    refine ⟨l, ?_⟩
    have hlt : (h i l + 2 * η) + (h j l + 2 * η) < |a i l - a j l| := by linarith
    change ((h i l : ℝ) + 2 * (η : ℝ)) + ((h j l : ℝ) + 2 * (η : ℝ)) <
      |(a i l : ℝ) - (a j l : ℝ)|
    exact_mod_cast hlt
  · intro i j hij
    obtain ⟨l, hl⟩ := hbgb i j hij
    apply realBox_disjoint_of_gap
    refine ⟨l, ?_⟩
    have hlt : (k i l + 2 * η) + (k j l + 2 * η) < |b i l - b j l| := by linarith
    change ((k i l : ℝ) + 2 * (η : ℝ)) + ((k j l : ℝ) + 2 * (η : ℝ)) <
      |(b i l : ℝ) - (b j l : ℝ)|
    exact_mod_cast hlt

def parkingCenter (K R : ℚ) (i : ℕ) : RationalSpace :=
  ![K + 30 * R * ((i : ℚ) + 1), 0, 0]

theorem parking_separated {K R : ℚ} (hR : 0 < R) {i j : ℕ} (hij : i ≠ j) :
    30 * R ≤ |parkingCenter K R i 0 - parkingCenter K R j 0| := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle : (i : ℚ) + 1 ≤ (j : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have habs := neg_le_abs (parkingCenter K R i 0 - parkingCenter K R j 0)
    simp only [parkingCenter, Matrix.cons_val_zero] at *
    nlinarith
  · have hle : (j : ℚ) + 1 ≤ (i : ℚ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have habs := le_abs_self (parkingCenter K R i 0 - parkingCenter K R j 0)
    simp only [parkingCenter, Matrix.cons_val_zero] at *
    nlinarith

theorem parking_clearance {K R : ℚ} (hR : 0 < R)
    (q : RationalSpace) (hq : |q 0| ≤ K) (i : ℕ) :
    30 * R ≤ |parkingCenter K R i 0 - q 0| := by
  have hq' : q 0 ≤ K := (le_abs_self _).trans hq
  have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
  calc
    30 * R ≤ parkingCenter K R i 0 - q 0 := by dsimp [parkingCenter]; nlinarith
    _ ≤ |parkingCenter K R i 0 - q 0| := le_abs_self _

theorem exists_parking_offset {n : ℕ} (a b : Fin n → RationalSpace) (Λ : ℚ) :
    ∃ K : ℚ, 4 * Λ ≤ K ∧ (∀ i, |Λ * a i 0| ≤ K) ∧ (∀ i, |Λ * b i 0| ≤ K) := by
  let f : Option (Bool × Fin n) → ℚ
    | none => 4 * Λ
    | some (false, i) => |Λ * a i 0|
    | some (true, i) => |Λ * b i 0|
  let K := (Finset.univ : Finset (Option (Bool × Fin n))).sup' Finset.univ_nonempty f
  have hf (p : Option (Bool × Fin n)) : f p ≤ K :=
    Finset.le_sup' f (Finset.mem_univ p)
  exact ⟨K, hf none, fun i => hf (some (false, i)), fun i => hf (some (true, i))⟩

theorem smooth_power_scale {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun θ : ℝ => s ^ θ) := by
  simp only [Real.rpow_def_of_pos hs]
  fun_prop

theorem power_scale_between {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    min 1 s ≤ s ^ θ ∧ s ^ θ ≤ max 1 s := by
  rcases le_total 1 s with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    constructor
    · simpa using Real.rpow_le_rpow_of_exponent_le hle hθ.1
    · simpa using Real.rpow_le_rpow_of_exponent_le hle hθ.2
  · rw [min_eq_right hle, max_eq_left hle]
    constructor
    · simpa using Real.rpow_le_rpow_of_exponent_ge hs hle hθ.2
    · exact Real.rpow_le_one hs.le hle hθ.1

theorem determinant_power_scale (s : Space) (hs : ∀ j, 0 < s j)
    (hdet : ∏ j : Fin 3, s j = 1) (θ : ℝ) :
    Matrix.det (Matrix.diagonal (fun j => s j ^ θ)) = 1 := by
  rw [Matrix.det_diagonal, Real.finsetProd_rpow _ _ (fun j _ => (hs j).le), hdet,
    Real.one_rpow]

theorem geometric_halfwidth_le {h k R θ : ℝ}
    (hh : 0 < h) (hk : 0 < k) (hhR : h ≤ R) (hkR : k ≤ R)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    h * (k / h) ^ θ ≤ R := by
  rcases le_total k h with hkh | hhk
  · have hs : k / h ≤ 1 := (div_le_one hh).mpr hkh
    have hp : (k / h) ^ θ ≤ 1 := Real.rpow_le_one (div_pos hk hh).le hs hθ.1
    calc
      h * (k / h) ^ θ ≤ h * 1 := mul_le_mul_of_nonneg_left hp hh.le
      _ ≤ R := by simpa using hhR
  · have hs : 1 ≤ k / h := (le_div_iff₀ hh).mpr (by simpa using hhk)
    have hp : (k / h) ^ θ ≤ k / h := by
      simpa using Real.rpow_le_rpow_of_exponent_le hs hθ.2
    calc
      h * (k / h) ^ θ ≤ h * (k / h) := mul_le_mul_of_nonneg_left hp hh.le
      _ = k := by field_simp
      _ ≤ R := hkR

theorem reshaping_properties (h k : Space)
    (hh : ∀ j, 0 < h j) (hk : ∀ j, 0 < k j)
    (hvol : ∏ j : Fin 3, k j / h j = 1)
    {R θ : ℝ} (hhR : ∀ j, h j ≤ R) (hkR : ∀ j, k j ≤ R)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ j, 0 < (k j / h j) ^ θ) ∧
    (∀ j, h j * (k j / h j) ^ θ ≤ R) ∧
    Matrix.det (Matrix.diagonal (fun j => (k j / h j) ^ θ)) = 1 := by
  refine ⟨fun j => Real.rpow_pos_of_pos (div_pos (hk j) (hh j)) _, ?_, ?_⟩
  · intro j
    exact geometric_halfwidth_le (hh j) (hk j) (hhR j) (hkR j) hθ
  · exact determinant_power_scale _ (fun j => div_pos (hk j) (hh j)) hvol θ

theorem diagonal_affine_image (c d h s : Space) (hs : ∀ j, 0 < s j) :
    (fun x : Space => fun j => d j + s j * (x j - c j)) '' realBox c h =
      realBox d (fun j => s j * h j) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro j
    dsimp
    rw [add_sub_cancel_left, abs_mul, abs_of_pos (hs j)]
    exact mul_le_mul_of_nonneg_left (hx j) (hs j).le
  · intro hy
    let x : Space := fun j => c j + (y j - d j) / s j
    refine ⟨x, ?_, ?_⟩
    · intro j
      dsimp [x]
      rw [add_sub_cancel_left, abs_div, abs_of_pos (hs j)]
      apply (div_le_iff₀ (hs j)).mpr
      simpa [mul_comm] using hy j
    · ext j
      dsimp [x]
      rw [add_sub_cancel_left]
      have hsj : s j ≠ 0 := ne_of_gt (hs j)
      field_simp
      ring

theorem prescribedAffine_image (a b h k : RationalSpace)
    (hh : ∀ j, 0 < h j) (hk : ∀ j, 0 < k j) :
    prescribedAffine a b h k '' solidBox a h = solidBox b k := by
  let s : Space := fun j => ((k j / h j : ℚ) : ℝ)
  have hs : ∀ j, 0 < s j := by
    intro j
    change (0 : ℝ) < ((k j / h j : ℚ) : ℝ)
    exact_mod_cast div_pos (hk j) (hh j)
  have hw : (fun j => s j * realPoint h j) = realPoint k := by
    ext j
    change ((k j / h j : ℚ) : ℝ) * (h j : ℝ) = (k j : ℝ)
    exact_mod_cast div_mul_cancel₀ (k j) (ne_of_gt (hh j))
  have himage := diagonal_affine_image (realPoint a) (realPoint b) (realPoint h) s hs
  rw [hw] at himage
  exact himage

def openBox (c h : Space) (ε : ℝ) : Set Space :=
  {x | ∀ j, |x j - c j| < h j + ε}

theorem isOpen_openBox (c h : Space) (ε : ℝ) : IsOpen (openBox c h ε) := by
  simp only [openBox, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt
  · fun_prop
  · fun_prop

theorem realBox_subset_openBox (c h : Space) {ε : ℝ} (hε : 0 < ε) :
    realBox c h ⊆ openBox c h ε := by
  intro x hx j
  exact (hx j).trans_lt (lt_add_of_pos_right _ hε)

theorem affine_openBox_control (c d h s : Space) {ε M : ℝ}
    (hε : 0 ≤ ε) (hs : ∀ j, 0 < s j) (hsM : ∀ j, s j ≤ M)
    {x : Space} (hx : x ∈ openBox c h ε) :
    (fun j => d j + s j * (x j - c j)) ∈
      openBox d (fun j => s j * h j) (M * ε) := by
  intro j
  dsimp
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (hs j)]
  calc
    s j * |x j - c j| < s j * (h j + ε) := mul_lt_mul_of_pos_left (hx j) (hs j)
    _ ≤ s j * h j + M * ε := by
      have := mul_le_mul_of_nonneg_right (hsM j) hε
      nlinarith

end BoxTransport.Routing

end

end OAI
