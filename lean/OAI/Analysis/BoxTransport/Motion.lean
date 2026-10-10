import Mathlib
import OAI.Analysis.BoxTransport.Flow

namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
def centerKey {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : ℚ ×ₗ ℕ := toLex (f i, i.val)

def coordinateRank {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => centerKey f j < centerKey f i).card

theorem centerKey_injective {n : ℕ} (f : Fin n → ℚ) : Function.Injective (centerKey f) := by
  intro i j hij
  have hp := toLex.injective hij
  exact Fin.ext (congrArg Prod.snd hp)

theorem coordinateRank_strict {n : ℕ} {f : Fin n → ℚ} {i j : Fin n}
    (hij : centerKey f i < centerKey f j) : coordinateRank f i < coordinateRank f j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans hij
  · intro he
    have hi : i ∈ Finset.univ.filter (fun k => centerKey f k < centerKey f j) := by
      simp [hij]
    rw [← he] at hi
    simp at hi

theorem coordinateRank_lt {n : ℕ} (f : Fin n → ℚ) (i : Fin n) : coordinateRank f i < n := by
  have hs : (Finset.univ.filter fun j => centerKey f j < centerKey f i) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hi : i ∈ Finset.univ.filter (fun j => centerKey f j < centerKey f i) :=
      he.symm ▸ Finset.mem_univ i
    simp at hi
  simpa only [coordinateRank, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hs

theorem centerKey_coordinate_le {n : ℕ} {f : Fin n → ℚ} {i j : Fin n}
    (hij : centerKey f i < centerKey f j) : f i ≤ f j :=
  Prod.Lex.monotone_fst _ _ hij.le

def spreadCenter {n : ℕ} (a : Fin n → RationalSpace) (D θ : ℝ) (i : Fin n) : Space :=
  fun j => if j = 0 then (a i 0 : ℝ) + θ * D * coordinateRank (fun q => a q 0) i
    else (a i j : ℝ)

@[simp] theorem spreadCenter_zero {n : ℕ} (a : Fin n → RationalSpace) (D : ℝ) (i : Fin n) :
    spreadCenter a D 0 i = realPoint (a i) := by
  ext j
  by_cases hj : j = 0 <;> simp [spreadCenter, hj, realPoint]

theorem spreadCenter_gap {n : ℕ} (a : Fin n → RationalSpace) {D θ : ℝ}
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (i j : Fin n) (k : Fin 3) :
    |(a i k : ℝ) - (a j k : ℝ)| ≤ |spreadCenter a D θ i k - spreadCenter a D θ j k| := by
  by_cases hk : k = 0
  · subst k
    wlog hij : centerKey (fun q => a q 0) i ≤ centerKey (fun q => a q 0) j generalizing i j
    · simpa only [abs_sub_comm] using this j i (le_of_not_ge hij)
    rcases hij.eq_or_lt with he | hij
    · have heij := centerKey_injective (fun q => a q 0) he
      subst j
      simp
    have hr : coordinateRank (fun q => a q 0) i ≤ coordinateRank (fun q => a q 0) j :=
      (coordinateRank_strict hij).le
    have hc : (a i 0 : ℝ) ≤ (a j 0 : ℝ) := by exact_mod_cast centerKey_coordinate_le hij
    have hr' : (coordinateRank (fun q => a q 0) i : ℝ) ≤
        (coordinateRank (fun q => a q 0) j : ℝ) := by exact_mod_cast hr
    have hm := mul_le_mul_of_nonneg_left hr' (mul_nonneg hθ hD)
    simp only [spreadCenter, ite_true]
    rw [abs_of_nonpos (sub_nonpos.mpr hc), abs_of_nonpos (by linarith)]
    linarith
  · simp only [spreadCenter, ite_eq_right hk]
    exact le_rfl

theorem spreadCenter_separated {n : ℕ} (a : Fin n → RationalSpace) {D : ℝ}
    (hD : 0 ≤ D) {i j : Fin n} (hij : i ≠ j) :
    D ≤ |spreadCenter a D 1 i 0 - spreadCenter a D 1 j 0| := by
  wlog hkey : centerKey (fun q => a q 0) i < centerKey (fun q => a q 0) j generalizing i j
  · have hne : centerKey (fun q => a q 0) i ≠ centerKey (fun q => a q 0) j :=
      (centerKey_injective (fun q => a q 0)).ne hij
    simpa only [abs_sub_comm] using this hij.symm (lt_of_le_of_ne (le_of_not_gt hkey) hne.symm)
  have hr : coordinateRank (fun q => a q 0) i + 1 ≤ coordinateRank (fun q => a q 0) j :=
    coordinateRank_strict hkey
  have hr' : (coordinateRank (fun q => a q 0) i : ℝ) + 1 ≤
      (coordinateRank (fun q => a q 0) j : ℝ) := by exact_mod_cast hr
  have hc : (a i 0 : ℝ) ≤ (a j 0 : ℝ) := by exact_mod_cast centerKey_coordinate_le hkey
  simp only [spreadCenter, ite_true, one_mul]
  have ha := neg_le_abs ((a i 0 : ℝ) + D * coordinateRank (fun q => a q 0) i -
    ((a j 0 : ℝ) + D * coordinateRank (fun q => a q 0) j))
  nlinarith

theorem spreadCenter_disjoint {n : ℕ} (a : Fin n → RationalSpace) (r : Fin n → Space)
    {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hr : ∀ i k, 0 ≤ r i k)
    (hsep : Pairwise fun i j => Disjoint (realBox (realPoint (a i)) (r i))
      (realBox (realPoint (a j)) (r j))) :
    Pairwise fun i j => Disjoint (realBox (spreadCenter a D θ i) (r i))
      (realBox (spreadCenter a D θ j) (r j)) := by
  intro i j hij
  obtain ⟨k, hk⟩ := (realBox_disjoint_iff (hr i) (hr j)).mp (hsep hij)
  apply realBox_disjoint_of_gap
  exact ⟨k, hk.trans_le (spreadCenter_gap a hD hθ i j k)⟩

noncomputable def stageSwitch (j : Fin 5) (t : ℝ) : ℝ :=
  Real.smoothTransition (10 * t - 5 / 2 - (j : ℝ))

theorem contDiff_stageSwitch (j : Fin 5) : ContDiff ℝ ∞ (stageSwitch j) := by
  apply Real.smoothTransition.contDiff.comp
  fun_prop

theorem stageSwitch_mem (j : Fin 5) (t : ℝ) : stageSwitch j t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem stageSwitch_zero {j : Fin 5} {t : ℝ} (h : 10 * t - 5 / 2 ≤ (j : ℝ)) :
    stageSwitch j t = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h)

theorem stageSwitch_one {j : Fin 5} {t : ℝ} (h : (j : ℝ) + 1 ≤ 10 * t - 5 / 2) :
    stageSwitch j t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem stageSwitch_before (j : Fin 5) {t : ℝ} (h : t ≤ 1 / 4) : stageSwitch j t = 0 := by
  apply stageSwitch_zero
  have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith

theorem stageSwitch_after (j : Fin 5) {t : ℝ} (h : 3 / 4 ≤ t) : stageSwitch j t = 1 := by
  apply stageSwitch_one
  have hj : (j : ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  linarith

theorem stageSwitch_cases (t : ℝ) :
    (stageSwitch 1 t = 0 ∧ stageSwitch 2 t = 0 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 2 t = 0 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 3 t = 0 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 2 t = 1 ∧ stageSwitch 4 t = 0) ∨
    (stageSwitch 0 t = 1 ∧ stageSwitch 1 t = 1 ∧ stageSwitch 2 t = 1 ∧ stageSwitch 3 t = 1) := by
  by_cases h₁ : 10 * t - 5 / 2 ≤ 1
  · exact Or.inl ⟨stageSwitch_zero (by simpa using h₁), stageSwitch_zero (by norm_num; linarith),
      stageSwitch_zero (by norm_num; linarith), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₂ : 10 * t - 5 / 2 ≤ 2
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_zero (by simpa using h₂),
      stageSwitch_zero (by norm_num; linarith), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₃ : 10 * t - 5 / 2 ≤ 3
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
      stageSwitch_zero (by simpa using h₃), stageSwitch_zero (by norm_num; linarith)⟩
  right
  by_cases h₄ : 10 * t - 5 / 2 ≤ 4
  · exact Or.inl ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
      stageSwitch_one (by norm_num; linarith), stageSwitch_zero (by simpa using h₄)⟩
  right
  exact ⟨stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith),
    stageSwitch_one (by norm_num; linarith), stageSwitch_one (by norm_num; linarith)⟩

def routeCenterParameters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (u : Fin 5 → ℝ) (i : Fin n) : Space :=
  ![(a i 0 : ℝ) + u 0 * D * coordinateRank (fun q => a q 0) i +
      u 2 * ((b i 0 : ℝ) + D * coordinateRank (fun q => b q 0) i -
        (a i 0 : ℝ) - D * coordinateRank (fun q => a q 0) i) -
      u 4 * D * coordinateRank (fun q => b q 0) i,
    (a i 1 : ℝ) + u 2 * ((b i 1 : ℝ) - (a i 1 : ℝ)),
    (a i 2 : ℝ) + u 1 * (D * (i : ℝ) - (a i 2 : ℝ)) +
      u 3 * ((b i 2 : ℝ) - D * (i : ℝ))]

noncomputable def routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) (t : ℝ) : Space := routeCenterParameters a b D (fun j => stageSwitch j t) i

theorem contDiff_routeCenters {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ) (i : Fin n) :
    ContDiff ℝ ∞ (routeCenters a b D i) := by
  have hs := contDiff_stageSwitch
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [routeCenters, routeCenterParameters] <;> fun_prop

theorem routeCenter_stage₀ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₁ : u 1 = 0) (h₂ : u 2 = 0) (h₃ : u 3 = 0) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i = spreadCenter a D (u 0) i := by
  ext j
  fin_cases j <;> simp [routeCenterParameters, spreadCenter, h₁, h₂, h₃, h₄]

theorem routeCenter_stage₁ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (h₂ : u 2 = 0) (_h₃ : u 3 = 0) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 0 = spreadCenter a D 1 i 0 := by
  simp [routeCenterParameters, spreadCenter, h₀, h₂, h₄]

theorem routeCenter_stage₂ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (_h₀ : u 0 = 1) (h₁ : u 1 = 1) (h₃ : u 3 = 0) (_h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 2 = D * (i : ℝ) := by
  simp [routeCenterParameters, h₁, h₃]

theorem routeCenter_stage₃ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (_h₁ : u 1 = 1) (h₂ : u 2 = 1) (h₄ : u 4 = 0)
    (i : Fin n) : routeCenterParameters a b D u i 0 = spreadCenter b D 1 i 0 := by
  simp [routeCenterParameters, spreadCenter, h₀, h₂, h₄]

theorem routeCenter_stage₄ {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    {u : Fin 5 → ℝ} (h₀ : u 0 = 1) (h₁ : u 1 = 1) (h₂ : u 2 = 1) (h₃ : u 3 = 1)
    (i : Fin n) : routeCenterParameters a b D u i = spreadCenter b D (1 - u 4) i := by
  ext j
  fin_cases j <;> simp [routeCenterParameters, spreadCenter, h₀, h₁, h₂, h₃]
  ring

theorem routeCenters_before {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) {t : ℝ} (ht : t ≤ 1 / 4) : routeCenters a b D i t = realPoint (a i) := by
  rw [routeCenters, routeCenter_stage₀ a b D
    (stageSwitch_before 1 ht) (stageSwitch_before 2 ht) (stageSwitch_before 3 ht)
    (stageSwitch_before 4 ht), stageSwitch_before 0 ht, spreadCenter_zero]

theorem routeCenters_after {n : ℕ} (a b : Fin n → RationalSpace) (D : ℝ)
    (i : Fin n) {t : ℝ} (ht : 3 / 4 ≤ t) : routeCenters a b D i t = realPoint (b i) := by
  rw [routeCenters, routeCenter_stage₄ a b D
    (stageSwitch_after 0 ht) (stageSwitch_after 1 ht) (stageSwitch_after 2 ht)
    (stageSwitch_after 3 ht), stageSwitch_after 4 ht, sub_self, spreadCenter_zero]

theorem private_layers_separated {n : ℕ} {D : ℝ} (hD : 0 ≤ D) {i j : Fin n} (hij : i ≠ j) :
    D ≤ |D * (i : ℝ) - D * (j : ℝ)| := by
  wlog hlt : i < j generalizing i j
  · simpa only [abs_sub_comm] using this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
  have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
  have ha := neg_le_abs (D * (i : ℝ) - D * (j : ℝ))
  nlinarith

def scaleRatio {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (j : Fin 3) : ℝ :=
  ((k i j / h i j : ℚ) : ℝ)

noncomputable def balancedScale (s : Space) (u : ℝ) : Space :=
  ![1 - u + u * s 0, 1 - u + u * s 1,
    ((1 - u + u * s 0) * (1 - u + u * s 1))⁻¹]

@[simp] theorem balancedScale_zero (s : Space) : balancedScale s 0 = 1 := by
  ext j; fin_cases j <;> simp [balancedScale]

theorem balancedScale_one (s : Space) (hdet : ∏ j : Fin 3, s j = 1) :
    balancedScale s 1 = s := by
  have hd : s 0 * s 1 * s 2 = 1 := by simpa [Fin.prod_univ_three] using hdet
  ext j
  fin_cases j
  · simp [balancedScale]
  · simp [balancedScale]
  · simpa [balancedScale] using inv_eq_of_mul_eq_one_right hd

theorem linearBlend_between {s u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    min 1 s ≤ 1 - u + u * s ∧ 1 - u + u * s ≤ max 1 s := by
  by_cases h : 1 ≤ s
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h)]
  · have h' := le_of_not_ge h
    rw [min_eq_right h', max_eq_left h']
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr h')]
    · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr h')]

theorem linearBlend_pos {s u : ℝ} (hs : 0 < s) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - u + u * s :=
  lt_of_lt_of_le (lt_min zero_lt_one hs) (linearBlend_between hu).1

theorem linearBlend_product_lower {s t u : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    min 1 (s * t) ≤ (1 - u + u * s) * (1 - u + u * t) := by
  have hb (s : ℝ) := linearBlend_between (s := s) hu
  have hbs : 0 ≤ 1 - u + u * s := (linearBlend_pos hs hu).le
  have hbt : 0 ≤ 1 - u + u * t := (linearBlend_pos ht hu).le
  by_cases hs' : 1 ≤ s <;> by_cases ht' : 1 ≤ t
  · have h₁ : 1 ≤ 1 - u + u * s := by simpa [min_eq_left hs'] using (hb s).1
    have h₂ : 1 ≤ 1 - u + u * t := by simpa [min_eq_left ht'] using (hb t).1
    exact (min_le_left _ _).trans (by nlinarith)
  · have hc : 0 ≤ u * (1 - u) * (s - 1) * (1 - t) :=
      mul_nonneg (mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))
        (sub_nonneg.mpr hs')) (sub_nonneg.mpr (le_of_not_ge ht'))
    have hl := (linearBlend_between (s := s * t) hu).1
    nlinarith
  · have hc : 0 ≤ u * (1 - u) * (1 - s) * (t - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))
        (sub_nonneg.mpr (le_of_not_ge hs'))) (sub_nonneg.mpr ht')
    have hl := (linearBlend_between (s := s * t) hu).1
    nlinarith
  · have h₁ : s ≤ 1 - u + u * s := by simpa [min_eq_right (le_of_not_ge hs')] using (hb s).1
    have h₂ : t ≤ 1 - u + u * t := by simpa [min_eq_right (le_of_not_ge ht')] using (hb t).1
    exact (min_le_right _ _).trans (mul_le_mul h₁ h₂ ht.le hbs)

theorem balancedScale_pos (s : Space) (hs : ∀ j, 0 < s j)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (j : Fin 3) :
    0 < balancedScale s u j := by
  fin_cases j
  · exact linearBlend_pos (hs 0) hu
  · exact linearBlend_pos (hs 1) hu
  · exact inv_pos.mpr (mul_pos (linearBlend_pos (hs 0) hu) (linearBlend_pos (hs 1) hu))

theorem balancedScale_det (s : Space) (hs : ∀ j, 0 < s j)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : ∏ j : Fin 3, balancedScale s u j = 1 := by
  simp only [Fin.prod_univ_three, balancedScale, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  exact mul_inv_cancel₀ (mul_ne_zero (ne_of_gt (linearBlend_pos (hs 0) hu))
    (ne_of_gt (linearBlend_pos (hs 1) hu)))

theorem balancedScale_le (s : Space) (hs : ∀ j, 0 < s j)
    (hdet : ∏ j : Fin 3, s j = 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (j : Fin 3) :
    balancedScale s u j ≤ max 1 (s j) := by
  fin_cases j
  · exact (linearBlend_between hu).2
  · exact (linearBlend_between hu).2
  have hp := linearBlend_product_lower (hs 0) (hs 1) hu
  have hd : (s 0 * s 1)⁻¹ = s 2 := by
    exact inv_eq_of_mul_eq_one_right (by simpa [Fin.prod_univ_three] using hdet)
  change ((1 - u + u * s 0) * (1 - u + u * s 1))⁻¹ ≤ max 1 (s 2)
  by_cases he : 1 ≤ s 0 * s 1
  · rw [min_eq_left he] at hp
    apply le_trans _ (le_max_left _ _)
    exact inv_le_one_of_one_le₀ hp
  · rw [min_eq_right (le_of_not_ge he)] at hp
    apply le_trans _ (le_max_right _ _)
    rw [← hd]
    exact inv_anti₀ (mul_pos (hs 0) (hs 1)) hp

noncomputable def routeScales {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (t : ℝ) : Space :=
  balancedScale (scaleRatio h k i) (stageSwitch 2 t)

theorem scaleRatio_pos {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (j : Fin 3) :
    0 < scaleRatio h k i j := by
  unfold scaleRatio
  exact_mod_cast div_pos (hk i j) (hh i j)

theorem scaleRatio_mul_width {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (i : Fin n) (j : Fin 3) :
    scaleRatio h k i j * (h i j : ℝ) = (k i j : ℝ) := by
  unfold scaleRatio
  exact_mod_cast div_mul_cancel₀ (k i j) (ne_of_gt (hh i j))

theorem contDiff_routeScales {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) :
    ContDiff ℝ ∞ (routeScales h k i) := by
  have hp (j : Fin 3) (t : ℝ) := linearBlend_pos (scaleRatio_pos hh hk i j) (stageSwitch_mem 2 t)
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ∞ (fun t => 1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 0)
    exact (contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)
  · change ContDiff ℝ ∞ (fun t => 1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 1)
    exact (contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)
  · change ContDiff ℝ ∞ (fun t => ((1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 0) *
        (1 - stageSwitch 2 t + stageSwitch 2 t * scaleRatio h k i 1))⁻¹)
    apply ContDiff.inv
    · exact ((contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const)).mul
        ((contDiff_const.sub (contDiff_stageSwitch 2)).add ((contDiff_stageSwitch 2).mul contDiff_const))
    · intro t; exact ne_of_gt (mul_pos (hp 0 t) (hp 1 t))

theorem routeScales_pos {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j) (i : Fin n) (t : ℝ) (j : Fin 3) :
    0 < routeScales h k i t j :=
  balancedScale_pos _ (scaleRatio_pos hh hk i) (stageSwitch_mem 2 t) j

theorem routeScales_det {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (_hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) (i : Fin n) (t : ℝ) :
    ∏ j : Fin 3, routeScales h k i t j = 1 :=
  balancedScale_det _ (scaleRatio_pos hh hk i) (stageSwitch_mem 2 t)

theorem scaleRatio_det {n : ℕ} {h k : Fin n → RationalSpace}
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) (i : Fin n) :
    ∏ j : Fin 3, scaleRatio h k i j = 1 := by
  unfold scaleRatio
  exact_mod_cast hvol i

theorem routeScales_le {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {M : ℝ} (hM : 1 ≤ M) (hsM : ∀ i j, scaleRatio h k i j ≤ M)
    (i : Fin n) (t : ℝ) (j : Fin 3) : routeScales h k i t j ≤ M :=
  (balancedScale_le _ (scaleRatio_pos hh hk i) (scaleRatio_det hvol i) (stageSwitch_mem 2 t) j).trans
    (max_le hM (hsM i j))

theorem routeScales_before {n : ℕ} (h k : Fin n → RationalSpace)
    (i : Fin n) {t : ℝ} (ht : t ≤ 1 / 4) : routeScales h k i t = 1 := by
  simp [routeScales, stageSwitch_before 2 ht]

theorem routeScales_after {n : ℕ} (h k : Fin n → RationalSpace)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    (i : Fin n) {t : ℝ} (ht : 3 / 4 ≤ t) : routeScales h k i t = scaleRatio h k i := by
  simp only [routeScales, stageSwitch_after 2 ht, balancedScale_one _ (scaleRatio_det hvol i)]

theorem routeScales_width_le {n : ℕ} {h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {R : ℝ} (hhR : ∀ i j, (h i j : ℝ) ≤ R) (hkR : ∀ i j, (k i j : ℝ) ≤ R)
    (i : Fin n) (t : ℝ) (j : Fin 3) : routeScales h k i t j * (h i j : ℝ) ≤ R := by
  have hh' : 0 ≤ (h i j : ℝ) := by exact_mod_cast (hh i j).le
  have hs := balancedScale_le _ (scaleRatio_pos hh hk i) (scaleRatio_det hvol i) (stageSwitch_mem 2 t) j
  apply (mul_le_mul_of_nonneg_right hs hh').trans
  rw [max_mul_of_nonneg _ _ hh', one_mul, scaleRatio_mul_width hh]
  exact max_le (hhR i j) (hkR i j)

def boxDataBound {n : ℕ} (h k : Fin n → RationalSpace) : ℚ :=
  1 + ∑ i : Fin n, ∑ j : Fin 3, (|h i j| + |k i j| + |k i j / h i j| + 1)

theorem boxDataBound_ge_one {n : ℕ} (h k : Fin n → RationalSpace) : 1 ≤ boxDataBound h k := by
  unfold boxDataBound
  have hn : 0 ≤ ∑ i : Fin n, ∑ j : Fin 3, (|h i j| + |k i j| + |k i j / h i j| + 1) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  linarith

theorem boxDataBound_bounds {n : ℕ} (h k : Fin n → RationalSpace) (i : Fin n) (j : Fin 3) :
    h i j ≤ boxDataBound h k ∧ k i j ≤ boxDataBound h k ∧ k i j / h i j ≤ boxDataBound h k := by
  have h₁ : |h i j| + |k i j| + |k i j / h i j| + 1 ≤
      ∑ l : Fin 3, (|h i l| + |k i l| + |k i l / h i l| + 1) :=
    Finset.single_le_sum (f := fun l : Fin 3 => |h i l| + |k i l| + |k i l / h i l| + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have h₂ : (∑ l : Fin 3, (|h i l| + |k i l| + |k i l / h i l| + 1)) ≤
      ∑ s : Fin n, ∑ l : Fin 3, (|h s l| + |k s l| + |k s l / h s l| + 1) :=
    Finset.single_le_sum (f := fun s : Fin n => ∑ l : Fin 3,
      (|h s l| + |k s l| + |k s l / h s l| + 1))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hs := h₁.trans h₂
  have hha := le_abs_self (h i j)
  have hka := le_abs_self (k i j)
  have hsa := le_abs_self (k i j / h i j)
  have hhn := abs_nonneg (h i j)
  have hkn := abs_nonneg (k i j)
  have hsn := abs_nonneg (k i j / h i j)
  unfold boxDataBound
  constructor
  · linarith
  constructor <;> linarith

theorem route_padded_disjoint {n : ℕ} {a b h k : Fin n → RationalSpace}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (hηR : η < R / 8)
    (hhR : ∀ i j, (h i j : ℝ) ≤ R) (hkR : ∀ i j, (k i j : ℝ) ≤ R)
    (ha : Pairwise fun i j =>
      Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
        (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η)))
    (hb : Pairwise fun i j =>
      Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
        (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) (t : ℝ) :
    Pairwise fun i j =>
      Disjoint
        (realBox (routeCenters a b (30 * R) i t)
          (fun l => routeScales h k i t l * (h i l : ℝ) + 2 * η))
        (realBox (routeCenters a b (30 * R) j t)
          (fun l => routeScales h k j t l * (h j l : ℝ) + 2 * η)) := by
  have hD : 0 ≤ 30 * R := by positivity
  have h4 : 4 * R ≤ 30 * R := by linarith
  have hwidth (i : Fin n) (j : Fin 3) := routeScales_width_le hh hk hvol hhR hkR i t j
  rcases stageSwitch_cases t with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₀, h₂, h₃, h₄⟩ |
    ⟨h₀, h₁, h₃, h₄⟩ | ⟨h₀, h₁, h₂, h₄⟩ | ⟨h₀, h₁, h₂, h₃⟩
  · have hp : ∀ i j, 0 ≤ (h i j : ℝ) + 2 * η := by
      intro i j
      have hhi : (0 : ℝ) < (h i j : ℝ) := by exact_mod_cast hh i j
      linarith
    have hs := spreadCenter_disjoint a (fun i j => (h i j : ℝ) + 2 * η) hD
      (stageSwitch_mem 0 t).1 hp ha
    simpa only [routeCenters, routeCenter_stage₀ a b (30 * R) (u := fun j => stageSwitch j t) h₁ h₂ h₃ h₄,
      routeScales, h₂, balancedScale_zero, Pi.one_apply, one_mul] using hs
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨0, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₁ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₂ h₃ h₄] using
      spreadCenter_separated a hD hij
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨2, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₂ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₃ h₄] using
      private_layers_separated hD hij
  · intro i j hij
    apply padded_boxes_disjoint_of_clearance hR hηR (hwidth i) (hwidth j)
    refine ⟨0, h4.trans ?_⟩
    simpa only [routeCenters, routeCenter_stage₃ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₂ h₄] using
      spreadCenter_separated b hD hij
  · have hp : ∀ i j, 0 ≤ (k i j : ℝ) + 2 * η := by
      intro i j
      have hki : (0 : ℝ) < (k i j : ℝ) := by exact_mod_cast hk i j
      linarith
    have hs := spreadCenter_disjoint b (fun i j => (k i j : ℝ) + 2 * η) hD
      (by have := (stageSwitch_mem 4 t).2; linarith : 0 ≤ 1 - stageSwitch 4 t) hp hb
    simpa only [routeCenters, routeCenter_stage₄ a b (30 * R) (u := fun j => stageSwitch j t) h₀ h₁ h₂ h₃,
      routeScales, h₂, balancedScale_one _ (scaleRatio_det hvol _), scaleRatio_mul_width hh] using hs

noncomputable def stationaryMotionField {n : ℕ} (c d : Fin n → ℝ → Space)
    (h : Fin n → Space) (η : ℝ) : Field :=
  spatialCurl (familyPotential c (fun i => deriv (c i))
    (fun i => diagonalLogVelocity (d i))
    (fun i t j => d i t j * h i j) η)

theorem finite_motion_bound {n : ℕ} {c r : Fin n → ℝ → Space}
    (hc : ∀ i, Continuous (c i)) (hr : ∀ i, Continuous (r i)) (η t₀ t₁ : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i t, t ∈ Set.Icc t₀ t₁ → ∀ j,
      |c i t j| + r i t j + 2 * η ≤ R := by
  let F : ℝ → ℝ := fun t => (∑ i : Fin n, (‖c i t‖ + ‖r i t‖)) + 2 * |η|
  have hF : Continuous F := by fun_prop
  obtain ⟨R, hR, hb⟩ := (isCompact_Icc.image hF).isBounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro i t ht j
  have hs : ‖c i t‖ + ‖r i t‖ ≤ ∑ i : Fin n, (‖c i t‖ + ‖r i t‖) :=
    Finset.single_le_sum (f := fun i : Fin n => ‖c i t‖ + ‖r i t‖)
      (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)
  have hcn : |c i t j| ≤ ‖c i t‖ := norm_le_pi_norm (c i t) j
  have hrn : r i t j ≤ ‖r i t‖ := (le_abs_self _).trans (norm_le_pi_norm (r i t) j)
  have hη := le_abs_self η
  have hf := le_abs_self (F t)
  have hb' : |F t| ≤ R := hb _ ⟨t, ht, rfl⟩
  dsimp [F] at hf
  linarith

theorem stationaryMotionField_realizes {n : ℕ}
    (a h : Fin n → Space) {c d : Fin n → ℝ → Space}
    {η M : ℝ} (hη : 0 < η) (hM : 0 < M)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (hstart : ∀ i t, t ≤ (1 / 4 : ℝ) → c i t = a i ∧ d i t = 1)
    (hend : ∀ i t, (3 / 4 : ℝ) ≤ t → c i t = c i 1 ∧ d i t = d i 1)
    (hdet : ∀ i t, ∏ j : Fin 3, d i t j = 1)
    (hdpos : ∀ i t j, 0 < d i t j) (hdM : ∀ i t j, d i t j ≤ M)
    (hdis : ∀ t, Pairwise fun i j =>
      Disjoint (realBox (c i t) (fun k => d i t k * h i k + 2 * η))
        (realBox (c j t) (fun k => d j t k * h j k + 2 * η))) :
    ContDiff ℝ ∞ (stationaryMotionField c d h η) ∧
    HasCompactSupport (stationaryMotionField c d h η) ∧
    (∀ t x, spatialDivergence (stationaryMotionField c d h η) t x = 0) ∧
    (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      stationaryMotionField c d h η (t, x) = 0) ∧
    ∃ Φ, IsGlobalFlow (stationaryMotionField c d h η) Φ ∧
      (∀ i, ∃ O : Set Space, IsOpen O ∧ realBox (a i) (h i) ⊆ O ∧
        ∀ x ∈ O, ∀ t, Φ t x = affineTrajectory (c i) (d i) (a i) x t) := by
  let r : Fin n → ℝ → Space := fun i t j => d i t j * h i j
  let v : Fin n → ℝ → Space := fun i => deriv (c i)
  let l : Fin n → ℝ → Space := fun i => diagonalLogVelocity (d i)
  have hv (i : Fin n) : ContDiff ℝ ∞ (v i) := contDiff_motion_deriv (hc i)
  have hl (i : Fin n) : ContDiff ℝ ∞ (l i) := contDiff_diagonalLogVelocity (hd i) (hdpos i)
  have hr (i : Fin n) : ContDiff ℝ ∞ (r i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_pi.mp (hd i) j).mul contDiff_const
  have htr (i : Fin n) (t : ℝ) : ∑ j : Fin 3, l i t j = 0 :=
    trace_zero_of_determinant_one (hasDerivAt_diagonalLogVelocity (hd i) (hdpos i) t) (hdet i)
  have htime : ∀ i t, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → v i t = 0 ∧ l i t = 0 := by
    intro i t ht
    refine ⟨deriv_zero_outside_interval (fun s hs => (hstart i s hs).1)
      (fun s hs => (hend i s hs).1) ht, ?_⟩
    have hz := deriv_zero_outside_interval (fun s hs => (hstart i s hs).2)
      (fun s hs => (hend i s hs).2) ht
    ext j
    simp [l, diagonalLogVelocity, hz]
  obtain ⟨R, hR, hbound⟩ := finite_motion_bound (fun i => (hc i).continuous)
    (fun i => (hr i).continuous) η (1 / 4) (3 / 4)
  have hA := contDiff_familyPotential η hc hv hl hr
  have hcp := hasCompactSupport_familyPotential hη hR.le hbound htime
  have hzero : ∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) →
      familyPotential c v l r η (t, x) = 0 := by
    intro t x ht
    exact familyPotential_zero η (fun i => (htime i t ht).1) (fun i => (htime i t ht).2) x
  obtain ⟨hUsm, hUcp, hUdiv, hUt⟩ := curl_field_properties hA hcp hzero
  refine ⟨hUsm, hUcp, hUdiv, hUt, ?_⟩
  obtain ⟨Φ, hΦ⟩ := smooth_compact_globalFlow hUsm hUcp
  refine ⟨Φ, hΦ, ?_⟩
  intro i
  have hδ : 0 < η / (2 * M) := div_pos hη (by positivity)
  refine ⟨openBox (a i) (h i) (η / (2 * M)), isOpen_openBox _ _ _,
    realBox_subset_openBox _ _ hδ, ?_⟩
  intro x hx t
  apply Eq.symm
  apply hΦ.2.2 x (affineTrajectory (c i) (d i) (a i) x)
    (affineTrajectory_initial (hstart i 0 (by norm_num)).1 (hstart i 0 (by norm_num)).2 x)
  intro s
  have hp := affineTrajectory_in_plateau (c := c i) (a i) (h i) hη hM (hdpos i) (hdM i) hx s
  rw [spatialCurl_familyPotential_on_plateau hη hc hv hl hr htr hdis i hp]
  exact hasDerivAt_affineTrajectory ((hc i).differentiable (by simp) s).hasDerivAt
    (hasDerivAt_diagonalLogVelocity (hd i) (hdpos i) s) (a i) x

noncomputable def routedField {n : ℕ} (a b h k : Fin n → RationalSpace) (η : ℚ) : Field :=
  stationaryMotionField (routeCenters a b (30 * (boxDataBound h k : ℝ)))
    (routeScales h k) (fun i => realPoint (h i)) η

theorem routedField_realizes {n : ℕ} (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1)
    {η : ℚ} (hη : 0 < η) (hηR : η < boxDataBound h k / 8)
    (ha : Pairwise fun i j =>
      Disjoint (realBox (realPoint (a i)) (fun l => (h i l : ℝ) + 2 * η))
        (realBox (realPoint (a j)) (fun l => (h j l : ℝ) + 2 * η)))
    (hb : Pairwise fun i j =>
      Disjoint (realBox (realPoint (b i)) (fun l => (k i l : ℝ) + 2 * η))
        (realBox (realPoint (b j)) (fun l => (k j l : ℝ) + 2 * η))) :
    ContDiff ℝ ∞ (routedField a b h k η) ∧ HasCompactSupport (routedField a b h k η) ∧
    (∀ t x, spatialDivergence (routedField a b h k η) t x = 0) ∧
    (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → routedField a b h k η (t, x) = 0) ∧
    ∃ Φ, IsGlobalFlow (routedField a b h k η) Φ ∧ Delivers a b h k Φ := by
  let R : ℝ := boxDataBound h k
  have hR₁ : 1 ≤ R := by dsimp [R]; exact_mod_cast boxDataBound_ge_one h k
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR₁
  have hη' : (0 : ℝ) < η := by exact_mod_cast hη
  have hηR' : (η : ℝ) < R / 8 := by dsimp [R]; exact_mod_cast hηR
  have hbound (i : Fin n) (j : Fin 3) :
      (h i j : ℝ) ≤ R ∧ (k i j : ℝ) ≤ R ∧ scaleRatio h k i j ≤ R := by
    dsimp [R, scaleRatio]
    exact_mod_cast boxDataBound_bounds h k i j
  have hstart (i : Fin n) (t : ℝ) (ht : t ≤ (1 / 4 : ℝ)) :
      routeCenters a b (30 * R) i t = realPoint (a i) ∧ routeScales h k i t = 1 :=
    ⟨routeCenters_before a b (30 * R) i ht, routeScales_before h k i ht⟩
  have hend (i : Fin n) (t : ℝ) (ht : (3 / 4 : ℝ) ≤ t) :
      routeCenters a b (30 * R) i t = routeCenters a b (30 * R) i 1 ∧
      routeScales h k i t = routeScales h k i 1 := by
    rw [routeCenters_after a b (30 * R) i ht, routeCenters_after a b (30 * R) i (t := 1) (by norm_num),
      routeScales_after h k hvol i ht, routeScales_after h k hvol i (t := 1) (by norm_num)]
    exact ⟨rfl, rfl⟩
  have hsep := route_padded_disjoint hh hk hvol hR hη' hηR'
    (fun i j => (hbound i j).1) (fun i j => (hbound i j).2.1) ha hb
  obtain ⟨hsm, hcp, hdiv, htime, Φ, hΦ, hn⟩ :=
    stationaryMotionField_realizes (fun i => realPoint (a i)) (fun i => realPoint (h i))
      hη' hR (contDiff_routeCenters a b (30 * R)) (contDiff_routeScales hh hk)
      hstart hend (routeScales_det hh hk hvol) (routeScales_pos hh hk)
      (routeScales_le hh hk hvol hR₁ (fun i j => (hbound i j).2.2)) hsep
  refine ⟨hsm, hcp, hdiv, htime, Φ, hΦ, ?_⟩
  intro i
  obtain ⟨O, hO, hbO, hmap⟩ := hn i
  refine ⟨O, hO, hbO, ?_⟩
  intro x hx
  rw [hmap x hx 1]
  ext j
  simp only [affineTrajectory, routeCenters_after a b (30 * R) i (t := 1) (by norm_num),
    routeScales_after h k hvol i (t := 1) (by norm_num), scaleRatio, realPoint, prescribedAffine]

theorem exists_routedField_realization
    (n : ℕ) (a b h k : Fin n → RationalSpace)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (ha : Pairwise fun i j => Disjoint (solidBox (a i) (h i)) (solidBox (a j) (h j)))
    (hb : Pairwise fun i j => Disjoint (solidBox (b i) (k i)) (solidBox (b j) (k j)))
    (hvol : ∀ i, ∏ j : Fin 3, k i j / h i j = 1) :
    ∃ η : ℚ, 0 < η ∧
      ContDiff ℝ ∞ (routedField a b h k η) ∧ HasCompactSupport (routedField a b h k η) ∧
      (∀ t x, spatialDivergence (routedField a b h k η) t x = 0) ∧
      (∀ (t : ℝ) x, t ∉ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) → routedField a b h k η (t, x) = 0) ∧
      ∃ Φ, IsGlobalFlow (routedField a b h k η) Φ ∧ Delivers a b h k Φ := by
  have hR : 0 < boxDataBound h k := lt_of_lt_of_le zero_lt_one (boxDataBound_ge_one h k)
  obtain ⟨η, hη, hηR, hap, hbp⟩ := exists_rational_padding a b h k
    (fun i j => (hh i j).le) (fun i j => (hk i j).le) ha hb (boxDataBound h k) hR
  exact ⟨η, hη, routedField_realizes a b h k hh hk hvol hη hηR hap hbp⟩
end BoxTransport.Routing

end

end OAI
