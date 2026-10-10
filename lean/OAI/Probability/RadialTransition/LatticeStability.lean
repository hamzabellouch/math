import OAI.Probability.RadialTransition.ScaledKernels

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

abbrev Cell := Fin 3 → ℤ

def cellOf (x : Position) : Cell := fun k => ⌊4 * x k⌋

def cellMargin (R : ℝ) : ℤ := ⌈4 * R⌉ + 1

def CellReach (R : ℝ) (i j : Cell) : Prop := ∀ k, |j k - i k| ≤ cellMargin R

instance (R : ℝ) (i j : Cell) : Decidable (CellReach R i j) := inferInstanceAs (Decidable (∀ _k, _))

def rangeCells (R : ℝ) (i : Cell) : Finset Cell :=
  Fintype.piFinset fun k => Finset.Icc (i k - cellMargin R) (i k + cellMargin R)

theorem mem_rangeCells (R : ℝ) (i j : Cell) : j ∈ rangeCells R i ↔ CellReach R i j := by
  simp only [rangeCells, Fintype.mem_piFinset, Finset.mem_Icc, CellReach, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem cellReach_symm {R : ℝ} {i j : Cell} (h : CellReach R i j) : CellReach R j i := by
  intro k
  simpa only [abs_sub_comm] using h k

theorem cellMargin_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellMargin R := by
  have hh := Int.le_ceil (4 * R)
  have : (0 : ℝ) ≤ (cellMargin R : ℝ) := by dsimp [cellMargin]; push_cast; linarith
  exact_mod_cast this

theorem card_rangeCells {R : ℝ} (hR : 1 ≤ R) (i : Cell) :
    ((rangeCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  have hm := cellMargin_nonneg (le_trans zero_le_one hR)
  have hm1 : 0 ≤ 2 * cellMargin R + 1 := by omega
  have heq : (rangeCells R i).card = (2 * cellMargin R + 1).toNat ^ 3 := by
    simp only [rangeCells, Fintype.card_piFinset, Int.card_Icc]
    simp_rw [show ∀ k, i k + cellMargin R + 1 - (i k - cellMargin R) =
        2 * cellMargin R + 1 by intro k; ring]
    simp
  rw [heq]
  have hcast : (((2 * cellMargin R + 1).toNat : ℕ) : ℝ) = 2 * (cellMargin R : ℝ) + 1 := by
    have hh := Int.toNat_of_nonneg hm1
    exact_mod_cast hh
  push_cast
  rw [hcast]
  have hb : 2 * (cellMargin R : ℝ) + 1 ≤ 13 * R := by
    have hc := Int.ceil_lt_add_one (4 * R)
    dsimp [cellMargin]
    push_cast
    linarith
  calc
    _ ≤ (13 * R) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast hm1) hb 3
    _ = _ := by ring

theorem cellReach_of_dist {x y : Position} {R : ℝ} (hxy : dist x y ≤ R) :
    CellReach R (cellOf x) (cellOf y) := by
  intro k
  have hc : |x k - y k| ≤ R := by
    simpa only [Real.dist_eq] using (PiLp.dist_apply_le x y k).trans hxy
  have hxl := Int.floor_le (4 * x k)
  have hyl := Int.floor_le (4 * y k)
  have hxu := Int.lt_floor_add_one (4 * x k)
  have hyu := Int.lt_floor_add_one (4 * y k)
  have hceil := Int.le_ceil (4 * R)
  have hb : |((⌊4 * y k⌋ : ℤ) : ℝ) - (⌊4 * x k⌋ : ℤ)| ≤ (⌈4 * R⌉ : ℤ) + (1 : ℝ) := by
    rcases abs_le.mp hc with ⟨hc1, hc2⟩
    apply abs_le.mpr
    constructor <;> linarith
  dsimp [cellOf, cellMargin]
  exact_mod_cast hb

def cellMajorant (R W : ℝ) (i j : Cell) : ℝ :=
  if CellReach R i j then (R ^ 3)⁻¹ * W else 0

theorem cellMajorant_nonneg {R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W) (i j : Cell) :
    0 ≤ cellMajorant R W i j :=
  ite_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) hW) le_rfl

theorem cellMajorant_symm (R W : ℝ) (i j : Cell) :
    cellMajorant R W i j = cellMajorant R W j i := by
  unfold cellMajorant
  have hh : CellReach R i j ↔ CellReach R j i := ⟨cellReach_symm, cellReach_symm⟩
  by_cases h : CellReach R i j
  · simp [h, hh.mp h]
  · simp [h, show ¬ CellReach R j i from fun hji => h (hh.mpr hji)]

theorem cellMajorant_row {I : Type uI} [Fintype I]
    (e : I → Cell) (he : Function.Injective e) {R W : ℝ} (hR : 1 ≤ R) (hW : 0 ≤ W)
    (i : Cell) : ∑ j, cellMajorant R W i (e j) ≤ 2197 * W := by
  classical
  let s := Finset.univ.filter (fun j => CellReach R i (e j))
  have hcard : s.card ≤ (rangeCells R i).card := by
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact (mem_rangeCells R i (e j)).mpr (Finset.mem_filter.mp hj).2
    · exact he.injOn
  have hsum : (∑ j, cellMajorant R W i (e j)) = (s.card : ℝ) * ((R ^ 3)⁻¹ * W) := by
    simp [cellMajorant, s, ← Finset.sum_filter]
  rw [hsum]
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc : (s.card : ℝ) ≤ 2197 * R ^ 3 :=
    (by exact_mod_cast hcard : (s.card : ℝ) ≤ (rangeCells R i).card).trans (card_rangeCells hR i)
  calc
    _ ≤ (2197 * R ^ 3) * ((R ^ 3)⁻¹ * W) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR0.le _)) hW)
    _ = _ := by field_simp

theorem same_cell_diameter {x y : Position} (h : cellOf x = cellOf y) :
    dist x y ≤ 1 := by
  have hc (k : Fin 3) : |x k - y k| ≤ 1 / 4 := by
    have hh : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxl := Int.floor_le (4 * x k)
    have hxu := Int.lt_floor_add_one (4 * x k)
    have hyl := Int.floor_le (4 * y k)
    have hyu := Int.lt_floor_add_one (4 * y k)
    rw [← hh] at hyl hyu
    apply abs_le.mpr
    constructor <;> linarith
  have hs : dist x y ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ k : Fin 3, (1 / 4 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Real.dist_eq] using pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem scaledBumpProfile_le_cellMajorant {R : ℝ} (hR : 1 ≤ R) (x y : Position) :
    scaledBumpProfile R (dist x y) ≤ cellMajorant R bumpIntegral⁻¹ (cellOf x) (cellOf y) := by
  have hR0 := lt_of_lt_of_le zero_lt_one hR
  by_cases h : CellReach R (cellOf x) (cellOf y)
  · simp only [cellMajorant, ite_eq_left h, scaledBumpProfile]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (bumpProfile_bound _))
      (inv_nonneg.mpr (pow_nonneg hR0.le _))
  · have hd : R ≤ dist x y := le_of_not_ge (fun hh => h (cellReach_of_dist hh))
    simp [cellMajorant, h, scaledBumpProfile_zero hR0 hd]

def familyCellMajorant (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) : ℝ :=
  t * ∑' n, a n * cellMajorant (R n) bumpIntegral⁻¹ i j

theorem summable_cellMajorant {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i j : Cell) :
    Summable (fun n => a n * cellMajorant (R n) bumpIntegral⁻¹ i j) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
      (inv_nonneg.mpr bumpIntegral_pos.le) i j)
  · intro n
    apply mul_le_mul_of_nonneg_left ?_ (ha n)
    unfold cellMajorant
    split_ifs
    · exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
        (inv_le_one_of_one_le₀ (one_le_pow₀ (hR n)))
    · exact inv_nonneg.mpr bumpIntegral_pos.le

theorem familyCellMajorant_nonneg {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (i j : Cell) :
    0 ≤ familyCellMajorant t a R i j := by
  apply mul_nonneg ht (tsum_nonneg _)
  intro n
  exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
    (inv_nonneg.mpr bumpIntegral_pos.le) i j)

theorem familyCellMajorant_symm (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) :
    familyCellMajorant t a R i j = familyCellMajorant t a R j i := by
  unfold familyCellMajorant
  congr 1
  apply tsum_congr
  intro n
  rw [cellMajorant_symm]

theorem familyCellMajorant_row {I : Type uI} [Fintype I] (e : I → Cell)
    (he : Function.Injective e) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i : Cell) :
    ∑ j, familyCellMajorant t a R i (e j) ≤ 2197 * t * bumpIntegral⁻¹ * ∑' n, a n := by
  simp only [familyCellMajorant, ← Finset.mul_sum]
  have hswap : (∑ j, ∑' n, a n * cellMajorant (R n) bumpIntegral⁻¹ i (e j)) =
      ∑' n, a n * ∑ j, cellMajorant (R n) bumpIntegral⁻¹ i (e j) := by
    rw [← Summable.tsum_finsetSum (fun j _ => summable_cellMajorant ha hR hs i (e j))]
    simp_rw [Finset.mul_sum]
  rw [hswap]
  calc
    _ ≤ t * ∑' n, a n * (2197 * bumpIntegral⁻¹) := by
      apply mul_le_mul_of_nonneg_left ?_ ht
      apply Summable.tsum_le_tsum
      · intro n
        exact mul_le_mul_of_nonneg_left
          (cellMajorant_row e he (hR n) (inv_nonneg.mpr bumpIntegral_pos.le) i) (ha n)
      · simpa only [Finset.mul_sum] using
          summable_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
            summable_cellMajorant ha hR hs i (e j))
      · exact hs.mul_right _
    _ = _ := by rw [tsum_mul_right]; ring

theorem attraction_le_familyCellMajorant {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (x y : Position) :
    t * attractionProfile a R (dist x y) ≤ familyCellMajorant t a R (cellOf x) (cellOf y) := by
  apply mul_le_mul_of_nonneg_left ?_ ht
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (scaledBumpProfile_le_cellMajorant (hR n) x y) (ha n))
    (summable_attractionProfile ha hR hs _) (summable_cellMajorant ha hR hs _ _)

theorem family_energy_cell_bound {I : Type uI} [Fintype I] {N : ℕ}
    (e : I → Cell) (he : Function.Injective e) (q : Fin N → I) (x : Fin N → Position)
    (hq : ∀ j, e (q j) = cellOf (x j)) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
        (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤ energy (familyPotential t a R) x := by
  have hh := modified_energy_cell_bound ht q x (fun _ _ => 1)
    (fun i j => t * attractionProfile a R (dist (x i) (x j)))
    (fun i j => familyCellMajorant t a R (e i) (e j))
    (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun i j hij => same_cell_diameter (by rw [← hq i, ← hq j, hij]))
    (fun i j => mul_nonneg ht (attractionProfile_nonneg ha hR _))
    (fun i j => by rw [dist_comm (x i) (x j)])
    (fun i j => by simpa only [hq] using attraction_le_familyCellMajorant ht ha hR hs (x i) (x j))
    (fun i j => familyCellMajorant_nonneg ht ha hR (e i) (e j))
    (fun i j => familyCellMajorant_symm t a R (e i) (e j))
    (fun i => familyCellMajorant_row e he ht ha hR hs (e i))
  simpa only [one_mul, energy, familyPotential, coe_nndist] using hh

theorem stable_familyPotential {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 8) :
    StableWith (familyPotential t a R) (t ^ 2 / 2) := by
  classical
  intro N x
  let S : Finset Cell := Finset.univ.image (fun j => cellOf (x j))
  let q : Fin N → S := fun j => ⟨cellOf (x j), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hh := family_energy_cell_bound (fun i : S => (i : Cell)) Subtype.val_injective q x
    (fun _ => rfl) ht ha hR hs
  have hn : 0 ≤ (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
      (∑ i, occupation q i ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hcoerc) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  change -(t ^ 2 / 2 * (N : ℝ)) ≤ _
  linarith

theorem decay_familyPotential {t : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hw : Summable (fun n => a n * R n ^ (1 / 32 : ℝ))) :
    AlgebraicDecayWith (familyPotential t a R)
      (t ^ 2 * (2 : ℝ) ^ (3 + 1 / 32 : ℝ) +
        t * bumpIntegral⁻¹ * (∑' n, a n * R n ^ (1 / 32 : ℝ))) := by
  intro r hr
  have ht0 := zero_le_one.trans ht
  have hr0 : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr
  have hd := attractionProfile_decay ha hR hs (show (0 : ℝ) ≤ 1 / 32 by norm_num) hw hr
  have hc : coreReal t r ≤ t ^ 2 * (2 : ℝ) ^ (3 + 1 / 32 : ℝ) *
      (r : ℝ) ^ (-(3 + 1 / 32 : ℝ)) := by
    by_cases hrr : 2 ≤ (r : ℝ)
    · have hinv : 1 / t ≤ 1 := by simpa using inv_le_one_of_one_le₀ ht
      rw [coreReal_zero_outer (lt_of_lt_of_le zero_lt_one ht) (by linarith)]
      positivity
    · have hpow : (2 : ℝ) ^ (-(3 + 1 / 32 : ℝ)) ≤
          (r : ℝ) ^ (-(3 + 1 / 32 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 (le_of_not_ge hrr) (by norm_num)
      calc
        _ ≤ t ^ 2 := coreReal_le _ _
        _ = t ^ 2 * (2 : ℝ) ^ (3 + 1 / 32 : ℝ) * (2 : ℝ) ^ (-(3 + 1 / 32 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hab := abs_sub (coreReal t (r : ℝ)) (t * attractionProfile a R (r : ℝ))
  rw [abs_of_nonneg (coreReal_nonneg _ _), abs_of_nonneg
    (mul_nonneg ht0 (attractionProfile_nonneg ha hR _))] at hab
  have hc' := add_le_add hc (mul_le_mul_of_nonneg_left hd ht0)
  change |coreReal t (r : ℝ) - t * attractionProfile a R (r : ℝ)| ≤ _
  have heq : -(3 : ℝ) - 1 / 32 = -(3 + 1 / 32 : ℝ) := by ring
  rw [heq]
  convert (le_trans hab hc') using 1; first | rfl | (ring_nf; rfl)

def cubeCells (L : ℝ) : Finset Cell :=
  Fintype.piFinset (fun _ => Finset.Icc 0 ⌊4 * L⌋)

theorem cellOf_mem_cubeCells {L : ℝ} {x : Position} (hx : x ∈ cube L) :
    cellOf x ∈ cubeCells L := by
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellOf]
  intro k
  exact ⟨Int.floor_nonneg.mpr (by linarith [(hx k).1]), Int.floor_mono (by linarith [(hx k).2])⟩

theorem card_cubeCells {L : ℝ} (hL : 1 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ 216 * L ^ 3 := by
  have hf : 0 ≤ ⌊4 * L⌋ := Int.floor_nonneg.mpr (by linarith)
  have heq : (cubeCells L).card = (⌊4 * L⌋ + 1).toNat ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, Int.card_Icc]
  rw [heq]
  have hc : (((⌊4 * L⌋ + 1).toNat : ℕ) : ℝ) = (⌊4 * L⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ ⌊4 * L⌋ + 1 by omega))
  push_cast
  rw [hc]
  have hb : (⌊4 * L⌋ : ℝ) + 1 ≤ 6 * L := by
    have hh := Int.floor_le (4 * L)
    linarith
  calc
    _ ≤ (6 * L) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast (show 0 ≤ ⌊4 * L⌋ + 1 by omega)) hb 3
    _ = _ := by ring

theorem square_count_le_card_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) : (Fintype.card V : ℝ) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, occupation q i ^ 2 := by
  rw [← sum_occupation q]
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := occupation q)

theorem family_density_stability {t L : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t) (hL : 1 ≤ L)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 16)
    {N : ℕ} (x : Fin N → Position) (hx : x ∈ configurationCube L N) :
    t ^ 2 / 3456 * (N : ℝ) ^ 2 / L ^ 3 - t ^ 2 / 2 * N ≤ energy (familyPotential t a R) x := by
  classical
  let S := cubeCells L
  let q : Fin N → S := fun j => ⟨cellOf (x j), cellOf_mem_cubeCells (hx j)⟩
  have hh := family_energy_cell_bound (fun i : S => (i : Cell)) Subtype.val_injective q x
    (fun _ => rfl) ht ha hR hs
  have hsum : 0 ≤ ∑ i, occupation q i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn := square_count_le_card_occupation q
  have hcard : (Fintype.card S : ℝ) ≤ 216 * L ^ 3 := by
    simpa using card_cubeCells hL
  have hn' := hn.trans (mul_le_mul_of_nonneg_right hcard hsum)
  have hL0 : 0 < L ^ 3 := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  have hocc : (N : ℝ) ^ 2 / (216 * L ^ 3) ≤ ∑ i, occupation q i ^ 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hL0)).mpr
    simpa only [Fintype.card_fin, mul_comm] using hn'
  have hocc' := mul_le_mul_of_nonneg_left hocc (show 0 ≤ t ^ 2 / 16 by positivity)
  have heq : t ^ 2 / 16 * ((N : ℝ) ^ 2 / (216 * L ^ 3)) =
      t ^ 2 / 3456 * (N : ℝ) ^ 2 / L ^ 3 := by ring
  rw [heq] at hocc'
  nlinarith [mul_nonneg (show 0 ≤ t ^ 2 / 16 - 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 by linarith) hsum]

end RadialTransition

end

end OAI
