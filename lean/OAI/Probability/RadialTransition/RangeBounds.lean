import OAI.Probability.RadialTransition.MacroRegions

namespace OAI

universe uG uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma cellMargin_mono {R S : ℝ} (h : R ≤ S) : cellMargin R ≤ cellMargin S := by
  unfold cellMargin
  have hc := Int.ceil_mono (show 4*R ≤ 4*S by linarith)
  omega

lemma cellReach_mono {R S : ℝ} {i j : Cell} (h : R ≤ S) (hc : CellReach R i j) : CellReach S i j :=
  fun d => (hc d).trans (cellMargin_mono h)

lemma cellMargin_toNat_le {R : ℝ} (hR : 1 ≤ R) : ((cellMargin R).toNat:ℝ) ≤ 6*R := by
  have hm := cellMargin_nonneg (zero_le_one.trans hR)
  have he : ((cellMargin R).toNat:ℝ) = (cellMargin R:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
  rw [he]
  have hc := Int.ceil_lt_add_one (4*R)
  unfold cellMargin
  push_cast
  linarith

lemma deletionMajorant_le {G : Type uG} [DecidableEq G] (g : Cell → G)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j) (i j : Cell) :
    deletionMajorant g W i j ≤ W i j := by
  unfold deletionMajorant
  split_ifs
  · exact hW i j
  · exact le_rfl

lemma deletionMajorant_grid_sum {m q : ℕ} (hq : 0 < q) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ k, ∑ j : GridIndex (m*q), W k (gridEmbed j) ≤ C)
    (hsupp : ∀ i j, ¬ CellReach R i j → W i j = 0) :
    ∑ i : GridIndex (m*q), ∑ j : GridIndex (m*q),
      deletionMajorant (macroOf q) W (gridEmbed i) (gridEmbed j) ≤
      (m:ℝ)^3*(6*(cellMargin R).toNat*q^2)*C := by
  apply grid_sum_boundary_bound hq hC
  · intro i
    exact (Finset.sum_le_sum (fun j _ => deletionMajorant_le (macroOf q) hW _ _)).trans (hrow _)
  · intro i j hj
    apply Finset.sum_eq_zero
    intro k _
    by_cases hc : CellReach R (gridEmbed (blockEmbed i j)) (gridEmbed k)
    · have hk : macroOf q (gridEmbed k) = gridEmbed i := inner_block_macro hq i j hj (by
        intro d
        simpa only [Int.toNat_of_nonneg (cellMargin_nonneg hR)] using hc d)
      simp only [deletionMajorant, blockEmbed_macro hq, hk, ite_true]
    · simp only [deletionMajorant, hsupp _ _ hc, ite_self]

lemma deletionMajorant_grid_sum_range {m q : ℕ} (hq : 0 < q) {R C : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    {W : Cell → Cell → ℝ} (hW : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ k, ∑ j : GridIndex (m*q), W k (gridEmbed j) ≤ C)
    (hsupp : ∀ i j, ¬ CellReach R i j → W i j = 0) :
    ∑ i : GridIndex (m*q), ∑ j : GridIndex (m*q),
      deletionMajorant (macroOf q) W (gridEmbed i) (gridEmbed j) ≤
      36*(m:ℝ)^3*q^2*R*C := by
  calc
    _ ≤ (m:ℝ)^3*(6*(cellMargin R).toNat*q^2)*C :=
      deletionMajorant_grid_sum hq (zero_le_one.trans hR) hC hW hrow hsupp
    _ ≤ (m:ℝ)^3*(6*(6*R)*q^2)*C := by gcongr; exact cellMargin_toNat_le hR
    _ = _ := by ring

def referenceMajorant (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) : ℝ :=
  cellMajorant 2 (8*t^2) i j + familyCellMajorant t a R i j

lemma referenceMajorant_nonneg {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (i j : Cell) :
    0 ≤ referenceMajorant t a R i j :=
  add_nonneg (cellMajorant_nonneg (by norm_num) (by positivity) i j)
    (familyCellMajorant_nonneg ht ha hR i j)

lemma referenceMajorant_row {I : Type uI} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t) (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable a) (i : Cell) :
    ∑ j, referenceMajorant t a R i (e j) ≤ 2197*8*t^2+2197*t*bumpIntegral⁻¹*∑' n, a n := by
  simp only [referenceMajorant, Finset.sum_add_distrib]
  have hc := cellMajorant_row e he (R := 2) (W := 8*t^2) (by norm_num) (by positivity) i
  have ha' := familyCellMajorant_row e he ht ha hR hs i
  linarith

lemma referenceMajorant_support {t R₀ : ℝ} {a R : ℕ → ℝ} (hR₀ : 2 ≤ R₀)
    (hrange : ∀ n, R n ≤ R₀) (i j : Cell) (hc : ¬ CellReach R₀ i j) :
    referenceMajorant t a R i j = 0 := by
  have hc₂ : ¬ CellReach 2 i j := fun h => hc (cellReach_mono hR₀ h)
  have hcn (n : ℕ) : ¬ CellReach (R n) i j := fun h => hc (cellReach_mono (hrange n) h)
  simp only [referenceMajorant, familyCellMajorant, cellMajorant, ite_eq_right hc₂, ite_eq_right (hcn _),
    mul_zero, tsum_zero, add_zero]

lemma core_le_cellMajorant {t : ℝ} (ht : 1 ≤ t) (x y : Position) :
    corePotential t (nndist x y) ≤ cellMajorant 2 (8*t^2) (cellOf x) (cellOf y) := by
  by_cases hc : CellReach 2 (cellOf x) (cellOf y)
  · simp only [cellMajorant, ite_eq_left hc]
    have he : ((2:ℝ)^3)⁻¹*(8*t^2) = t^2 := by ring
    rw [he]
    exact coreReal_le t (dist x y)
  · have hd : 2 < dist x y := lt_of_not_ge (fun h => hc (cellReach_of_dist h))
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hz : corePotential t (nndist x y) = 0 := coreReal_zero_outer ht0
      (by change 1+1/t ≤ dist x y; have hi := one_div_le_one_div_of_le zero_lt_one ht; norm_num only [div_one] at hi; linarith)
    rw [hz, cellMajorant, ite_eq_right hc]

lemma family_abs_le_referenceMajorant {t : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (x y : Position) :
    |radialPair (familyPotential t a R) x y| ≤ referenceMajorant t a R (cellOf x) (cellOf y) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hc : |coreReal t (dist x y)| = coreReal t (dist x y) := abs_of_nonneg (coreReal_nonneg _ _)
  have ha' : |t*attractionProfile a R (dist x y)| = t*attractionProfile a R (dist x y) :=
    abs_of_nonneg (mul_nonneg ht0 (attractionProfile_nonneg ha hR _))
  calc
    _ ≤ |coreReal t (dist x y)|+|t*attractionProfile a R (dist x y)| := abs_sub _ _
    _ = coreReal t (dist x y)+t*attractionProfile a R (dist x y) := by rw [hc, ha']
    _ ≤ _ := add_le_add (core_le_cellMajorant ht x y) (attraction_le_familyCellMajorant ht0 ha hR hs x y)

def referenceRowBound (t A : ℝ) : ℝ := 2197*8*t^2+2197*t*bumpIntegral⁻¹*A

def boxPressureConstant (t β h A : ℝ) : ℝ :=
  288*β*localMomentBound t β (t*h)*referenceRowBound t A/t

lemma referenceRowBound_nonneg {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) :
    0 ≤ referenceRowBound t A := by
  unfold referenceRowBound
  have hb := bumpIntegral_pos.le
  positivity

lemma boxPressureConstant_nonneg {t β h A : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hA : 0 ≤ A) :
    0 ≤ boxPressureConstant t β h A := by
  unfold boxPressureConstant
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (localMomentBound_nonneg hβ _))
    (referenceRowBound_nonneg ht hA)) ht

lemma family_aligned_box_comparison {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, R n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, a n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t a R) t ((m:ℝ)*q/4) β h-
      finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h| ≤
      boxPressureConstant t β h (∑' n, a n)*R₀/((q:ℝ)/4) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  let : NeZero (m*q) := ⟨ne_of_gt (Nat.mul_pos hm hq)⟩
  have hcont := continuous_familyPotential ha hR hs t
  have hbound := bounded_familyPotential ha hR hs t
  have hstable := stable_family_of_master ht0.le ha hR hs hs (fun _ => le_rfl) hrow
  let φ := familyPotential t a R
  let W := referenceMajorant t a R
  have hW : ∀ i j, 0 ≤ W i j := referenceMajorant_nonneg ht0.le ha hR
  have hcost := deletedPair_grid_bound (@gridEmbed (m*q)) (gridEmbed_injective _) (macroOf q)
    (measurableSet_halfCube ((m*q:ℕ)/4)) (halfCube_grid_cover (m*q)) hcont
    (show Continuous (0 : Potential) from continuous_const) ht0 hβ (t*h)
    (familyCellMajorant t a R) (fun _ _ => 0) W
    (familyCellMajorant_nonneg ht0.le ha hR) (fun _ _ => le_rfl)
    (fun i j => by simp only [add_zero, familyCellMajorant_symm])
    (fun i => by simpa only [add_zero] using
      (familyCellMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le ha hR hs (gridEmbed i)).trans hrow)
    (familyPotential_grid_lower ht0.le ha ha hR hs hs (fun _ => le_rfl))
    (fun _ _ => by simp only [neg_zero, radialPair, Pi.zero_apply, le_refl]) hW
    (family_abs_le_referenceMajorant ht ha hR hs)
  have hA : volume (halfCube (((m:ℝ)*q)/4)) ≠ ⊤ := by rw [volume_halfCube]; finiteness
  have hgrand := pairGrand_radial hcont hbound hstable hβ.le hA (t*h)
  simp only [add_zero, Nat.cast_mul] at hcost
  rw [hgrand, grandOn_halfCube hcont hbound hstable hβ.le, grandOn_cube,
    deletedPair_macro_factorization hq hcont hbound hstable hβ.le (t*h), grandOn_cube,
    Real.log_pow] at hcost
  have hC : 0 ≤ referenceRowBound t (∑' n, a n) := referenceRowBound_nonneg ht0.le (tsum_nonneg ha)
  have hsum := deletionMajorant_grid_sum_range (m := m) hq (show 1 ≤ R₀ by linarith) hC hW
    (referenceMajorant_row (@gridEmbed (m*q)) (gridEmbed_injective _) ht0.le ha hR hs)
    (referenceMajorant_support hR₀ hrange)
  have hcoeff : 0 ≤ β/2*localMomentBound t β (t*h) :=
    mul_nonneg (by positivity) (localMomentBound_nonneg hβ.le _)
  have hlog := hcost.trans (mul_le_mul_of_nonneg_left hsum hcoeff)
  have hden : 0 < t*((m:ℝ)*q/4)^3 := by positivity
  have he : finiteGrandPressure φ t ((m:ℝ)*q/4) β h-finiteGrandPressure φ t ((q:ℝ)/4) β h =
      (Real.log (grandPartition φ t ((m:ℝ)*q/4) β h)-(m:ℝ)^3*Real.log (grandPartition φ t ((q:ℝ)/4) β h)) /
        (t*((m:ℝ)*q/4)^3) := by
    unfold finiteGrandPressure
    field_simp
  change |finiteGrandPressure φ t _ β h-finiteGrandPressure φ t _ β h| ≤ _
  rw [he, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  convert hlog using 1 <;> dsimp only [φ, W, boxPressureConstant] at *
  · simp only [Nat.cast_pow]
  · field_simp
    ring

theorem finiteGrandPressure_family_box_error {q : ℕ} (hq : 0 < q)
    {t β h R₀ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, R n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, a n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h-
      grandPressure (familyPotential t a R) t β h| ≤
      boxPressureConstant t β h (∑' n, a n)*R₀/((q:ℝ)/4) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hl := (grandPressure_spec (continuous_familyPotential ha hR hs t)
    (bounded_familyPotential ha hR hs t)
    (stable_family_of_master ht0.le ha hR hs hs (fun _ => le_rfl) hrow)
    ht0 hβ.le (fun r hr => familyPotential_nonpos_outer ha hR ht hr) h).1
  have hL : Tendsto (fun m : ℕ => (m:ℝ)*q/4) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hq0).atTop_div_const (by norm_num)
  have hh := ((hl.comp hL).sub_const (finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h)).abs
  rw [abs_sub_comm]
  apply le_of_tendsto hh
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  exact family_aligned_box_comparison hm hq ht hβ ha hR hs hR₀ hrange hrow

def bumpLip : ℝ≥0 := Classical.choose
  (ContDiff.lipschitzWith_of_hasCompactSupport compactSupport_bump contDiff_bump (by simp))

lemma lipschitz_bump : LipschitzWith bumpLip bump := Classical.choose_spec
  (ContDiff.lipschitzWith_of_hasCompactSupport compactSupport_bump contDiff_bump (by simp))

lemma scaledBump_nonneg {R : ℝ} (hR : 0 < R) (x : Position) : 0 ≤ scaledBump R x := by
  rw [scaledBump_radial hR]
  exact scaledBumpProfile_nonneg hR _

lemma continuous_scaledBump (R : ℝ) : Continuous (scaledBump R) :=
  continuous_const.mul (contDiff_bump.continuous.comp (continuous_id.const_smul R⁻¹))

lemma integrable_scaledBump {R : ℝ} (hR : 0 < R) : Integrable (scaledBump R) := by
  have hc : HasCompactSupport (scaledBump R) :=
    (compactSupport_bump.comp_smul (inv_ne_zero hR.ne')).mul_left
  exact (continuous_scaledBump R).integrable_of_hasCompactSupport hc

lemma scaledBump_bound {R : ℝ} (hR : 0 < R) (x : Position) :
    |scaledBump R x| ≤ (R^3)⁻¹*bumpIntegral⁻¹ := by
  unfold scaledBump
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))]
  exact mul_le_mul_of_nonneg_left (bumpProfile_bound _) (by positivity)

lemma scaledBump_zero {R : ℝ} (hR : 0 < R) {x : Position} (hx : R ≤ ‖x‖) : scaledBump R x = 0 := by
  rw [scaledBump_radial hR, scaledBumpProfile_zero hR hx]

lemma scaledBump_symm (R : ℝ) (x y : Position) : scaledBump R (x-y) = scaledBump R (y-x) := by
  unfold scaledBump bump
  rw [← neg_sub x y, smul_neg, norm_neg]

lemma scaledBump_oscillation {R : ℝ} (hR : 0 < R) (x y : Position) :
    |scaledBump R x-scaledBump R y| ≤ (bumpLip:ℝ)/R^4*dist x y := by
  have hh := lipschitz_bump.dist_le_mul (R⁻¹ • x) (R⁻¹ • y)
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)] at hh
  simp only [Real.dist_eq] at hh
  calc
    _ = (R^3)⁻¹*|bump (R⁻¹ • x)-bump (R⁻¹ • y)| := by
      unfold scaledBump
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (R^3)⁻¹*((bumpLip:ℝ)*(R⁻¹*dist x y)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

lemma macroOrigin_mem {q : ℕ} (hq : 0 < q) (k : Cell) : macroOrigin q k ∈ macroRegion q k := by
  rw [macroRegion_translate hq]
  intro d
  change 0 ≤ (macroOrigin q k) d-(macroOrigin q k) d ∧
    (macroOrigin q k) d-(macroOrigin q k) d < (q:ℝ)/4
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  simp only [sub_self]; exact ⟨le_rfl, by positivity⟩

lemma macro_distance_origin {q : ℕ} (hq : 0 < q) (k : Cell) {x : Position}
    (hx : x ∈ macroRegion q k) : dist x (macroOrigin q k) ≤ (q:ℝ)/2 := by
  rw [macroRegion_translate hq] at hx
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hc (d : Fin 3) : |x d-(macroOrigin q k) d| ≤ (q:ℝ)/4 := by
    have hh : 0 ≤ x d-(macroOrigin q k) d ∧ x d-(macroOrigin q k) d < (q:ℝ)/4 := hx d
    rw [abs_of_nonneg hh.1]
    exact hh.2.le
  have hs : dist x (macroOrigin q k)^2 ≤ 3*((q:ℝ)/4)^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _d : Fin 3, ((q:ℝ)/4)^2 := by
        apply Finset.sum_le_sum
        intro d _
        simpa only [Real.dist_eq] using pow_le_pow_left₀ (abs_nonneg _) (hc d) 2
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := macroOrigin q k)]

lemma macro_difference_dist {q : ℕ} (hq : 0 < q) {i j : Cell} {x y : Position}
    (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) :
    dist (x-y) (macroOrigin q i-macroOrigin q j) ≤ (q:ℝ) := by
  exact (dist_sub_sub_le x y _ _).trans (by linarith [macro_distance_origin hq i hx, macro_distance_origin hq j hy])

lemma macroReach_of_dist {q : ℕ} (hq : 0 < q) {R : ℝ} {i j : Cell} {x y : Position}
    (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) (hd : dist x y ≤ R) :
    CellReach (R/q+1) i j := by
  rw [macroRegion_translate hq] at hx hy
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  intro d
  have hxy : |y d-x d| ≤ R := by
    simpa only [Real.dist_eq, abs_sub_comm] using (PiLp.dist_apply_le x y d).trans hd
  have hxd : 0 ≤ x d-(q:ℝ)*(i d:ℝ)/4 ∧ x d-(q:ℝ)*(i d:ℝ)/4 < (q:ℝ)/4 := hx d
  have hyd : 0 ≤ y d-(q:ℝ)*(j d:ℝ)/4 ∧ y d-(q:ℝ)*(j d:ℝ)/4 < (q:ℝ)/4 := hy d
  have hceil := Int.le_ceil (4*(R/(q:ℝ)+1))
  have he : (q:ℝ)*(4*(R/(q:ℝ)+1)) = 4*R+4*q := by field_simp
  have hh := mul_le_mul_of_nonneg_left hceil hq0.le
  change (q:ℝ)*(4*(R/(q:ℝ)+1)) ≤ (q:ℝ)*(⌈4*(R/(q:ℝ)+1)⌉:ℝ) at hh
  rw [he] at hh
  have hc : |((j d:ℤ):ℝ)-(i d:ℝ)| ≤ (⌈4*(R/(q:ℝ)+1)⌉:ℤ)+(1:ℝ) := by
    apply abs_le.mpr
    have hab := abs_le.mp hxy
    constructor <;> nlinarith
  unfold cellMargin
  exact_mod_cast hc

def macroKernel (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  scaledBump R (macroOrigin q i-macroOrigin q j)

def macroKernelError (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  if CellReach (R/q+1) i j then (bumpLip:ℝ)/R^4*q else 0

def macroKernelUpper (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  macroKernel q R i j+macroKernelError q R i j

def macroKernelLower (q : ℕ) (R : ℝ) (i j : Cell) : ℝ :=
  max 0 (macroKernel q R i j-macroKernelError q R i j)

lemma macroKernelError_nonneg (q : ℕ) (R : ℝ) (i j : Cell) : 0 ≤ macroKernelError q R i j := by
  unfold macroKernelError
  split_ifs <;> positivity

lemma macroKernelUpper_nonneg {q : ℕ} {R : ℝ} (hR : 0 < R) (i j : Cell) :
    0 ≤ macroKernelUpper q R i j := add_nonneg (scaledBump_nonneg hR _) (macroKernelError_nonneg _ _ _ _)

lemma macroKernelLower_nonneg (q : ℕ) (R : ℝ) (i j : Cell) : 0 ≤ macroKernelLower q R i j := le_max_left _ _

lemma macroKernel_symm (q : ℕ) (R : ℝ) (i j : Cell) : macroKernel q R i j = macroKernel q R j i :=
  scaledBump_symm _ _ _

lemma macroKernelError_symm (q : ℕ) (R : ℝ) (i j : Cell) :
    macroKernelError q R i j = macroKernelError q R j i := by
  unfold macroKernelError
  have he : CellReach (R/q+1) i j ↔ CellReach (R/q+1) j i := ⟨cellReach_symm, cellReach_symm⟩
  simp only [he]

lemma macroKernelUpper_symm (q : ℕ) (R : ℝ) (i j : Cell) :
    macroKernelUpper q R i j = macroKernelUpper q R j i := by
  unfold macroKernelUpper
  rw [macroKernel_symm, macroKernelError_symm]

lemma macroKernelLower_symm (q : ℕ) (R : ℝ) (i j : Cell) :
    macroKernelLower q R i j = macroKernelLower q R j i := by
  unfold macroKernelLower
  rw [macroKernel_symm, macroKernelError_symm]

lemma macroKernel_pair_bounds {q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 < R)
    {i j : Cell} {x y : Position} (hx : x ∈ macroRegion q i) (hy : y ∈ macroRegion q j) :
    macroKernelLower q R i j ≤ scaledBump R (x-y) ∧
      scaledBump R (x-y) ≤ macroKernelUpper q R i j := by
  have hc : |scaledBump R (x-y)-macroKernel q R i j| ≤ macroKernelError q R i j := by
    by_cases h : CellReach (R/q+1) i j
    · rw [macroKernelError, ite_eq_left h]
      exact (scaledBump_oscillation hR _ _).trans
        (mul_le_mul_of_nonneg_left (macro_difference_dist hq hx hy) (by positivity))
    · have hd : R < dist x y := lt_of_not_ge (fun hh => h (macroReach_of_dist hq hx hy hh))
      have hd' : R < dist (macroOrigin q i) (macroOrigin q j) :=
        lt_of_not_ge (fun hh => h (macroReach_of_dist hq (macroOrigin_mem hq i) (macroOrigin_mem hq j) hh))
      rw [macroKernel, scaledBump_zero hR (by simpa only [dist_eq_norm] using hd.le),
        scaledBump_zero hR (by simpa only [dist_eq_norm] using hd'.le), sub_self, abs_zero,
        macroKernelError, ite_eq_right h]
  have hh := abs_le.mp hc
  constructor
  · exact max_le (scaledBump_nonneg hR _) (by linarith)
  · unfold macroKernelUpper
    linarith

end RadialTransition

end

end OAI
