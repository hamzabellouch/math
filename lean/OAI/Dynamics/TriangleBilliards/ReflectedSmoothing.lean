import OAI.Dynamics.TriangleBilliards.SpatialSmoothing

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

namespace TriangularBilliards
open SpatialSmoothing

abbrev SmoothPhase := Phase × ZMod 2

/-- The direct Euclidean convolution term on one copy of the table. -/
def directS (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) : ℂ :=
  ∫ y in Q.table, kernel ε (x - y) • f ((y, v), b)

/-- The opposite-copy contribution after unfolding through wall `i`. -/
def reflectedS (Q : Triangle) (i : Fin 3) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) : ℂ :=
  ∫ y in Q.table, kernel ε (x - wallReflection Q i y) •
    f ((y, reflectedDirection Q i v), b + 1)

/-- A bounded global extension of the local disk mollifier. Away from
vertices, at most one reflected term can contribute. This fact is proved
geometrically instead of assuming a chart or an injectivity-radius bound. -/
def reflectedSmoothing (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ) : SmoothPhase → ℂ :=
  fun z => directS Q ε f z.2 z.1.2 z.1.1 +
    ∑ i : Fin 3, reflectedS Q i ε f z.2 z.1.2 z.1.1

lemma reflectedDirection_involutive (Q : Triangle) (i : Fin 3) (v : Circle) :
    reflectedDirection Q i (reflectedDirection Q i v) = v := by
  apply Subtype.ext
  exact reflect_involutive (Q.tangent_ne_zero i) v

lemma wallReflection_isometry (Q : Triangle) (i : Fin 3) : Isometry (wallReflection Q i) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, wallReflection_sub, reflect_norm (Q.tangent_ne_zero i), dist_eq_norm]

lemma kernel_wall_pair (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (wallReflection Q i x - wallReflection Q i y) = kernel ε (x - y) := by
  rw [wallReflection_sub]
  exact kernel_radial ε (reflect_norm (Q.tangent_ne_zero i) _)

lemma kernel_wall_transfer (Q : Triangle) (i : Fin 3) (ε : ℝ) (x y : ℂ) :
    kernel ε (wallReflection Q i x - y) = kernel ε (x - wallReflection Q i y) := by
  have h := kernel_wall_pair Q i ε x (wallReflection Q i y)
  rwa [wallReflection_involutive] at h

lemma seamS_equivariant (Q : Triangle) (i : Fin 3) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) (x : ℂ) :
    directS Q ε f (b + 1) (reflectedDirection Q i v) (wallReflection Q i x) +
      reflectedS Q i ε f (b + 1) (reflectedDirection Q i v) (wallReflection Q i x) =
    directS Q ε f b v x + reflectedS Q i ε f b v x := by
  simp only [directS, reflectedS, kernel_wall_transfer, wallReflection_involutive,
    reflectedDirection_involutive]
  have hb : (b + 1) + 1 = b := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  rw [hb, add_comm]

namespace Triangle

def coordCLM (Q : Triangle) (i : Fin 3) : ℂ →L[ℝ] ℝ :=
  (Q.basis.coord i).linear.toContinuousLinearMap

lemma coord_sub (Q : Triangle) (i : Fin 3) (x y : ℂ) :
    Q.basis.coord i x - Q.basis.coord i y = Q.coordCLM i (x - y) := by
  exact ((Q.basis.coord i).linearMap_vsub x y).symm

def coordinateBound (Q : Triangle) : ℝ := ∑ i, ‖Q.coordCLM i‖

lemma coordinateBound_nonneg (Q : Triangle) : 0 ≤ Q.coordinateBound :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma coord_norm_le (Q : Triangle) (i : Fin 3) (x y : ℂ) :
    |Q.basis.coord i x - Q.basis.coord i y| ≤ Q.coordinateBound * ‖x - y‖ := by
  rw [Q.coord_sub, ← Real.norm_eq_abs]
  apply (Q.coordCLM i).le_opNorm _ |>.trans
  gcongr
  exact Finset.single_le_sum (fun j _ => norm_nonneg (Q.coordCLM j)) (Finset.mem_univ i)

lemma coord_wallReflection (Q : Triangle) (i : Fin 3) (x : ℂ) :
    Q.basis.coord (i + 2) (wallReflection Q i x) = -Q.basis.coord (i + 2) x := by
  have hv : Q.basis.coord (i + 2) (Q.vertex i) = 0 := by
    exact Q.basis.coord_apply (i + 2) i |>.trans (ite_eq_right (by decide +revert))
  have h₁ := Q.coord_shift (i + 2) (Q.vertex i) (reflect (Q.tangent i) (x - Q.vertex i)) 1
  have h₂ := Q.coord_shift (i + 2) (Q.vertex i) (x - Q.vertex i) 1
  rw [one_smul, hv, one_mul, Q.slope_reflect] at h₁
  rw [one_smul, add_sub_cancel, hv, one_mul, zero_add] at h₂
  change Q.basis.coord (i + 2) (Q.vertex i + reflect (Q.tangent i) (x - Q.vertex i)) = _
  linarith

lemma coord_small_of_reflected_near (Q : Triangle) (i : Fin 3) {x y : ℂ} {ε : ℝ}
    (hy : y ∈ Q.table) (hxy : ‖x - wallReflection Q i y‖ ≤ ε) :
    Q.basis.coord (i + 2) x ≤ Q.coordinateBound * ε := by
  have h := Q.coord_norm_le (i + 2) x (wallReflection Q i y)
  rw [Q.coord_wallReflection] at h
  have hp := ((Q.table_iff_coords y).mp hy (i + 2)).le
  have ha := le_abs_self (Q.basis.coord (i + 2) x - -Q.basis.coord (i + 2) y)
  have hm := mul_le_mul_of_nonneg_left hxy Q.coordinateBound_nonneg
  linarith

end Triangle

lemma norm_decompose_sq (e : ℂ) (a b : ℝ) :
    ‖a • e + b • (Complex.I * e)‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖e‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma reflect_distance_le {e : ℂ} (he : e ≠ 0) (l : ℂ →ₗ[ℝ] ℝ)
    (hl : l e = 0) (hlI : l (Complex.I * e) ≠ 0) {x y : ℂ}
    (hxy : 0 ≤ l x * l y) : ‖x - y‖ ≤ ‖x - reflect e y‖ := by
  obtain ⟨a, b, rfl⟩ := complex_decompose_tangent he x
  obtain ⟨c, d, rfl⟩ := complex_decompose_tangent he y
  simp only [map_add, map_smul, smul_eq_mul, hl, mul_zero, zero_add] at hxy
  have hbd : 0 ≤ b * d := by
    nlinarith [sq_pos_of_ne_zero hlI]
  rw [reflect_add, reflect_real_smul, reflect_real_smul, reflect_tangent he, reflect_normal he]
  have hsub : a • e + b • (Complex.I * e) - (c • e + d • (Complex.I * e)) =
      (a - c) • e + (b - d) • (Complex.I * e) := by module
  have href : a • e + b • (Complex.I * e) - (c • e + d • -(Complex.I * e)) =
      (a - c) • e + (b + d) • (Complex.I * e) := by module
  rw [hsub, href]
  have hpos : 0 ≤ ‖e‖ ^ 2 := sq_nonneg ‖e‖
  have hn₁ := norm_decompose_sq e (a - c) (b - d)
  have hn₂ := norm_decompose_sq e (a - c) (b + d)
  nlinarith [norm_nonneg ((a - c) • e + (b - d) • (Complex.I * e)),
    norm_nonneg ((a - c) • e + (b + d) • (Complex.I * e)), mul_nonneg hbd hpos]

namespace Triangle

lemma slope_normal_ne_zero (Q : Triangle) (i : Fin 3) :
    Q.slope (i + 2) (Complex.I * Q.tangent i) ≠ 0 := by
  intro hz
  have hall (v : ℂ) : Q.slope (i + 2) v = 0 := by
    obtain ⟨a, b, rfl⟩ := complex_decompose_tangent (Q.tangent_ne_zero i) v
    change (Q.basis.coord (i + 2)).linear _ = 0
    rw [map_add, map_smul, map_smul]
    change a * Q.slope (i + 2) (Q.tangent i) +
      b * Q.slope (i + 2) (Complex.I * Q.tangent i) = 0
    rw [Q.slope_tangent_zero, hz, mul_zero, mul_zero, add_zero]
  have h := Q.coord_sub (i + 2) (Q.vertex (i + 2)) (Q.vertex i)
  change Q.basis.coord (i + 2) (Q.basis (i + 2)) -
    Q.basis.coord (i + 2) (Q.basis i) = Q.slope (i + 2) _ at h
  simp only [Q.basis.coord_apply, ite_eq_right (show i + 2 ≠ i by fin_cases i <;> decide),
    hall, sub_zero] at h
  exact one_ne_zero h

/-- Reflection through a supporting line can only increase the distance
between two points in the closed table. This also controls tip clearance
without any injectivity-radius assumption. -/
lemma dist_le_reflected_dist (Q : Triangle) (i : Fin 3) {x y : ℂ}
    (hx : x ∈ Q.table) (hy : y ∈ Q.table) :
    ‖x - y‖ ≤ ‖x - wallReflection Q i y‖ := by
  have hv : Q.basis.coord (i + 2) (Q.vertex i) = 0 :=
    Q.basis.coord_apply (i + 2) i |>.trans (ite_eq_right (by decide +revert))
  have he (z : ℂ) : (Q.basis.coord (i + 2)).linear (z - Q.vertex i) =
      Q.basis.coord (i + 2) z := by
    have h := Q.coord_sub (i + 2) z (Q.vertex i)
    rw [hv, sub_zero] at h
    exact h.symm
  have h := reflect_distance_le (Q.tangent_ne_zero i)
    (Q.basis.coord (i + 2)).linear (Q.slope_tangent_zero i) (Q.slope_normal_ne_zero i)
    (x := x - Q.vertex i) (y := y - Q.vertex i) (by
      rw [he, he]
      exact mul_nonneg ((Q.table_iff_coords x).mp hx _).le ((Q.table_iff_coords y).mp hy _).le)
  rw [sub_sub_sub_cancel_right] at h
  have hr : x - Q.vertex i - reflect (Q.tangent i) (y - Q.vertex i) =
      x - wallReflection Q i y := by unfold wallReflection; abel
  rwa [hr] at h

/-- Exact distance to the three cone tips. -/
def clearance (Q : Triangle) (x : ℂ) : ℝ := Metric.infDist x (range Q.vertex)

lemma clearance_nonneg (Q : Triangle) (x : ℂ) : 0 ≤ Q.clearance x :=
  Metric.infDist_nonneg

lemma clearance_lipschitz (Q : Triangle) : LipschitzWith 1 Q.clearance :=
  Metric.lipschitz_infDist_pt (range Q.vertex)

lemma clearance_le_add (Q : Triangle) (x y : ℂ) :
    Q.clearance y ≤ Q.clearance x + ‖x - y‖ := by
  have h := Q.clearance_lipschitz.dist_le_mul y x
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] at h
  rw [norm_sub_rev y x] at h
  have hs := le_abs_self (Q.clearance y - Q.clearance x)
  linarith

end Triangle

def SpatiallyZero (Q : Triangle) (R : ℝ) (f : SmoothPhase → ℂ) : Prop :=
  ∀ y ∈ Q.table, Q.clearance y < R → ∀ v b, f ((y, v), b) = 0

lemma directS_zero_near_tips (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) (b : ZMod 2) (v : Circle)
    {x : ℂ} (hx : Q.clearance x + ε ≤ R) : directS Q ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  by_cases hk : kernel ε (x - y) = 0
  · simp only [hk, zero_smul, Pi.zero_apply]
  · have hd : ‖x - y‖ < ε := by
      have hmem : x - y ∈ support (kernel ε) := hk
      rwa [kernel_support hε, mem_ball_zero_iff] at hmem
    have hr := Q.clearance_le_add x y
    have he := hf y hy (by linarith) v b
    simp only [he, smul_zero, Pi.zero_apply]

lemma reflectedS_zero_near_tips (Q : Triangle) (i : Fin 3) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) (b : ZMod 2) (v : Circle)
    {x : ℂ} (hx : x ∈ Q.table) (hr : Q.clearance x + ε ≤ R) :
    reflectedS Q i ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  by_cases hk : kernel ε (x - wallReflection Q i y) = 0
  · simp only [hk, zero_smul, Pi.zero_apply]
  · have hd : ‖x - wallReflection Q i y‖ < ε := by
      have hmem : x - wallReflection Q i y ∈ support (kernel ε) := hk
      rwa [kernel_support hε, mem_ball_zero_iff] at hmem
    have hg := Q.dist_le_reflected_dist i hx hy
    have hr' := Q.clearance_le_add x y
    have he := hf y hy (by linarith) (reflectedDirection Q i v) (b + 1)
    simp only [he, smul_zero, Pi.zero_apply]

lemma reflectedSmoothing_zero_near_tips (Q : Triangle) {ε R : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} (hf : SpatiallyZero Q R f) {z : SmoothPhase}
    (hx : z.1.1 ∈ Q.table) (hr : Q.clearance z.1.1 + ε ≤ R) :
    reflectedSmoothing Q ε f z = 0 := by
  rw [reflectedSmoothing, directS_zero_near_tips Q hε hf _ _ hr]
  simp only [reflectedS_zero_near_tips Q _ hε hf _ _ hx hr, Finset.sum_const_zero, add_zero]

namespace Triangle

def diameterBound (Q : Triangle) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ‖Q.vertex i - Q.vertex j‖

lemma diameterBound_nonneg (Q : Triangle) : 0 ≤ Q.diameterBound :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma vertex_dist_le_diameterBound (Q : Triangle) (i j : Fin 3) :
    ‖Q.vertex i - Q.vertex j‖ ≤ Q.diameterBound := by
  apply (Finset.single_le_sum (fun k _ => norm_nonneg (Q.vertex i - Q.vertex k))
    (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg
    (fun l _ => norm_nonneg (Q.vertex k - Q.vertex l))) (Finset.mem_univ i)

lemma reconstruct_difference (Q : Triangle) (x : ℂ) (k : Fin 3) :
    x - Q.vertex k = ∑ j : Fin 3, Q.basis.coord j x • (Q.vertex j - Q.vertex k) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    Q.basis.sum_coord_apply_eq_one, one_smul]
  have h := Q.basis.linear_combination_coord_eq_self x
  change ∑ i, Q.basis.coord i x • Q.vertex i = x at h
  rw [h]

lemma clearance_of_coords_small_nonneg (Q : Triangle) {x : ℂ}
    (hx : ∀ j, 0 ≤ Q.basis.coord j x)
    (k : Fin 3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ i, i ≠ k → Q.basis.coord i x ≤ δ) :
    Q.clearance x ≤ 3 * Q.diameterBound * δ := by
  calc
    Q.clearance x ≤ dist x (Q.vertex k) :=
      Metric.infDist_le_dist_of_mem (mem_range_self k)
    _ = ‖∑ j : Fin 3, Q.basis.coord j x • (Q.vertex j - Q.vertex k)‖ := by
      rw [dist_eq_norm, Q.reconstruct_difference]
    _ ≤ ∑ j : Fin 3, ‖Q.basis.coord j x • (Q.vertex j - Q.vertex k)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, δ * Q.diameterBound := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = k
      · simp only [hj, sub_self, smul_zero, norm_zero]
        exact mul_nonneg hδ Q.diameterBound_nonneg
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx j)]
        exact mul_le_mul (hc j hj) (Q.vertex_dist_le_diameterBound j k)
          (norm_nonneg _) hδ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma clearance_of_coords_small (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table)
    (k : Fin 3) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ i, i ≠ k → Q.basis.coord i x ≤ δ) :
    Q.clearance x ≤ 3 * Q.diameterBound * δ :=
  Q.clearance_of_coords_small_nonneg (fun j => ((Q.table_iff_coords x).mp hx j).le) k hδ hc

/-- A concrete fixed safety factor depending only on the triangle. -/
def safetyFactor (Q : Triangle) : ℝ := 3 * Q.diameterBound * Q.coordinateBound + 1

lemma safetyFactor_pos (Q : Triangle) : 0 < Q.safetyFactor := by
  unfold safetyFactor
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) Q.diameterBound_nonneg)
    Q.coordinateBound_nonneg
  linarith

lemma unique_nearby_wall (Q : Triangle) {x : ℂ} (hx : x ∈ Q.table) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance x) {i j : Fin 3}
    (hi : ∃ y ∈ Q.table, ‖x - wallReflection Q i y‖ ≤ ε)
    (hj : ∃ y ∈ Q.table, ‖x - wallReflection Q j y‖ ≤ ε) : i = j := by
  by_contra hij
  obtain ⟨y, hy, hxy⟩ := hi
  obtain ⟨z, hz, hxz⟩ := hj
  have hci := Q.coord_small_of_reflected_near i hy hxy
  have hcj := Q.coord_small_of_reflected_near j hz hxz
  let k : Fin 3 := -((i + 2) + (j + 2))
  have hfin : ∀ i j l : Fin 3, i ≠ j →
      l ≠ -((i + 2) + (j + 2)) → l = i + 2 ∨ l = j + 2 := by decide
  have hcover (l : Fin 3) (hl : l ≠ k) : l = i + 2 ∨ l = j + 2 :=
    hfin i j l hij hl
  have hh := Q.clearance_of_coords_small hx k
    (mul_nonneg Q.coordinateBound_nonneg hε.le) (fun l hl => by
      rcases hcover l hl with h | h
      · rwa [h]
      · rwa [h])
  unfold safetyFactor at hsafe
  nlinarith

end Triangle

/-- Zero extension of a spatial slice; no value at a seam is used. -/
def spatialSlice (Q : Triangle) (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) : ℂ → ℂ :=
  Q.table.indicator (fun y => f ((y, v), b))

def scalarKernelMap : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

lemma directS_eq_convolution (Q : Triangle) (ε : ℝ) (f : SmoothPhase → ℂ)
    (b : ZMod 2) (v : Circle) :
    directS Q ε f b v = convolution (spatialSlice Q f b v) (kernel ε)
      scalarKernelMap volume := by
  funext x
  rw [convolution_def]
  change (∫ y in Q.table, kernel ε (x - y) • f ((y, v), b)) =
    ∫ y, kernel ε (x - y) • Q.table.indicator (fun z => f ((z, v), b)) y
  rw [← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table <;> simp [indicator_of_mem, indicator_of_notMem, hy]

lemma directS_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table) :
    ContDiff ℝ ∞ (directS Q ε f b v) := by
  rw [directS_eq_convolution]
  apply (kernel_hasCompactSupport hε).contDiff_convolution_right scalarKernelMap
  · exact ((integrable_indicator_iff Q.measurableSet_table).mpr hf).locallyIntegrable
  · exact kernel_contDiff ε

lemma reflectedS_eq_directS (Q : Triangle) (i : Fin 3) (ε : ℝ)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) :
    reflectedS Q i ε f b v =
      directS Q ε f (b + 1) (reflectedDirection Q i v) ∘ wallReflection Q i := by
  funext x
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp only [kernel_wall_transfer]

lemma wallReflection_contDiff (Q : Triangle) (i : Fin 3) :
    ContDiff ℝ ∞ (wallReflection Q i) := by
  change ContDiff ℝ ∞ (fun x => Q.vertex i +
    reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i) (x - Q.vertex i))
  exact contDiff_const.add ((reflectIsometry (Q.tangent i) (Q.tangent_ne_zero i)).contDiff.comp
    (contDiff_id.sub contDiff_const))

lemma reflectedS_contDiff (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, reflectedDirection Q i v), b + 1)) Q.table) :
    ContDiff ℝ ∞ (reflectedS Q i ε f b v) := by
  rw [reflectedS_eq_directS]
  exact (directS_contDiff Q hε hf).comp (wallReflection_contDiff Q i)

/-- The genuine kernel construction is spatially smooth on every integrable
angular slice. No angular regularization, differentiability or boundedness of
`f` is required. -/
lemma reflectedSmoothing_contDiff (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table)
    (hfr : ∀ i, IntegrableOn
      (fun y => f ((y, reflectedDirection Q i v), b + 1)) Q.table) :
    ContDiff ℝ ∞ (fun x => reflectedSmoothing Q ε f ((x, v), b)) := by
  exact (directS_contDiff Q hε hf).add
    (ContDiff.sum fun i _ => reflectedS_contDiff Q i hε (hfr i))

lemma reflectedS_zero_of_coord (Q : Triangle) (i : Fin 3) {ε : ℝ} (hε : 0 < ε)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) {x : ℂ}
    (hx : Q.coordinateBound * ε < Q.basis.coord (i + 2) x) :
    reflectedS Q i ε f b v x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem Q.measurableSet_table] with y hy
  have hz : kernel ε (x - wallReflection Q i y) = 0 := by
    by_contra hn
    have hd : ‖x - wallReflection Q i y‖ < ε := by
      have hm : x - wallReflection Q i y ∈ support (kernel ε) := hn
      rwa [kernel_support hε, mem_ball_zero_iff] at hm
    exact (not_le_of_gt hx) (Q.coord_small_of_reflected_near i hy hd.le)
  simp only [hz, zero_smul, Pi.zero_apply]

lemma side_other_coord_large (Q : Triangle) {i j : Fin 3} {x : ℂ}
    (hx : x ∈ Q.side i) (hji : j ≠ i) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance x) :
    Q.coordinateBound * ε < Q.basis.coord (j + 2) x := by
  by_contra hn
  have hj := le_of_not_gt hn
  have hi : Q.basis.coord (i + 2) x = 0 := (Q.side_coord_zero_iff hx _).mpr rfl
  let k : Fin 3 := -((i + 2) + (j + 2))
  have hfin : ∀ i j l : Fin 3, i ≠ j →
      l ≠ -((i + 2) + (j + 2)) → l = i + 2 ∨ l = j + 2 := by decide
  have hp := mul_nonneg Q.coordinateBound_nonneg hε.le
  have hb := Q.clearance_of_coords_small_nonneg (Q.side_coords_nonneg hx) k hp (fun l hl => by
    rcases hfin i j l hji.symm hl with he | he
    · rw [he, hi]; exact hp
    · rwa [he])
  unfold Triangle.safetyFactor at hsafe
  nlinarith

/-- Near every safe open seam, the full finite kernel is exactly its
single unfolded two-sheet chart kernel. The assertion holds on a genuine
open neighborhood, so all spatial derivatives also glue. -/
lemma reflectedSmoothing_seam_germ (Q : Triangle) {i : Fin 3} {q : ℂ}
    (hq : q ∈ Q.side i) {ε : ℝ} (hε : 0 < ε)
    (hsafe : Q.safetyFactor * ε < Q.clearance q)
    (f : SmoothPhase → ℂ) (b : ZMod 2) (v : Circle) :
    ∀ᶠ x in nhds q,
      reflectedSmoothing Q ε f ((wallReflection Q i x, reflectedDirection Q i v), b + 1) =
        reflectedSmoothing Q ε f ((x, v), b) := by
  have hc (j : Fin 3) : Continuous (fun x => Q.basis.coord (j + 2) x) :=
    (Q.basis.coord (j + 2)).continuous_of_finiteDimensional
  have he (j : Fin 3) : ∀ᶠ x in nhds q, j ≠ i →
      Q.coordinateBound * ε < Q.basis.coord (j + 2) x ∧
      Q.coordinateBound * ε < Q.basis.coord (j + 2) (wallReflection Q i x) := by
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hh := side_other_coord_large Q hq hj hε hsafe
      have h₁ := (hc j).continuousAt.eventually (Ioi_mem_nhds hh)
      have hh' : Q.coordinateBound * ε < Q.basis.coord (j + 2) (wallReflection Q i q) := by
        rwa [wallReflection_fixed_side Q hq]
      have h₂ := ((hc j).comp (wallReflection_contDiff Q i).continuous).continuousAt
        (x := q) |>.eventually (Ioi_mem_nhds hh')
      filter_upwards [h₁, h₂] with x h₁ h₂ using fun _ => ⟨h₁, h₂⟩
  have hall := (Filter.eventually_all.mpr he)
  filter_upwards [hall] with x hx
  have hsum (b : ZMod 2) (v : Circle) {y : ℂ}
      (hy : ∀ j, j ≠ i → Q.coordinateBound * ε < Q.basis.coord (j + 2) y) :
      (∑ j : Fin 3, reflectedS Q j ε f b v y) = reflectedS Q i ε f b v y := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact reflectedS_zero_of_coord Q j hε f b v (hy j hj)
    · simp
  simp only [reflectedSmoothing, hsum b v (fun j hj => (hx j hj).1),
    hsum (b + 1) (reflectedDirection Q i v) (fun j hj => (hx j hj).2)]
  exact seamS_equivariant Q i ε f b v x

lemma directS_fderiv (Q : Triangle) {ε : ℝ} (hε : 0 < ε)
    {f : SmoothPhase → ℂ} {b : ZMod 2} {v : Circle}
    (hf : IntegrableOn (fun y => f ((y, v), b)) Q.table) (x : ℂ) :
    fderiv ℝ (directS Q ε f b v) x =
      ∫ y in Q.table, (fderiv ℝ (kernel ε) (x - y)).smulRight (f ((y, v), b)) := by
  rw [directS_eq_convolution]
  have hi : LocallyIntegrable (spatialSlice Q f b v) volume :=
    ((integrable_indicator_iff Q.measurableSet_table).mpr hf).locallyIntegrable
  rw [((kernel_hasCompactSupport hε).hasFDerivAt_convolution_right scalarKernelMap hi
    ((kernel_contDiff ε).of_le (by simp)) x).fderiv, convolution_def]
  rw [← integral_indicator Q.measurableSet_table]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ Q.table
    · simp only [spatialSlice, indicator_of_mem hy]
      rfl
    · simp only [spatialSlice, indicator_of_notMem hy, map_zero, zero_apply]

lemma kernel_lintegral {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x : ℂ, ENNReal.ofReal (kernel ε x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (kernel_integrable hε)
    (Filter.Eventually.of_forall (kernel_nonneg ε)), kernel_integral hε, ENNReal.ofReal_one]

lemma kernel_row_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal (kernel ε (x - y)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ y : ℂ, ENNReal.ofReal (kernel ε (x - y)) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = 1 := (lintegral_sub_left_eq_self (fun y : ℂ => ENNReal.ofReal (kernel ε y)) x).trans
      (kernel_lintegral hε)

lemma kernel_col_bound (Q : Triangle) {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal (kernel ε (x - y)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ x : ℂ, ENNReal.ofReal (kernel ε (x - y)) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = 1 := (lintegral_sub_right_eq_self (fun x : ℂ => ENNReal.ofReal (kernel ε x)) y).trans
      (kernel_lintegral hε)

lemma reflected_kernel_row_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫⁻ y in Q.table, ENNReal.ofReal (kernel ε (x - wallReflection Q i y)) ≤ 1 := by
  simp_rw [← kernel_wall_transfer]
  exact kernel_row_bound Q hε _

lemma reflected_kernel_col_bound (Q : Triangle) (i : Fin 3)
    {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    ∫⁻ x in Q.table, ENNReal.ofReal (kernel ε (x - wallReflection Q i y)) ≤ 1 :=
  kernel_col_bound Q hε _

end TriangularBilliards

end
end

end OAI
