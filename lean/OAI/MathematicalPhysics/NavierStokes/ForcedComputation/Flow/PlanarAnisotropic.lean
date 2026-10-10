import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FourShearSchedule

namespace OAI

/-! Anisotropic four-shear routes. Horizontal compression of the recorder
must persist throughout the scaling stage, so the parking columns remain
disjoint even when there are many instructions. All four coefficients are
rational functions of the input data. -/

noncomputable section

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

def diagonalScale (a b : ℝ) (x : Plane) : Plane := ![a * x 0, b * x 1]

def diagonalLinear (a b : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun := diagonalScale a b
  map_add' x y := by
    funext j
    fin_cases j <;> simp [diagonalScale, mul_add]
  map_smul' r x := by
    funext j
    fin_cases j <;> dsimp [diagonalScale] <;> ring

theorem diagonalScale_hasDerivAt {f : ℝ → Plane} {v : Plane} {t : ℝ}
    (hf : HasDerivAt f v t) (a b : ℝ) (c : Plane) :
    HasDerivAt (fun s => c + diagonalScale a b (f s)) (diagonalScale a b v) t := by
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · change HasDerivAt (fun s => c 0 + a * f s 0) (a * v 0) t
    exact (((hasDerivAt_pi.mp hf) 0).const_mul a).const_add (c 0)
  · change HasDerivAt (fun s => c 1 + b * f s 1) (b * v 1) t
    exact (((hasDerivAt_pi.mp hf) 1).const_mul b).const_add (c 1)

def anisotropicPotential (a b μ : ℝ) (c : Plane) : Fin 4 → Plane → ℝ :=
  ![verticalPotential c (-μ * b / a),
    horizontalPotential c ((μ⁻¹ - 1) * a / b),
    verticalPotential c (b / a),
    horizontalPotential c ((μ - 1) * a / b)]

theorem anisotropicPotential_smooth (a b μ : ℝ) (c : Plane) (k : Fin 4) :
    ContDiff ℝ ∞ (anisotropicPotential a b μ c k) := by
  fin_cases k <;>
    first | exact horizontalPotential_smooth _ _ | exact verticalPotential_smooth _ _

theorem field_anisotropicPotential {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (μ : ℝ) (c z : Plane) (k : Fin 4) :
    field (anisotropicPotential a b μ c k) (c + diagonalScale a b z) =
      diagonalScale a b (field (fourShearPotential μ 0 k) z) := by
  have hY (q : ℝ) :
      field (verticalPotential c (q * b / a)) (c + diagonalScale a b z) =
        diagonalScale a b (field (verticalPotential 0 q) z) := by
    simp only [field_vertical]
    funext j
    fin_cases j
    · simp [diagonalScale]
    · dsimp [diagonalScale]
      field_simp
      ring
  have hX (q : ℝ) :
      field (horizontalPotential c (q * a / b)) (c + diagonalScale a b z) =
        diagonalScale a b (field (horizontalPotential 0 q) z) := by
    simp only [field_horizontal]
    funext j
    fin_cases j
    · dsimp [diagonalScale]
      field_simp
      ring
    · simp [diagonalScale]
  fin_cases k
  · exact hY (-μ)
  · exact hX (μ⁻¹ - 1)
  · change field (verticalPotential c (b / a)) (c + diagonalScale a b z) =
      diagonalScale a b (field (verticalPotential 0 1) z)
    simpa only [one_mul] using hY 1
  · exact hX (μ - 1)

def normalizedOffset (a b : ℝ) (c w : Plane) : Plane :=
  ![(w 0 - c 0) / a, (w 1 - c 1) / b]

def anisotropicRoute (a b μ : ℝ) (c w : Plane) (t : ℝ) : Plane :=
  c + diagonalScale a b (route μ 0 (normalizedOffset a b c w) t)

theorem anisotropicRoute_smooth (a b μ : ℝ) (c w : Plane) :
    ContDiff ℝ ∞ (anisotropicRoute a b μ c w) := by
  have hs := route_smooth μ 0 (normalizedOffset a b c w)
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [anisotropicRoute, diagonalScale] <;> fun_prop

def anisotropicVelocity (a b μ : ℝ) (c : Plane) (χ : Plane → ℝ)
    (t : ℝ) (x : Plane) : Plane :=
  ∑ k : Fin 4, slotPulse k t •
    field (fun y => χ y * anisotropicPotential a b μ c k y) x

theorem anisotropicVelocity_smooth (a b μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => anisotropicVelocity a b μ c χ p.1 p.2) := by
  unfold anisotropicVelocity
  apply ContDiff.sum
  intro k _
  exact ((smoothPulse_smooth (slotStart k) (slotFinish k)).comp contDiff_fst).smul
    ((field_smooth (hχ.mul (anisotropicPotential_smooth a b μ c k))).comp contDiff_snd)

theorem anisotropicVelocity_compactSupport (a b μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hc : HasCompactSupport χ) (t : ℝ) :
    HasCompactSupport (anisotropicVelocity a b μ c χ t) := by
  apply HasCompactSupport.intro hc.isCompact
  intro x hx
  unfold anisotropicVelocity
  apply Finset.sum_eq_zero
  intro k _
  have hs : tsupport (field (fun y => χ y * anisotropicPotential a b μ c k y)) ⊆ tsupport χ :=
    (field_tsupport _).trans tsupport_mul_subset_left
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), smul_zero]

theorem anisotropicVelocity_integral_eq_zero (a b μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (t : ℝ) :
    ∫ x, anisotropicVelocity a b μ c χ t x = 0 := by
  have hH (k : Fin 4) :
      ContDiff ℝ ∞ (fun y => χ y * anisotropicPotential a b μ c k y) :=
    hχ.mul (anisotropicPotential_smooth a b μ c k)
  have hC (k : Fin 4) :
      HasCompactSupport (fun y => χ y * anisotropicPotential a b μ c k y) := hc.mul_right
  have hI (k : Fin 4) : Integrable (fun x =>
      slotPulse k t • field (fun y => χ y * anisotropicPotential a b μ c k y) x) := by
    have hs : Continuous (fun x : Plane =>
        slotPulse k t • field (fun y => χ y * anisotropicPotential a b μ c k y) x) :=
      (continuous_const (y := slotPulse k t)).smul (field_smooth (hH k)).continuous
    have hc' : HasCompactSupport (fun x : Plane =>
        slotPulse k t • field (fun y => χ y * anisotropicPotential a b μ c k y) x) :=
      (field_compactSupport (hC k)).smul_left (f := fun _ : Plane => slotPulse k t)
    exact hs.integrable_of_hasCompactSupport hc'
  change (∫ x, ∑ k : Fin 4,
    slotPulse k t • field (fun y => χ y * anisotropicPotential a b μ c k y) x) = 0
  rw [integral_finsetSum _ (fun k _ => hI k)]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_smul, field_integral_eq_zero (hH k) (hC k), smul_zero]

theorem anisotropicVelocity_scale {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (μ : ℝ) (c z : Plane) (t : ℝ) :
    anisotropicVelocity a b μ c (fun _ => 1) t (c + diagonalScale a b z) =
      diagonalScale a b (scheduledVelocity μ 0 (fun _ => 1) t z) := by
  change (∑ k : Fin 4, slotPulse k t •
    field (fun y => 1 * anisotropicPotential a b μ c k y) (c + diagonalScale a b z)) =
      diagonalLinear a b (∑ k : Fin 4,
        slotPulse k t • field (fun y => 1 * fourShearPotential μ 0 k y) z)
  simp only [one_mul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [field_anisotropicPotential ha hb]
  rfl

theorem anisotropicVelocity_plateau (a b μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    {x : Plane} (hχ : χ =ᶠ[𝓝 x] fun _ => 1) (t : ℝ) :
    anisotropicVelocity a b μ c χ t x =
      anisotropicVelocity a b μ c (fun _ => 1) t x := by
  apply Finset.sum_congr rfl
  intro k _
  rw [field_cutoff_plateau _ _ hχ]
  simp only [one_mul]

theorem anisotropicRoute_hasDerivAt {a b μ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hμ : μ ≠ 0) (c w : Plane) (χ : Plane → ℝ) (t : ℝ)
    (hχ : χ =ᶠ[𝓝 (anisotropicRoute a b μ c w t)] fun _ => 1) :
    HasDerivAt (anisotropicRoute a b μ c w)
      (anisotropicVelocity a b μ c χ t (anisotropicRoute a b μ c w t)) t := by
  rw [anisotropicVelocity_plateau a b μ c hχ]
  unfold anisotropicRoute
  rw [anisotropicVelocity_scale ha hb]
  exact diagonalScale_hasDerivAt
    (route_hasDerivAt hμ 0 (normalizedOffset a b c w) (fun _ => 1) t Filter.EventuallyEq.rfl)
    a b c

theorem anisotropicRoute_initial {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (μ : ℝ) (c w : Plane) : anisotropicRoute a b μ c w 0 = w := by
  rw [anisotropicRoute, route_initial]
  funext j
  fin_cases j
  · change c 0 + a * ((w 0 - c 0) / a) = w 0
    rw [mul_comm a, div_mul_cancel₀ _ ha, add_sub_cancel]
  · change c 1 + b * ((w 1 - c 1) / b) = w 1
    rw [mul_comm b, div_mul_cancel₀ _ hb, add_sub_cancel]

theorem anisotropicRoute_final {a b μ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hμ : μ ≠ 0) (c w : Plane) :
    anisotropicRoute a b μ c w 1 =
      ![c 0 + μ * (w 0 - c 0), c 1 + (w 1 - c 1) / μ] := by
  rw [anisotropicRoute, route_final hμ]
  funext j
  fin_cases j <;> simp [diagonalScale, normalizedOffset] <;> field_simp

theorem anisotropicRoute_bound {a b μ h : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hμ : 0 < μ) (hh : 0 ≤ h) (c w : Plane)
    (hx : |(w 0 - c 0) / a| ≤ h) (hy : |(w 1 - c 1) / b| ≤ h)
    (hμx : |μ * ((w 0 - c 0) / a)| ≤ h)
    (hyμ : |((w 1 - c 1) / b) / μ| ≤ h) (t : ℝ) :
    |anisotropicRoute a b μ c w t 0 - c 0| ≤ 2 * a * h ∧
      |anisotropicRoute a b μ c w t 1 - c 1| ≤ 2 * b * h := by
  have hr := route_bound hμ hh 0 (normalizedOffset a b c w)
    (by simpa [normalizedOffset] using hx)
    (by simpa [normalizedOffset] using hy)
    (by simpa [normalizedOffset] using hμx)
    (by simpa [normalizedOffset] using hyμ) t
  have hc (j : Fin 2) : |route μ 0 (normalizedOffset a b c w) t j| ≤ 2 * h := by
    have hh : |route μ 0 (normalizedOffset a b c w) t j| ≤
        ‖route μ 0 (normalizedOffset a b c w) t‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (route μ 0 (normalizedOffset a b c w) t) j
    exact hh.trans (by simpa using hr)
  constructor
  · simpa [anisotropicRoute, diagonalScale, abs_mul, abs_of_nonneg ha, mul_assoc,
      mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left (hc 0) ha
  · simpa [anisotropicRoute, diagonalScale, abs_mul, abs_of_nonneg hb, mul_assoc,
      mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left (hc 1) hb

end ForcedComputation.PlanarHamiltonian

end

end OAI
