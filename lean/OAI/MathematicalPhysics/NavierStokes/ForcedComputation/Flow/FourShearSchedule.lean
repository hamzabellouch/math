import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarHamiltonian

namespace OAI

/-! Four separated rational time slots give an actual smooth planar trajectory
for a reciprocal affine map. The global curve is polynomial in the four smooth
clocks, so no piecewise path or logarithmic coefficient is needed. -/

noncomputable section

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

def slotStart (k : Fin 4) : ℚ := (2 * (k.val : ℚ) + 1) / 10

def slotFinish (k : Fin 4) : ℚ := (2 * (k.val : ℚ) + 2) / 10

theorem slot_order (k : Fin 4) : slotStart k < slotFinish k := by
  dsimp [slotStart, slotFinish]
  linarith

def slotClock (k : Fin 4) : ℝ → ℝ := smoothRamp (slotStart k) (slotFinish k)

def slotPulse (k : Fin 4) : ℝ → ℝ := smoothPulse (slotStart k) (slotFinish k)

theorem slotClock_smooth (k : Fin 4) : ContDiff ℝ ∞ (slotClock k) :=
  smoothRamp_smooth _ _

theorem slotClock_hasDerivAt (k : Fin 4) (t : ℝ) :
    HasDerivAt (slotClock k) (slotPulse k t) t :=
  ((slotClock_smooth k).differentiable (by simp) t).hasDerivAt

def slotRegion (k : Fin 4) : Set ℝ :=
  (if k = 0 then univ else Ioi ((k.val : ℝ) / 5)) ∩
    (if k = 3 then univ else Iio ((2 * (k.val : ℝ) + 3) / 10))

theorem slotRegion_open (k : Fin 4) : IsOpen (slotRegion k) := by
  unfold slotRegion
  apply IsOpen.inter <;> split <;> first | exact isOpen_univ | exact isOpen_Ioi | exact isOpen_Iio

theorem exists_slotRegion (t : ℝ) : ∃ k : Fin 4, t ∈ slotRegion k := by
  by_cases h₀ : t < 3 / 10
  · exact ⟨0, by simpa [slotRegion] using h₀⟩
  by_cases h₁ : t < 5 / 10
  · refine ⟨1, ?_⟩
    norm_num [slotRegion]
    constructor <;> linarith
  by_cases h₂ : t < 7 / 10
  · refine ⟨2, ?_⟩
    norm_num [slotRegion]
    constructor <;> linarith
  · refine ⟨3, ?_⟩
    norm_num [slotRegion]
    linarith

theorem previous_finish_lt {j k : Fin 4} {t : ℝ}
    (hj : j < k) (ht : t ∈ slotRegion k) : (slotFinish j : ℝ) < t := by
  have hk : k ≠ 0 := by intro hk; subst k; exact (not_lt_of_ge (Fin.zero_le j)) hj
  have hlo : (k.val : ℝ) / 5 < t := by simpa [slotRegion, hk] using ht.1
  have hj' : (j.val : ℝ) + 1 ≤ (k.val : ℝ) := by exact_mod_cast (show j.val + 1 ≤ k.val from hj)
  dsimp [slotFinish]
  push_cast
  linarith

theorem lt_future_start {j k : Fin 4} {t : ℝ}
    (hj : k < j) (ht : t ∈ slotRegion k) : t < (slotStart j : ℝ) := by
  have hk : k ≠ 3 := by
    intro hk
    subst k
    have := j.isLt
    omega
  have hhi : t < (2 * (k.val : ℝ) + 3) / 10 := by
    simpa [slotRegion, hk] using ht.2
  have hj' : (k.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast (show k.val + 1 ≤ j.val from hj)
  dsimp [slotStart]
  push_cast
  linarith

theorem clock_previous {j k : Fin 4} {t : ℝ}
    (hj : j < k) (ht : t ∈ slotRegion k) :
    slotClock j t = 1 ∧ slotPulse j t = 0 := by
  have hord : (slotStart j : ℝ) < slotFinish j := by exact_mod_cast slot_order j
  exact ⟨smoothRamp_after hord (previous_finish_lt hj ht).le,
    smoothPulse_after hord (previous_finish_lt hj ht).le⟩

theorem clock_future {j k : Fin 4} {t : ℝ}
    (hj : k < j) (ht : t ∈ slotRegion k) :
    slotClock j t = 0 ∧ slotPulse j t = 0 := by
  have hord : (slotStart j : ℝ) < slotFinish j := by exact_mod_cast slot_order j
  exact ⟨smoothRamp_before hord (lt_future_start hj ht).le,
    smoothPulse_before hord (lt_future_start hj ht).le⟩

def route (μ : ℝ) (c w : Plane) (t : ℝ) : Plane :=
  c + shearX (slotClock 3 t * (μ - 1))
    (shearY (slotClock 2 t)
      (shearX (slotClock 1 t * (μ⁻¹ - 1))
        (shearY (slotClock 0 t * (-μ)) (w - c))))

theorem route_smooth (μ : ℝ) (c w : Plane) : ContDiff ℝ ∞ (route μ c w) := by
  have h₀ := slotClock_smooth 0
  have h₁ := slotClock_smooth 1
  have h₂ := slotClock_smooth 2
  have h₃ := slotClock_smooth 3
  unfold route shearX shearY
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp <;> fun_prop

theorem route_eq_stage {μ : ℝ} (hμ : μ ≠ 0) (c w : Plane)
    {k : Fin 4} {t : ℝ} (ht : t ∈ slotRegion k) :
    route μ c w t = fourShearPath (slotClock k) μ c w k t := by
  have hp (j : Fin 4) (hj : j < k) := (clock_previous hj ht).1
  have hf (j : Fin 4) (hj : k < j) := (clock_future hj ht).1
  fin_cases k
  · have h₁ := hf 1 (by decide)
    have h₂ := hf 2 (by decide)
    have h₃ := hf 3 (by decide)
    funext j
    fin_cases j <;> simp [route, fourShearPath, partialShear, scalingEndpoints,
      shearX, shearY, h₁, h₂, h₃]
  · have h₀ := hp 0 (by decide)
    have h₂ := hf 2 (by decide)
    have h₃ := hf 3 (by decide)
    funext j
    fin_cases j <;> simp [route, fourShearPath, partialShear, scalingEndpoints,
      shearX, shearY, h₀, h₂, h₃, sub_eq_add_neg]
  · have h₀ := hp 0 (by decide)
    have h₁ := hp 1 (by decide)
    have h₃ := hf 3 (by decide)
    funext j
    fin_cases j <;> simp [route, fourShearPath, partialShear, scalingEndpoints,
      shearX, shearY, h₀, h₁, h₃] <;> field_simp <;> ring
  · have h₀ := hp 0 (by decide)
    have h₁ := hp 1 (by decide)
    have h₂ := hp 2 (by decide)
    funext j
    fin_cases j <;> simp [route, fourShearPath, partialShear, scalingEndpoints,
      shearX, shearY, h₀, h₁, h₂] <;> field_simp <;> ring

theorem route_eq_stage_near {μ : ℝ} (hμ : μ ≠ 0) (c w : Plane)
    {k : Fin 4} {t : ℝ} (ht : t ∈ slotRegion k) :
    route μ c w =ᶠ[𝓝 t] fourShearPath (slotClock k) μ c w k :=
  Filter.eventually_of_mem ((slotRegion_open k).mem_nhds ht)
    (fun _ hs => route_eq_stage hμ c w hs)

def scheduledVelocity (μ : ℝ) (c : Plane) (χ : Plane → ℝ) (t : ℝ) (x : Plane) : Plane :=
  ∑ k : Fin 4, slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x

theorem scheduledVelocity_smooth (μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => scheduledVelocity μ c χ p.1 p.2) := by
  unfold scheduledVelocity
  apply ContDiff.sum
  intro k _
  exact ((smoothPulse_smooth (slotStart k) (slotFinish k)).comp contDiff_fst).smul
    ((field_smooth (hχ.mul (fourShearPotential_smooth μ c k))).comp contDiff_snd)

theorem scheduledVelocity_compactSupport (μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hc : HasCompactSupport χ) (t : ℝ) :
    HasCompactSupport (scheduledVelocity μ c χ t) := by
  apply HasCompactSupport.intro hc.isCompact
  intro x hx
  unfold scheduledVelocity
  apply Finset.sum_eq_zero
  intro k _
  have hs : tsupport (field (fun y => χ y * fourShearPotential μ c k y)) ⊆ tsupport χ :=
    (field_tsupport _).trans tsupport_mul_subset_left
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), smul_zero]

theorem scheduledVelocity_integral_eq_zero (μ : ℝ) (c : Plane) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (t : ℝ) :
    ∫ x, scheduledVelocity μ c χ t x = 0 := by
  have hH (k : Fin 4) : ContDiff ℝ ∞ (fun y => χ y * fourShearPotential μ c k y) :=
    hχ.mul (fourShearPotential_smooth μ c k)
  have hC (k : Fin 4) : HasCompactSupport (fun y => χ y * fourShearPotential μ c k y) :=
    hc.mul_right
  have hI (k : Fin 4) : Integrable (fun x =>
      slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x) := by
    have hs : Continuous (fun x : Plane =>
        slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x) :=
      (continuous_const (y := slotPulse k t)).smul (field_smooth (hH k)).continuous
    have hc' : HasCompactSupport (fun x : Plane =>
        slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x) :=
      (field_compactSupport (hC k)).smul_left (f := fun _ : Plane => slotPulse k t)
    exact hs.integrable_of_hasCompactSupport hc'
  change (∫ x, ∑ k : Fin 4,
    slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x) = 0
  rw [integral_finsetSum _ (fun k _ => hI k)]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_smul, field_integral_eq_zero (hH k) (hC k), smul_zero]

theorem scheduledVelocity_one_slot {μ : ℝ} {c : Plane} {χ : Plane → ℝ}
    {k : Fin 4} {t : ℝ} (ht : t ∈ slotRegion k) (x : Plane) :
    scheduledVelocity μ c χ t x =
      slotPulse k t • field (fun y => χ y * fourShearPotential μ c k y) x := by
  unfold scheduledVelocity
  apply Finset.sum_eq_single k
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hj | hj
    · simp only [(clock_previous hj ht).2, zero_smul]
    · simp only [(clock_future hj ht).2, zero_smul]
  · simp

theorem route_hasDerivAt {μ : ℝ} (hμ : μ ≠ 0) (c w : Plane) (χ : Plane → ℝ)
    (t : ℝ) (hχ : χ =ᶠ[𝓝 (route μ c w t)] fun _ => 1) :
    HasDerivAt (route μ c w) (scheduledVelocity μ c χ t (route μ c w t)) t := by
  obtain ⟨k, hk⟩ := exists_slotRegion t
  have he := route_eq_stage_near hμ c w hk
  have hev := he.eq_of_nhds
  rw [scheduledVelocity_one_slot hk, hev]
  have hd := fourShearPath_cutoff_ode (slotClock_hasDerivAt k t) μ c w k χ
    (by simpa only [← hev] using hχ)
  exact hd.congr_of_eventuallyEq he

theorem route_initial (μ : ℝ) (c w : Plane) : route μ c w 0 = w := by
  have hz (k : Fin 4) : slotClock k 0 = 0 := by
    apply smoothRamp_before
    · exact_mod_cast slot_order k
    · dsimp [slotStart]
      positivity
  funext j
  fin_cases j <;> simp [route, hz, shearX, shearY]

theorem route_final {μ : ℝ} (hμ : μ ≠ 0) (c w : Plane) :
    route μ c w 1 = ![c 0 + μ * (w 0 - c 0), c 1 + (w 1 - c 1) / μ] := by
  have ho (k : Fin 4) : slotClock k 1 = 1 := by
    apply smoothRamp_after
    · exact_mod_cast slot_order k
    · have hk : (k.val : ℚ) < 4 := by exact_mod_cast k.isLt
      dsimp [slotFinish]
      exact_mod_cast (show (2 * (k.val : ℚ) + 2) / 10 ≤ 1 by linarith)
  rw [route, ho, ho, ho, ho]
  simp only [one_mul]
  rw [four_shears hμ]
  funext j
  fin_cases j <;> rfl

theorem route_bound {μ h : ℝ} (hμ : 0 < μ) (hh : 0 ≤ h) (c w : Plane)
    (hx : |w 0 - c 0| ≤ h) (hy : |w 1 - c 1| ≤ h)
    (hμx : |μ * (w 0 - c 0)| ≤ h) (hyμ : |(w 1 - c 1) / μ| ≤ h)
    (t : ℝ) : ‖route μ c w t - c‖ ≤ 2 * h := by
  obtain ⟨k, hk⟩ := exists_slotRegion t
  rw [route_eq_stage hμ.ne' c w hk]
  exact fourShearPath_bound (smoothRamp_range _ _ _) hμ hh c w hx hy hμx hyμ k

end ForcedComputation.PlanarHamiltonian

end

end OAI
