import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Profiles
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Affine

namespace OAI

/-! Local two-dimensional Hamiltonian pulses for the stationary-forcing
construction. The fields act on the actual plane, including throughout their
cutoff collars. -/

noncomputable section

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

def basis (j : Fin 2) : Plane := Pi.single j 1

def spatialD (j : Fin 2) (H : Plane → ℝ) (x : Plane) : ℝ :=
  fderiv ℝ H x (basis j)

def field (H : Plane → ℝ) (x : Plane) : Plane :=
  letI := ShearFlows.neZeroTwo
  spatialD 1 H x • basis 0 - spatialD 0 H x • basis 1

def divergence (V : Plane → Plane) (x : Plane) : ℝ :=
  ∑ j : Fin 2, spatialD j (fun y => V y j) x

@[simp] theorem basis_apply (i j : Fin 2) : basis i j = if j = i then 1 else 0 := by
  simp [basis, Pi.single_apply]

theorem spatialD_smooth (j : Fin 2) {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (spatialD j H) :=
  (hH.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialD_comm (i j : Fin 2) {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) :
    spatialD i (spatialD j H) = spatialD j (spatialD i H) := by
  funext x
  have hd := (hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have he (a b : Fin 2) : spatialD a (spatialD b H) x =
      fderiv ℝ (fderiv ℝ H) x (basis a) (basis b) := by
    unfold spatialD
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [he, he]
  exact hH.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _

theorem field_smooth {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (field H) :=
  ((spatialD_smooth 1 hH).smul contDiff_const).sub
    ((spatialD_smooth 0 hH).smul contDiff_const)

theorem field_tsupport (H : Plane → ℝ) : tsupport (field H) ⊆ tsupport H := by
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact (tsupport_smul_subset_left _ _).trans (tsupport_fderiv_apply_subset ℝ (basis 1))
  · exact (tsupport_smul_subset_left _ _).trans (tsupport_fderiv_apply_subset ℝ (basis 0))

theorem field_compactSupport {H : Plane → ℝ} (hH : HasCompactSupport H) :
    HasCompactSupport (field H) :=
  hH.of_isClosed_subset (isClosed_tsupport _) (field_tsupport H)

theorem field_divergence {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H) (x : Plane) :
    divergence (field H) x = 0 := by
  have h₀ : (fun y => field H y 0) = spatialD 1 H := by
    funext y
    simp [field]
  have h₁ : (fun y => field H y 1) = fun y => -spatialD 0 H y := by
    funext y
    simp [field]
  rw [divergence, Fin.sum_univ_two, h₀, h₁]
  have hn : spatialD 1 (fun y => -spatialD 0 H y) x = -spatialD 1 (spatialD 0 H) x := by
    change (fderiv ℝ (-spatialD 0 H) x) (basis 1) =
      -(fderiv ℝ (spatialD 0 H) x) (basis 1)
    rw [fderiv_neg]
    simp
  rw [hn, spatialD_comm 0 1 hH]
  ring

/-- Every compactly supported smooth Hamiltonian has zero average velocity. -/
theorem spatialD_integral_eq_zero {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (j : Fin 2) : ∫ x, spatialD j H x = 0 := by
  have hD : Integrable (spatialD j H) :=
    (spatialD_smooth j hH).continuous.integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis j))
  have hI : Integrable H := hH.continuous.integrable_of_hasCompactSupport hc
  change Integrable (fun x : Plane => fderiv ℝ H x (basis j)) at hD
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Plane)) (f := fun _ : Plane => (1 : ℝ)) (g := H) (v := basis j)
    (by simp)
    (by simpa only [one_mul] using hD)
    (by simpa only [one_mul] using hI)
    (fun _ _ => differentiableAt_const 1)
    (fun x _ => hH.differentiable (by simp) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul,
    integral_zero, neg_zero, spatialD] using hi

theorem field_integral_eq_zero {H : Plane → ℝ} (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) : ∫ x, field H x = 0 := by
  have hD (j : Fin 2) : Integrable (spatialD j H) :=
    (spatialD_smooth j hH).continuous.integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis j))
  simp only [field, integral_sub ((hD 1).smul_const _) ((hD 0).smul_const _),
    integral_smul_const, spatialD_integral_eq_zero hH hc, zero_smul, sub_self]

theorem field_congr_of_eventuallyEq {H G : Plane → ℝ} {x : Plane}
    (h : H =ᶠ[𝓝 x] G) : field H x = field G x := by
  unfold field spatialD
  rw [h.fderiv_eq]

theorem field_cutoff_plateau (G χ : Plane → ℝ) {x : Plane}
    (hχ : χ =ᶠ[𝓝 x] fun _ => 1) :
    field (fun y => χ y * G y) x = field G x := by
  apply field_congr_of_eventuallyEq
  filter_upwards [hχ] with y hy
  simp [hy]

def translationPotential (v : Plane) (x : Plane) : ℝ :=
  letI := ShearFlows.neZeroTwo
  v 0 * x 1 - v 1 * x 0

theorem translationPotential_smooth (v : Plane) : ContDiff ℝ ∞ (translationPotential v) := by
  unfold translationPotential
  fun_prop

theorem field_translation (v : Plane) (x : Plane) : field (translationPotential v) x = v := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 1 x).const_mul (v 0)).sub
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 x).const_mul (v 1))
  change HasFDerivAt (translationPotential v) _ x at hd
  funext j
  fin_cases j <;> simp [field, spatialD, hd.fderiv, basis]

def translationPath (θ : ℝ → ℝ) (v w : Plane) (t : ℝ) : Plane := w + θ t • v

theorem translationPath_hasDerivAt {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (v w : Plane) :
    HasDerivAt (translationPath θ v w) (θ' • v) t := by
  exact (hθ.smul_const v).const_add w

theorem translationPath_cutoff_ode {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (v w : Plane) (χ : Plane → ℝ)
    (hχ : χ =ᶠ[𝓝 (translationPath θ v w t)] fun _ => 1) :
    HasDerivAt (translationPath θ v w)
      (θ' • field (fun x => χ x * translationPotential v x) (translationPath θ v w t)) t := by
  rw [field_cutoff_plateau _ _ hχ, field_translation]
  exact translationPath_hasDerivAt hθ v w

theorem translationPath_endpoints {θ : ℝ → ℝ} {a b : ℝ}
    (ha : θ a = 0) (hb : θ b = 1) (v w : Plane) :
    translationPath θ v w a = w ∧ translationPath θ v w b = w + v := by
  simp [translationPath, ha, hb]

/-- Polynomial Hamiltonians for the elementary shears. The coefficients are
rational whenever the instruction and parking point are rational. -/
def horizontalPotential (c : Plane) (a : ℝ) (x : Plane) : ℝ :=
  letI := ShearFlows.neZeroTwo
  letI := ShearFlows.twoAtLeastTwo
  (a / 2) * (x 1 - c 1) ^ 2

def verticalPotential (c : Plane) (a : ℝ) (x : Plane) : ℝ :=
  letI := ShearFlows.neZeroTwo
  letI := ShearFlows.twoAtLeastTwo
  show ℝ from -(a / 2) * (x 0 - c 0) ^ 2

theorem horizontalPotential_smooth (c : Plane) (a : ℝ) :
    ContDiff ℝ ∞ (horizontalPotential c a) := by
  unfold horizontalPotential
  fun_prop

theorem verticalPotential_smooth (c : Plane) (a : ℝ) :
    ContDiff ℝ ∞ (verticalPotential c a) := by
  unfold verticalPotential
  fun_prop

theorem field_horizontal (c : Plane) (a : ℝ) (x : Plane) :
    field (horizontalPotential c a) x = ![a * (x 1 - c 1), 0] := by
  have hd := (((hasFDerivAt_apply (𝕜 := ℝ) 1 x).sub_const (c 1)).pow 2).const_mul (a / 2)
  change HasFDerivAt (horizontalPotential c a) _ x at hd
  funext j
  fin_cases j <;>
    simp [field, spatialD, hd.fderiv, basis]; ring

theorem field_vertical (c : Plane) (a : ℝ) (x : Plane) :
    field (verticalPotential c a) x = ![0, a * (x 0 - c 0)] := by
  have hd := (((hasFDerivAt_apply (𝕜 := ℝ) 0 x).sub_const (c 0)).pow 2).const_mul (-(a / 2))
  change HasFDerivAt (verticalPotential c a) _ x at hd
  funext j
  fin_cases j <;>
    simp [field, spatialD, hd.fderiv, basis]; ring

def horizontalPath (θ : ℝ → ℝ) (a : ℝ) (c v : Plane) (t : ℝ) : Plane :=
  c + shearX (θ t * a) v

def verticalPath (θ : ℝ → ℝ) (a : ℝ) (c v : Plane) (t : ℝ) : Plane :=
  c + shearY (θ t * a) v

theorem horizontalPath_hasDerivAt {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (a : ℝ) (c v : Plane) :
    HasDerivAt (horizontalPath θ a c v)
      (θ' • field (horizontalPotential c a) (horizontalPath θ a c v t)) t := by
  rw [field_horizontal]
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · have h := ((hθ.mul_const a).mul_const (v 1)).const_add (v 0) |>.const_add (c 0)
    convert h using 1 <;>
      simp [horizontalPath, shearX, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · simpa [horizontalPath, shearX] using hasDerivAt_const t (c 1 + v 1)

theorem verticalPath_hasDerivAt {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (a : ℝ) (c v : Plane) :
    HasDerivAt (verticalPath θ a c v)
      (θ' • field (verticalPotential c a) (verticalPath θ a c v t)) t := by
  rw [field_vertical]
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · simpa [verticalPath, shearY] using hasDerivAt_const t (c 0 + v 0)
  · have h := ((hθ.mul_const a).mul_const (v 0)).const_add (v 1) |>.const_add (c 1)
    convert h using 1 <;>
      simp [verticalPath, shearY, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The four successive polynomial Hamiltonians have reciprocal-diagonal
composition. This avoids logarithms in a finite effective force program. -/
def fourShearPotential (μ : ℝ) (c : Plane) : Fin 4 → Plane → ℝ :=
  ![verticalPotential c (-μ), horizontalPotential c (μ⁻¹ - 1),
    verticalPotential c 1, horizontalPotential c (μ - 1)]

def fourShearPath (θ : ℝ → ℝ) (μ : ℝ) (c w : Plane) (k : Fin 4) (t : ℝ) : Plane :=
  c + partialShear μ k (θ t) (scalingEndpoints μ (w - c) k.castSucc)

theorem fourShearPotential_smooth (μ : ℝ) (c : Plane) (k : Fin 4) :
    ContDiff ℝ ∞ (fourShearPotential μ c k) := by
  fin_cases k <;>
    first | exact horizontalPotential_smooth _ _ | exact verticalPotential_smooth _ _

theorem fourShearPath_hasDerivAt {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (μ : ℝ) (c w : Plane) (k : Fin 4) :
    HasDerivAt (fourShearPath θ μ c w k)
      (θ' • field (fourShearPotential μ c k) (fourShearPath θ μ c w k t)) t := by
  fin_cases k
  · exact verticalPath_hasDerivAt hθ (-μ) c (scalingEndpoints μ (w - c) 0)
  · exact horizontalPath_hasDerivAt hθ (μ⁻¹ - 1) c (scalingEndpoints μ (w - c) 1)
  · let v := scalingEndpoints μ (w - c) 2
    change HasDerivAt (fun s => c + shearY (θ s) v)
      (θ' • field (verticalPotential c 1) (c + shearY (θ t) v)) t
    have h := verticalPath_hasDerivAt hθ 1 c v
    unfold verticalPath at h
    simpa only [mul_one] using h
  · exact horizontalPath_hasDerivAt hθ (μ - 1) c (scalingEndpoints μ (w - c) 3)

theorem fourShearPath_cutoff_ode {θ : ℝ → ℝ} {t θ' : ℝ}
    (hθ : HasDerivAt θ θ' t) (μ : ℝ) (c w : Plane) (k : Fin 4) (χ : Plane → ℝ)
    (hχ : χ =ᶠ[𝓝 (fourShearPath θ μ c w k t)] fun _ => 1) :
    HasDerivAt (fourShearPath θ μ c w k)
      (θ' • field (fun x => χ x * fourShearPotential μ c k x)
        (fourShearPath θ μ c w k t)) t := by
  rw [field_cutoff_plateau _ _ hχ]
  exact fourShearPath_hasDerivAt hθ μ c w k

theorem fourShearPath_endpoints {θ : ℝ → ℝ} {a b μ : ℝ}
    (ha : θ a = 0) (hb : θ b = 1) (hμ : μ ≠ 0) (c w : Plane) (k : Fin 4) :
    fourShearPath θ μ c w k a = c + scalingEndpoints μ (w - c) k.castSucc ∧
      fourShearPath θ μ c w k b = c + scalingEndpoints μ (w - c) k.succ := by
  simp only [fourShearPath, ha, hb, partial_shear_is_segment hμ, sub_zero,
    one_smul, zero_smul, add_zero, sub_self, zero_add, and_self]

theorem fourShearPath_final {θ : ℝ → ℝ} {b μ : ℝ}
    (hb : θ b = 1) (hμ : μ ≠ 0) (c w : Plane) :
    fourShearPath θ μ c w 3 b =
      ![c 0 + μ * (w 0 - c 0), c 1 + (w 1 - c 1) / μ] := by
  simp only [fourShearPath, hb, partial_shear_is_segment hμ, sub_self, zero_smul,
    one_smul, zero_add]
  funext j
  fin_cases j <;> simp [scalingEndpoints]

theorem fourShearPath_bound {θ : ℝ → ℝ} {t μ h : ℝ}
    (hθ : θ t ∈ Icc (0 : ℝ) 1) (hμ : 0 < μ) (hh : 0 ≤ h) (c w : Plane)
    (hx : |w 0 - c 0| ≤ h) (hy : |w 1 - c 1| ≤ h)
    (hμx : |μ * (w 0 - c 0)| ≤ h) (hyμ : |(w 1 - c 1) / μ| ≤ h) (k : Fin 4) :
    ‖fourShearPath θ μ c w k t - c‖ ≤ 2 * h := by
  have hbound := scaling_endpoints_bound hμ hh (w - c) hx hy hμx hyμ
  simp only [fourShearPath, add_sub_cancel_left, partial_shear_is_segment hμ.ne']
  exact norm_segment_le (hbound _) (hbound _) hθ

end ForcedComputation.PlanarHamiltonian

end

end OAI
