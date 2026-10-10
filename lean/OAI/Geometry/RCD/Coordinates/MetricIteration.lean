import OAI.Geometry.RCD.Coordinates.FrozenInverseCosts
import OAI.Geometry.RCD.Coordinates.NormalizedJetStep
import OAI.Geometry.RCD.Coordinates.PointwiseMetricIteration

namespace OAI

/-!
# Finite analytic coordinate iteration

The maps are defined everywhere. Smoothness and metric estimates are
local statements on a fixed open set, derived from analytic field bounds.
-/

open Filter Set
open scoped Topology ContDiff BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual coordinate iteration, starting from the identity. -/
def metricIterate (v : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | i + 1 => fun x => metricIterate v i x +
      operatorInverseTranspose (fderiv ℝ (metricIterate v i) x) (v i x)

@[simp] theorem metricIterate_zero (v : ℕ → E → E) : metricIterate v 0 = id := rfl

@[simp] theorem metricIterate_succ (v : ℕ → E → E) (i : ℕ) :
    metricIterate v (i + 1) = fun x => metricIterate v i x +
      operatorInverseTranspose (fderiv ℝ (metricIterate v i) x) (v i x) := rfl

omit [CompleteSpace E] in
/-- Local smoothness is preserved by frozen normalization. -/
theorem contDiffAt_normalizedCoordinates {m : ℕ} {r : ℝ} (T : E ≃L[ℝ] E)
    (x : E) {h : E → E} (hh : ContDiffAt ℝ m h x) :
    ContDiffAt ℝ m (normalizedCoordinates r T x h) 0 := by
  have hh' : ContDiffAt ℝ m h (frozenSource r T x 0) := by
    simpa [frozenSource] using hh
  have hs : ContDiffAt ℝ m (frozenSource r T x) 0 := by
    unfold frozenSource
    fun_prop
  exact ((hh'.comp 0 hs).sub contDiffAt_const).const_smul r⁻¹

/-- Local smoothness is preserved by the dual frozen normalization. -/
theorem contDiffAt_normalizedCovector {m : ℕ} {r : ℝ} (T : E ≃L[ℝ] E)
    (x : E) {v : E → E} (hv : ContDiffAt ℝ m v x) :
    ContDiffAt ℝ m (normalizedCovector r T x v) 0 := by
  have hv' : ContDiffAt ℝ m v (frozenSource r T x 0) := by
    simpa [frozenSource] using hv
  have hs : ContDiffAt ℝ m (frozenSource r T x) 0 := by
    unfold frozenSource
    fun_prop
  exact (((T.symm : E →L[ℝ] E).adjoint.contDiff.contDiffAt).comp 0
    (hv'.comp 0 hs)).const_smul r⁻¹

omit [CompleteSpace E] in
/-- The same map at the next radius is obtained by a contracting metric
change and dyadic output scaling. -/
theorem normalizedCoordinates_dyadic {r : ℝ} (hr : r ≠ 0)
    (T U : E ≃L[ℝ] E) (x : E) (h : E → E) :
    normalizedCoordinates (r / 2) U x h = fun z => (2 : ℝ) •
      normalizedCoordinates r T x h
        ((1 / 2 : ℝ) • (((T : E →L[ℝ] E) ∘L (U.symm : E →L[ℝ] E)) z)) := by
  funext z
  have hsource : frozenSource r T x
      ((1 / 2 : ℝ) • (((T : E →L[ℝ] E) ∘L (U.symm : E →L[ℝ] E)) z)) =
      frozenSource (r / 2) U x z := by
    simp [frozenSource, smul_smul, div_eq_mul_inv]
  unfold normalizedCoordinates
  rw [hsource, smul_smul]
  congr 1
  field_simp

/-- Positive-order jets of the actual normalized update agree with
those of the normalized inverse-transpose update. The centering error
is a constant and the covariance identity is needed only locally. -/
theorem iteratedFDeriv_normalized_update {r : ℝ} (hr : r ≠ 0)
    (T : E ≃L[ℝ] E) (x : E) (h v : E → E) (e : E → E ≃L[ℝ] E)
    {m : ℕ} (hm : 0 < m) (hh : ContDiffAt ℝ (m + 1) h x)
    (hv : ContDiffAt ℝ m v x)
    (he : ∀ᶠ y in 𝓝 x, fderiv ℝ h y = (e y : E →L[ℝ] E)) :
    iteratedFDeriv ℝ m (normalizedCoordinates r T x
      (fun y => h y + operatorInverseTranspose (fderiv ℝ h y) (v y))) 0 =
    iteratedFDeriv ℝ m (fun z => normalizedCoordinates r T x h z +
      operatorInverseTranspose (fderiv ℝ (normalizedCoordinates r T x h) z)
        (normalizedCovector r T x v z)) 0 := by
  let g := normalizedCoordinates r T x h
  let w := normalizedCovector r T x v
  let f := fun y => h y + operatorInverseTranspose (fderiv ℝ h y) (v y)
  let u := fun z => g z + operatorInverseTranspose (fderiv ℝ g z) (w z)
  have he0 : fderiv ℝ h x = (e x : E →L[ℝ] E) := Filter.EventuallyEq.eq_of_nhds he
  have hg : ContDiffAt ℝ (m + 1) g 0 := contDiffAt_normalizedCoordinates (r := r) T x hh
  have hw : ContDiffAt ℝ m w 0 := contDiffAt_normalizedCovector (r := r) T x hv
  have hgJ : fderiv ℝ g 0 = (T.symm.trans (e x) : E →L[ℝ] E) := by
    change fderiv ℝ (normalizedCoordinates r T x h) 0 = _
    rw [fderiv_normalizedCoordinates hr T x 0 h]
    · simp only [frozenSource, map_zero, smul_zero, add_zero, he0]
      rfl
    · simpa [frozenSource] using hh.differentiableAt (by norm_cast)
  have hunit : IsUnit (fderiv ℝ g 0) := by
    rw [hgJ]
    exact (T.symm.trans (e x)).toUnit.isUnit
  have hu : ContDiffAt ℝ m u 0 :=
    (hg.of_le (by exact_mod_cast Nat.le_succ m)).add
      ((contDiffAt_inverseTranspose_field (hg.fderiv_right (by simp)) hunit).clm_apply hw)
  have htend : Tendsto (frozenSource r T x) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (frozenSource r T x) := by unfold frozenSource; fun_prop
    simpa [frozenSource] using hc.tendsto (0 : E)
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y :=
    (hh.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_cast)
  let b := -(r⁻¹ • operatorInverseTranspose (fderiv ℝ h x) (v x))
  have heq : normalizedCoordinates r T x f =ᶠ[𝓝 0] (fun z => u z + b) := by
    filter_upwards [htend.eventually he, htend.eventually hd] with z hez hdz
    have hid := normalized_update_identity hr T x z h v hdz (e (frozenSource r T x z)) hez
    change r⁻¹ • (f (frozenSource r T x z) - f x) = u z + b
    change r⁻¹ • (f (frozenSource r T x z) - h x) = u z at hid
    dsimp only [f, b]
    rw [← hid]
    module
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds]
  change iteratedFDeriv ℝ m (u + fun _ => b) 0 = _
  rw [iteratedFDeriv_add_apply hu contDiffAt_const]
  simp [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hm), u, g, w]

/-- The next frozen metric preserves a requested jet order, from only
source orders through `m+1`. The small parameter is independent of `m`. -/
theorem exists_frozen_normalized_jet_step
    {A B Cv : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (hCv : 0 ≤ Cv) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (r : ℝ), 0 < r → ∀ (T U : E ≃L[ℝ] E) (x : E) (h v : E → E)
        (e : E → E ≃L[ℝ] E) (m : ℕ), 2 ≤ m →
      ContDiffAt ℝ (m + 1) h x → ContDiffAt ℝ m v x →
      (∀ᶠ y in 𝓝 x, fderiv ℝ h y = (e y : E →L[ℝ] E)) →
      (∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖fderiv ℝ h x xi‖ ^ 2) →
      (∀ xi, ‖T xi‖ ≤ ‖U xi‖) →
      (∀ q, 2 ≤ q → q ≤ m + 1 →
        ‖iteratedFDeriv ℝ q (normalizedCoordinates r T x h) 0‖ ≤
          B ^ (q - 1) * (q.factorial : ℝ) ^ 3) →
      (∀ q, q ≤ m → ‖iteratedFDeriv ℝ q (normalizedCovector r T x v) 0‖ ≤
        epsilon * Cv * factorialMajorant q * jetCoefficientScale B q) →
      ‖iteratedFDeriv ℝ m (normalizedCoordinates (r / 2) U x
        (fun y => h y + operatorInverseTranspose (fderiv ℝ h y) (v y))) 0‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  obtain ⟨epsilon, hepsilon, hstep⟩ := exists_normalized_jet_step_finite (E := E) hA hB hCv
  refine ⟨epsilon, hepsilon, ?_⟩
  intro r hr T U x h v e m hm hh hv he hlower hmetric hjets hvjets
  let g := normalizedCoordinates r T x h
  let w := normalizedCovector r T x v
  let f := fun y => h y + operatorInverseTranspose (fderiv ℝ h y) (v y)
  have he0 : fderiv ℝ h x = (e x : E →L[ℝ] E) := Filter.EventuallyEq.eq_of_nhds he
  have hg : ContDiffAt ℝ (m + 1) g 0 := contDiffAt_normalizedCoordinates (r := r) T x hh
  have hw : ContDiffAt ℝ m w 0 := contDiffAt_normalizedCovector (r := r) T x hv
  have hgJ : fderiv ℝ g 0 = (T.symm.trans (e x) : E →L[ℝ] E) := by
    change fderiv ℝ (normalizedCoordinates r T x h) 0 = _
    rw [fderiv_normalizedCoordinates hr.ne' T x 0 h]
    · simp only [frozenSource, map_zero, smul_zero, add_zero, he0]
      rfl
    · simpa [frozenSource] using hh.differentiableAt (by norm_cast)
  have hunit : IsUnit (fderiv ℝ g 0) := by rw [hgJ]; exact (T.symm.trans (e x)).toUnit.isUnit
  have hginv : ‖Ring.inverse (fderiv ℝ g 0)‖ ≤ Real.sqrt A := by
    have heLower : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖e x xi‖ ^ 2 := by
      simpa only [he0, ContinuousLinearEquiv.coe_coe] using hlower
    have hinv : Ring.inverse (fderiv ℝ g 0) =
        (T : E →L[ℝ] E) ∘L ((e x).symm : E →L[ℝ] E) := by
      rw [hgJ]
      change Ring.inverse ((T.symm.trans (e x)).toUnit : E →L[ℝ] E) = _
      rw [Ring.inverse_unit]
      rfl
    rw [hinv]
    exact norm_frozen_comp_inverse_le T (e x) hA heLower
  have hbound := hstep m hm g w 0 hg hw hunit hginv hjets hvjets
  have hf : ContDiffAt ℝ m f x :=
    (hh.of_le (by norm_cast; omega)).add
      ((contDiffAt_inverseTranspose_field (hh.fderiv_right (by simp))
        (by rw [he0]; exact (e x).toUnit.isUnit)).clm_apply hv)
  have hnorm := norm_iteratedFDeriv_dyadic_metric_change_le
    ((T : E →L[ℝ] E) ∘L (U.symm : E →L[ℝ] E))
    (normalizedCoordinates r T x f) 0 (by omega : 0 < m)
    (norm_metric_change_le_one T U hmetric) (contDiffAt_normalizedCoordinates T x hf)
  have heq := normalizedCoordinates_dyadic hr.ne' T U x f
  simp only [add_zero] at hnorm
  rw [← heq, iteratedFDeriv_normalized_update hr.ne' T x h v e (by omega) hh hv he] at hnorm
  exact hnorm.trans hbound

/-- Dyadic radii, written without integer exponents. -/
def iterationRadius (r0 : ℝ) (i : ℕ) : ℝ := r0 / (2 : ℝ) ^ i

theorem iterationRadius_pos {r0 : ℝ} (hr0 : 0 < r0) (i : ℕ) :
    0 < iterationRadius r0 i := by unfold iterationRadius; positivity

theorem iterationRadius_succ (r0 : ℝ) (i : ℕ) :
    iterationRadius r0 (i + 1) = iterationRadius r0 i / 2 := by
  unfold iterationRadius
  rw [pow_succ]
  ring

/-- Explicit analytic inputs for the finite iteration. The mass and
principal comparisons come before construction of the coordinate maps;
none of the fields below assumes a coordinate metric or a scalar error
recurrence. -/
structure AnalyticIterationData (Ω : Set E) (r0 T F B epsilon : ℝ) where
  frozen : ℕ → E → E ≃L[ℝ] E
  correction : ℕ → E → E
  principal : ℕ → E → E →L[ℝ] E
  mass : ℕ → E → E →L[ℝ] E
  energy : ℕ → E → ℝ
  frozen_mono : ∀ i x, x ∈ Ω → ∀ xi, ‖frozen i x xi‖ ≤ ‖frozen (i + 1) x xi‖
  correction_smooth : ∀ i x, x ∈ Ω → ∀ m : ℕ, ContDiffAt ℝ m (correction i) x
  energy_nonneg : ∀ i x, x ∈ Ω → 0 ≤ energy i x
  energy_budget : ∀ k x, x ∈ Ω → (∑ i ∈ Finset.range k, energy i x) ≤ epsilon
  mass_nonneg : ∀ i x, x ∈ Ω → ∀ xi, 0 ≤ ⟪xi, mass i x xi⟫_ℝ
  principal_nonneg : ∀ i x, x ∈ Ω → ∀ xi, 0 ≤ ⟪xi, principal i x xi⟫_ℝ
  principal_le_mass : ∀ i x, x ∈ Ω → ∀ xi, ⟪xi, principal i x xi⟫_ℝ ≤ ⟪xi, mass i x xi⟫_ℝ
  mass_budget : ∀ k x, x ∈ Ω → ∀ xi,
    ‖xi‖ ^ 2 + (∑ i ∈ Finset.range k, ⟪xi, mass i x xi⟫_ℝ) ≤ T * ‖frozen k x xi‖ ^ 2
  principal_budget : ∀ k x, x ∈ Ω → ∀ xi,
    ‖frozen k x xi‖ ^ 2 ≤ T * (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k, ⟪xi, principal i x xi⟫_ℝ)
  value_bound : ∀ i x, x ∈ Ω →
    ‖(frozen i x).symm.toContinuousLinearMap.adjoint (correction i x)‖ ≤
      F * Real.sqrt epsilon * iterationRadius r0 i * Real.sqrt (energy i x)
  first_bound : ∀ i x, x ∈ Ω → ∀ xi,
    ‖(frozen i x).symm.toContinuousLinearMap.adjoint (fderiv ℝ (correction i) x xi)‖ ≤
      F * Real.sqrt epsilon * (Real.sqrt ⟪xi, mass i x xi⟫_ℝ + Real.sqrt (energy i x) * ‖frozen i x xi‖)
  second_bound : ∀ i x, x ∈ Ω → ∀ xi,
    ‖(frozen i x).symm.toContinuousLinearMap.adjoint (diagonalSecond (correction i) x xi)‖ ≤
      F / iterationRadius r0 i * (Real.sqrt ⟪xi, mass i x xi⟫_ℝ * ‖frozen i x xi‖ +
        Real.sqrt (energy i x) * ‖frozen i x xi‖ ^ 2)
  linear_bound : ∀ i x, x ∈ Ω → ∀ xi,
    |⟪xi, fderiv ℝ (correction i) x xi - principal i x xi⟫_ℝ| ≤
      F * Real.sqrt ⟪xi, mass i x xi⟫_ℝ * Real.sqrt (energy i x) * ‖frozen i x xi‖
  correction_jets : ∀ i x, x ∈ Ω → ∀ m,
    ‖iteratedFDeriv ℝ m (normalizedCovector (iterationRadius r0 i) (frozen i x) x (correction i)) 0‖ ≤
      epsilon * F * factorialMajorant m * jetCoefficientScale B m

omit [CompleteSpace E] in
/-- An invertible Jacobian representative may be selected locally from
coercivity on an open set. No smoothness of the selected representative
is needed: it agrees with the actual Jacobian throughout the set. -/
theorem exists_local_jacobian_family [FiniteDimensional ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) (h : E → E) (T : E → E ≃L[ℝ] E)
    {A : ℝ} (hA : 1 ≤ A)
    (hlower : ∀ x ∈ Ω, ∀ xi, A⁻¹ * ‖T x xi‖ ^ 2 ≤ ‖fderiv ℝ h x xi‖ ^ 2) :
    ∃ e : E → E ≃L[ℝ] E, ∀ x ∈ Ω,
      ∀ᶠ y in 𝓝 x, fderiv ℝ h y = (e y : E →L[ℝ] E) := by
  classical
  have hex : ∀ y, ∃ e : E ≃L[ℝ] E, y ∈ Ω → fderiv ℝ h y = (e : E →L[ℝ] E) := by
    intro y
    by_cases hy : y ∈ Ω
    · obtain ⟨e, he⟩ := exists_equiv_of_metric_lower (T y) (fderiv ℝ h y) hA (hlower y hy)
      exact ⟨e, fun _ => he.symm⟩
    · exact ⟨ContinuousLinearEquiv.refl ℝ E, fun hy' => (hy hy').elim⟩
  choose e he using hex
  exact ⟨e, fun x hx => Filter.Eventually.mono (hΩ.mem_nhds hx) (fun y hy => he y hy)⟩

omit [CompleteSpace E] in
/-- The identity starts the iteration with all higher jets zero. -/
theorem norm_iteratedFDeriv_id_of_two_le {m : ℕ} (hm : 2 ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ m (id : E → E) x‖ = 0 := by
  have heq : m = (m - 1) + 1 := by omega
  rw [heq, ← norm_iteratedFDeriv_fderiv]
  have hid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  rw [hid, iteratedFDeriv_const_of_ne (by omega)]
  simp

/-- Both the all-order jet threshold and the metric error threshold can
be met by a single positive parameter. -/
theorem exists_small_metric_iteration_parameter {C T delta : ℝ}
    (hT : 0 < T) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ epsilon ≤ delta ∧
      scalarMetricErrorCoefficient (pointwiseIterationCoefficient C) T epsilon ≤ (2 * T)⁻¹ := by
  have htarget : 0 < (2 * T)⁻¹ := by positivity
  obtain ⟨d, hd, hclose⟩ := Metric.tendsto_nhds_nhds.mp
    (scalarMetricErrorCoefficient_tendsto_zero (pointwiseIterationCoefficient C) T)
    _ htarget
  let epsilon := min (d / 2) (min delta 1)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hed : epsilon ≤ d / 2 := min_le_left _ _
  have he1 : epsilon ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hedelta : epsilon ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have hdist : dist epsilon 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hepsilon]
    linarith
  have hsmall := hclose hdist
  rw [Real.dist_eq, sub_zero] at hsmall
  exact ⟨epsilon, hepsilon, he1, hedelta, (le_abs_self _).trans hsmall.le⟩

/-- All finite stages are smooth on the given open set, coercive, and
have the same normalized higher-jet bounds. The constants are chosen in
order: metric bootstrap `4T`, inverse constant, fixed jet base, then a
single positive defect parameter. -/
theorem exists_analytic_metric_iteration [FiniteDimensional ℝ E]
    {T F B : ℝ} (hT : 1 ≤ T) (hF : 1 ≤ F) (hB : 1 ≤ B) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (Ω : Set E), IsOpen Ω → ∀ (r0 : ℝ), 0 < r0 →
      ∀ d : AnalyticIterationData (E := E) Ω r0 T F B epsilon,
      ∀ k x, x ∈ Ω →
        (∀ m : ℕ, ContDiffAt ℝ m (metricIterate d.correction k) x) ∧
        (∀ xi, (4 * T)⁻¹ * ‖d.frozen k x xi‖ ^ 2 ≤
            ‖fderiv ℝ (metricIterate d.correction k) x xi‖ ^ 2 ∧
          ‖fderiv ℝ (metricIterate d.correction k) x xi‖ ^ 2 ≤
            (4 * T) * ‖d.frozen k x xi‖ ^ 2) ∧
        (∀ m, 2 ≤ m →
          ‖iteratedFDeriv ℝ m (normalizedCoordinates (iterationRadius r0 k)
            (d.frozen k x) x (metricIterate d.correction k)) 0‖ ≤
              B ^ (m - 1) * (m.factorial : ℝ) ^ 3) := by
  have hA : 1 ≤ 4 * T := by linarith
  have hBpos : 0 < B := by linarith
  have hFnonneg : 0 ≤ F := by linarith
  obtain ⟨Ci, hCi0, hCiA, hcost⟩ := exists_frozen_inverse_derivative_cost (E := E) hA
  have hCinonneg : 0 ≤ Ci := (Real.sqrt_nonneg _).trans hCi0
  let C := 1 + F + Real.sqrt (4 * T) + 8 * Ci * B + 216 * Ci * B ^ 2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (4 * T)]
  have hCF : F ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (4 * T)]
  have hCroot : Real.sqrt (4 * T) ≤ C := by dsimp [C]; nlinarith
  have hCfirst : 8 * Ci * B ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (4 * T)]
  have hCsecond : 216 * Ci * B ^ 2 ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (4 * T)]
  obtain ⟨delta, hdelta, hjetstep⟩ := exists_frozen_normalized_jet_step (E := E) hA hBpos hFnonneg
  obtain ⟨epsilon, hepsilon, he1, hedelta, hesmall⟩ :=
    exists_small_metric_iteration_parameter (C := C) (by linarith : 0 < T) hdelta
  refine ⟨epsilon, hepsilon, he1, ?_⟩
  intro Ω hΩ r0 hr0 d
  have hr : ∀ i, 0 < iterationRadius r0 i := iterationRadius_pos hr0
  have hsmoothstep {i : ℕ} {x : E} (hx : x ∈ Ω)
      (hi : ∀ m : ℕ, ContDiffAt ℝ m (metricIterate d.correction i) x)
      (hmetric : ∀ xi, (4 * T)⁻¹ * ‖d.frozen i x xi‖ ^ 2 ≤
        ‖fderiv ℝ (metricIterate d.correction i) x xi‖ ^ 2) :
      ∀ m : ℕ, ContDiffAt ℝ m (metricIterate d.correction (i + 1)) x := by
    intro m
    rw [metricIterate_succ]
    exact (hi m).add ((contDiffAt_inverseTranspose_field ((hi (m + 1)).fderiv_right (by simp))
      (isUnit_of_metric_lower (d.frozen i x) _ hA hmetric)).clm_apply (d.correction_smooth i x hx m))
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hequiv : ∀ i, ∃ e : E → E ≃L[ℝ] E, ∀ x ∈ Ω, i < k →
        ∀ᶠ y in 𝓝 x, fderiv ℝ (metricIterate d.correction i) y = (e y : E →L[ℝ] E) := by
      intro i
      by_cases hi : i < k
      · obtain ⟨e, he⟩ := exists_local_jacobian_family hΩ (metricIterate d.correction i)
          (d.frozen i) hA (fun x hx xi => ((ih i hi x hx).2.1 xi).1)
        exact ⟨e, fun x hx _ => he x hx⟩
      · exact ⟨fun _ => ContinuousLinearEquiv.refl ℝ E, fun _ _ hi' => (hi hi').elim⟩
    choose e he using hequiv
    intro x hx
    cases k with
    | zero =>
      refine ⟨fun _ => contDiffAt_id, ?_, ?_⟩
      · intro xi
        simp only [metricIterate_zero, fderiv_id, ContinuousLinearMap.id_apply]
        have hlower : ‖d.frozen 0 x xi‖ ^ 2 ≤ T * ‖xi‖ ^ 2 := by
          simpa using d.principal_budget 0 x hx xi
        have hupper : ‖xi‖ ^ 2 ≤ T * ‖d.frozen 0 x xi‖ ^ 2 := by
          simpa using d.mass_budget 0 x hx xi
        constructor
        · rw [← div_eq_inv_mul]
          apply (div_le_iff₀ (by linarith : 0 < 4 * T)).2
          have hnonneg : 0 ≤ T * ‖xi‖ ^ 2 := by positivity
          nlinarith only [hlower, hnonneg]
        · have hnonneg : 0 ≤ T * ‖d.frozen 0 x xi‖ ^ 2 := by positivity
          nlinarith only [hupper, hnonneg]
      · intro m hm
        have hzero := normalized_jet_norm_le (d.frozen 0 x) (id : E → E) x 0
          (iterationRadius r0 0) (by omega : 0 < m) contDiffAt_id
        rw [norm_iteratedFDeriv_id_of_two_le hm, mul_zero, zero_mul] at hzero
        exact hzero.trans (by positivity)
    | succ n =>
      have hn : n < n + 1 := Nat.lt_succ_self n
      have hprev := ih n hn x hx
      refine ⟨hsmoothstep hx hprev.1 (fun xi => (hprev.2.1 xi).1), ?_, ?_⟩
      · intro xi
        by_cases hxi : xi = 0
        · simp [hxi]
        have hq : ∀ i, 0 < ‖d.frozen i x xi‖ := by
          intro i
          exact norm_pos_iff.mpr (fun hz => hxi ((d.frozen i x).injective (by simpa using hz)))
        have hmono : Monotone (fun i => ‖d.frozen i x xi‖) :=
          monotone_nat_of_le_succ (fun i => d.frozen_mono i x hx xi)
        have hleading := leading_metric_comparison (sq_nonneg ‖xi‖) (by linarith : 0 < T)
          (fun i => d.principal_nonneg i x hx xi) (n + 1)
          (fun i _ => d.principal_le_mass i x hx xi)
          (d.principal_budget (n + 1) x hx xi) (d.mass_budget (n + 1) x hx xi)
        have hcosts (i : ℕ) (hi : i < n + 1) :
            ∀ w : E,
              ‖fderiv ℝ (fun y => operatorInverseTranspose
                (fderiv ℝ (metricIterate d.correction i) y)) x xi w‖ ≤
                  8 * Ci * B / iterationRadius r0 i * ‖d.frozen i x xi‖ *
                    ‖(d.frozen i x).symm.toContinuousLinearMap.adjoint w‖ ∧
              ‖diagonalSecond (fun y => operatorInverseTranspose
                (fderiv ℝ (metricIterate d.correction i) y)) x xi w‖ ≤
                  216 * Ci * B ^ 2 / (iterationRadius r0 i) ^ 2 * ‖d.frozen i x xi‖ ^ 2 *
                    ‖(d.frozen i x).symm.toContinuousLinearMap.adjoint w‖ := by
          exact hcost B (iterationRadius r0 i) hBpos (hr i) (d.frozen i x) x
            (metricIterate d.correction i) (e i) ((ih i hi x hx).1 3)
            (he i x hx hi) (fun y => ((ih i hi x hx).2.1 y).1)
            (fun m hm _ => (ih i hi x hx).2.2 m hm) xi
        apply pointwise_metric_iteration (metricIterate d.correction) d.correction
          (fun i => e i x) (fun i => d.principal i x)
          (fun i w => ‖(d.frozen i x).symm.toContinuousLinearMap.adjoint w‖)
          x xi (fun i => ‖d.frozen i x xi‖) (iterationRadius r0)
          (fun i => ⟪xi, d.mass i x xi⟫_ℝ) (fun i => d.energy i x) (n + 1)
          hC hT hepsilon.le he1 (sq_nonneg _) hq hr
          (fun i => d.mass_nonneg i x hx xi) (fun i => d.energy_nonneg i x hx)
          (fun i hi => (ih i hi x hx).1 3) (fun i _ => d.correction_smooth i x hx 2)
          (fun i hi => Filter.EventuallyEq.eq_of_nhds (he i x hx hi))
          (fun _ _ => rfl) (fun i _ => iterationRadius_succ r0 i)
          (fun i _ => d.frozen_mono i x hx xi)
        · simp [metricIterate, diagonalSecond]
        · intro i hi w
          have he0 := Filter.EventuallyEq.eq_of_nhds (he i x hx hi)
          rw [he0, operatorInverseTranspose_equiv]
          have hlower : ∀ y, (4 * T)⁻¹ * ‖d.frozen i x y‖ ^ 2 ≤ ‖e i x y‖ ^ 2 := by
            simpa only [he0, ContinuousLinearEquiv.coe_coe] using
              (fun y => ((ih i hi x hx).2.1 y).1)
          exact (inverseTranspose_norm_le_frozen (d.frozen i x) (e i x) hA hlower w).trans
            (mul_le_mul_of_nonneg_right hCroot (norm_nonneg _))
        · intro i hi w
          exact ((hcosts i hi w).1).trans (by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc
              _ = (8 * Ci * B) * (‖d.frozen i x xi‖ / iterationRadius r0 i) := by ring
              _ ≤ C * (‖d.frozen i x xi‖ / iterationRadius r0 i) :=
                mul_le_mul_of_nonneg_right hCfirst (div_nonneg (norm_nonneg _) (hr i).le)
              _ = _ := by ring)
        · intro i hi w
          exact ((hcosts i hi w).2).trans (by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc
              _ = (216 * Ci * B ^ 2) * (‖d.frozen i x xi‖ ^ 2 / (iterationRadius r0 i) ^ 2) := by ring
              _ ≤ C * (‖d.frozen i x xi‖ ^ 2 / (iterationRadius r0 i) ^ 2) :=
                mul_le_mul_of_nonneg_right hCsecond (by positivity)
              _ = _ := by ring)
        · intro i _
          have hri := (hr i).le
          exact (d.value_bound i x hx).trans (by gcongr)
        · intro i _
          exact (d.first_bound i x hx xi).trans (by gcongr)
        · intro i _
          have hri := (hr i).le
          exact (d.second_bound i x hx xi).trans (by gcongr)
        · intro i _
          exact (d.linear_bound i x hx xi).trans (by gcongr)
        · nlinarith [d.mass_budget (n + 1) x hx xi, sq_nonneg ‖xi‖]
        · exact weighted_defect_sum_le (fun i => d.energy_nonneg i x hx) (sq_nonneg _) (n + 1)
            (fun i hi => by
              nlinarith [hmono (Nat.le_of_lt hi), norm_nonneg (d.frozen i x xi),
                norm_nonneg (d.frozen (n + 1) x xi)]) (d.energy_budget (n + 1) x hx)
        · simpa only [metricIterate_zero, fderiv_id, ContinuousLinearMap.id_apply] using hleading.1
        · simpa only [metricIterate_zero, fderiv_id, ContinuousLinearMap.id_apply] using hleading.2
        · exact hesmall
      · intro m hm
        rw [metricIterate_succ, iterationRadius_succ]
        apply hjetstep (iterationRadius r0 n) (hr n) (d.frozen n x) (d.frozen (n + 1) x)
          x (metricIterate d.correction n) (d.correction n) (e n) m hm
          (hprev.1 (m + 1)) (d.correction_smooth n x hx m) (he n x hx hn)
          (fun xi => (hprev.2.1 xi).1) (d.frozen_mono n x hx)
          (fun q hq _ => hprev.2.2 q hq)
        intro q _
        exact (d.correction_jets n x hx q).trans (by
          apply mul_le_mul_of_nonneg_right _ (jetCoefficientScale_pos hBpos q).le
          apply mul_le_mul_of_nonneg_right _ (factorialMajorant_pos q).le
          exact mul_le_mul_of_nonneg_right hedelta hFnonneg)

/-- Every Jacobian produced by the analytic iteration is a unit. In
finite dimension this is a consequence of the proved metric lower
bound, rather than an additional input to the construction. -/
theorem exists_analytic_metric_iteration_invertible [FiniteDimensional ℝ E]
    {T F B : ℝ} (hT : 1 ≤ T) (hF : 1 ≤ F) (hB : 1 ≤ B) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (Ω : Set E), IsOpen Ω → ∀ (r0 : ℝ), 0 < r0 →
      ∀ d : AnalyticIterationData (E := E) Ω r0 T F B epsilon,
      ∀ k x, x ∈ Ω → IsUnit (fderiv ℝ (metricIterate d.correction k) x) := by
  obtain ⟨epsilon, hepsilon, he1, hcontrol⟩ :=
    exists_analytic_metric_iteration (E := E) hT hF hB
  refine ⟨epsilon, hepsilon, he1, ?_⟩
  intro Ω hΩ r0 hr0 d k x hx
  exact isUnit_of_metric_lower (d.frozen k x) _ (by linarith : 1 ≤ 4 * T)
    (fun xi => ((hcontrol Ω hΩ r0 hr0 d k x hx).2.1 xi).1)

end RegularPointCoordinates

end

end OAI
