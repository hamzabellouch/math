import OAI.Dynamics.EntropyCounterexample.SphereCharts

namespace OAI

noncomputable section
open scoped RealInnerProductSpace ContDiff OnePoint

namespace Problem340

def sphereInfinityFlipLinear : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient where
  toFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2]
  invFun x := WithLp.toLp 2 ![x 0, -x 1, -x 2]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' r x := by ext i; fin_cases i <;> simp
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]

@[simp] theorem sphereInfinityFlipLinear_zero (x : SphereAmbient) :
    sphereInfinityFlipLinear x 0 = x 0 := rfl

@[simp] theorem sphereInfinityFlipLinear_one (x : SphereAmbient) :
    sphereInfinityFlipLinear x 1 = -x 1 := rfl

@[simp] theorem sphereInfinityFlipLinear_two (x : SphereAmbient) :
    sphereInfinityFlipLinear x 2 = -x 2 := rfl

@[simp] theorem sphereInfinityFlipLinear_involutive (x : SphereAmbient) :
    sphereInfinityFlipLinear (sphereInfinityFlipLinear x) = x :=
  sphereInfinityFlipLinear.left_inv x

def sphereInfinityFlip (x : StandardSphere2) : StandardSphere2 :=
  ⟨sphereInfinityFlipLinear x.val, by simp⟩

@[simp] theorem sphereInfinityFlip_involutive (x : StandardSphere2) :
    sphereInfinityFlip (sphereInfinityFlip x) = x := by
  apply Subtype.ext
  exact sphereInfinityFlipLinear_involutive x.val

def sphereAtInfinity (w : ℂ) : StandardSphere2 :=
  sphereInfinityFlip (sphereOfComplex w)

@[simp] theorem sphereAtInfinity_val_zero (w : ℂ) :
    (sphereAtInfinity w).val 0 = 2 * w.re / (‖w‖ ^ 2 + 1) := by
  change (sphereOfComplex w).val 0 = _
  exact sphereOfComplex_val_zero w

@[simp] theorem sphereAtInfinity_val_one (w : ℂ) :
    (sphereAtInfinity w).val 1 = -(2 * w.im / (‖w‖ ^ 2 + 1)) := by
  change -(sphereOfComplex w).val 1 = _
  rw [sphereOfComplex_val_one]

@[simp] theorem sphereAtInfinity_val_two (w : ℂ) :
    (sphereAtInfinity w).val 2 = -((‖w‖ ^ 2 - 1) / (‖w‖ ^ 2 + 1)) := by
  change -(sphereOfComplex w).val 2 = _
  rw [sphereOfComplex_val_two]

@[simp] theorem sphereAtInfinity_zero : sphereAtInfinity 0 = chartNorthPole := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [chartNorthPole, chartNorthVector]

theorem contDiff_sphereAtInfinity_val {n : ℕ∞ω} :
    ContDiff ℝ n (fun w : ℂ => (sphereAtInfinity w : SphereAmbient)) :=
  sphereInfinityFlipLinear.contDiff.comp contDiff_sphereOfComplex_val

theorem continuous_sphereAtInfinity : Continuous sphereAtInfinity :=
  continuous_induced_rng.2 (contDiff_sphereAtInfinity_val (n := 0)).continuous

theorem sphereAtInfinity_eq_sphereOfComplex_inv {w : ℂ} (hw : w ≠ 0) :
    sphereAtInfinity w = sphereOfComplex w⁻¹ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hn2 : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have hd : ‖w‖ ^ 2 + 1 ≠ 0 := by positivity
  apply Subtype.ext
  ext i
  fin_cases i
  · change (sphereAtInfinity w).val 0 = (sphereOfComplex w⁻¹).val 0
    rw [sphereAtInfinity_val_zero, sphereOfComplex_val_zero]
    simp only [Complex.inv_re, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
    field_simp
    ring
  · change (sphereAtInfinity w).val 1 = (sphereOfComplex w⁻¹).val 1
    rw [sphereAtInfinity_val_one, sphereOfComplex_val_one]
    simp only [Complex.inv_im, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
    field_simp
    ring
  · change (sphereAtInfinity w).val 2 = (sphereOfComplex w⁻¹).val 2
    rw [sphereAtInfinity_val_two, sphereOfComplex_val_two]
    simp only [norm_inv, inv_pow]
    field_simp
    ring

def chartSouthPole : StandardSphere2 := sphereOfComplex 0

@[simp] theorem sphereInfinityFlip_south : sphereInfinityFlip chartSouthPole = chartNorthPole :=
  sphereAtInfinity_zero

@[simp] theorem sphereInfinityFlip_north : sphereInfinityFlip chartNorthPole = chartSouthPole := by
  rw [← sphereInfinityFlip_south, sphereInfinityFlip_involutive]

def complexInfinityCoordinate (w : ℂ) : OnePoint ℂ :=
  if w = 0 then ∞ else (w⁻¹ : ℂ)

@[simp] theorem complexSphereHomeomorph_infinityCoordinate (w : ℂ) :
    complexSphereHomeomorph (complexInfinityCoordinate w) = sphereAtInfinity w := by
  by_cases hw : w = 0
  · simp [complexInfinityCoordinate, hw]
  · simp only [complexInfinityCoordinate, ite_eq_right hw, complexSphereHomeomorph_coe]
    exact (sphereAtInfinity_eq_sphereOfComplex_inv hw).symm

@[simp] theorem complexSphereHomeomorph_symm_atInfinity (w : ℂ) :
    complexSphereHomeomorph.symm (sphereAtInfinity w) = complexInfinityCoordinate w := by
  exact complexSphereHomeomorph.symm_apply_eq.mpr
    (complexSphereHomeomorph_infinityCoordinate w).symm

def sphereInfinityCoordinate (x : StandardSphere2) : ℂ :=
  sphereToComplex (sphereInfinityFlip x)

def sphereInfinityCoordinateAmbient (x : SphereAmbient) : ℂ :=
  sphereToComplexAmbient (sphereInfinityFlipLinear x)

@[simp] theorem sphereInfinityCoordinate_atInfinity (w : ℂ) :
    sphereInfinityCoordinate (sphereAtInfinity w) = w := by
  unfold sphereInfinityCoordinate sphereAtInfinity
  rw [sphereInfinityFlip_involutive, sphereToComplex_sphereOfComplex]

theorem sphereAtInfinity_ne_south (w : ℂ) : sphereAtInfinity w ≠ chartSouthPole := by
  intro h
  have hh := congrArg sphereInfinityFlip h
  simp only [sphereAtInfinity, sphereInfinityFlip_involutive, sphereInfinityFlip_south] at hh
  exact sphereOfComplex_ne_north w hh

theorem sphereAtInfinity_sphereInfinityCoordinate {x : StandardSphere2}
    (hx : x ≠ chartSouthPole) : sphereAtInfinity (sphereInfinityCoordinate x) = x := by
  have hf : sphereInfinityFlip x ≠ chartNorthPole := by
    intro h
    have hh := congrArg sphereInfinityFlip h
    apply hx
    simpa only [sphereInfinityFlip_involutive, sphereInfinityFlip_north] using hh
  unfold sphereAtInfinity sphereInfinityCoordinate
  rw [sphereOfComplex_sphereToComplex hf, sphereInfinityFlip_involutive]

theorem contDiffOn_sphereInfinityCoordinateAmbient {n : ℕ∞ω} :
    ContDiffOn ℝ n sphereInfinityCoordinateAmbient {x : SphereAmbient | x 2 ≠ -1} := by
  apply contDiffOn_sphereToComplexAmbient.comp sphereInfinityFlipLinear.contDiff.contDiffOn
  intro x hx
  change -x 2 ≠ 1
  change x 2 ≠ -1 at hx
  intro heq
  apply hx
  linarith

end Problem340

end

end OAI
