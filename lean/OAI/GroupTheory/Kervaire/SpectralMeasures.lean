import OAI.GroupTheory.Kervaire.StrongLimits

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-- Embed a real-valued function into complex-valued functions. -/
def complexify {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexify_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : complexify f x = (f x : ℂ) := rfl

@[simp] theorem complexify_add {X : Type*} [TopologicalSpace X]
    (f g : C(X, ℝ)) : complexify (f + g) = complexify f + complexify g := by ext; simp [complexify]

@[simp] theorem complexify_smul {X : Type*} [TopologicalSpace X]
    (r : ℝ) (f : C(X, ℝ)) : complexify (r • f) = (r : ℂ) • complexify f := by
  ext; simp [complexify]

/-- A vector functional restricted to the continuous calculus of a normal operator. -/
def vectorFunctional (U : Operator H) [hU : IsStarNormal U] (ξ : H) :
    C_c(spectrum ℂ U, ℝ) →ₚ[ℝ] ℝ := .mk₀ {
  toFun f := (inner ℂ ξ (cfcHom hU (complexify f.toContinuousMap) ξ)).re
  map_add' f g := by
    have hfg : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
    rw [hfg, complexify_add, map_add]
    simp
  map_smul' r f := by
    have hrf : (r • f).toContinuousMap = r • f.toContinuousMap := rfl
    rw [hrf, complexify_smul, map_smul]
    simp
  } (by
    intro f hf
    have hfc : 0 ≤ complexify f.toContinuousMap := by
      intro x
      exact (Complex.zero_le_real).mpr (hf x)
    have hc : 0 ≤ cfcHom hU (complexify f.toContinuousMap) :=
      (cfcHom_nonneg_iff hU).mpr hfc
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hc).re_inner_nonneg_right ξ)

/-- The finite scalar spectral measure of a vector, on the actual spectrum. -/
def vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) : Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure (vectorFunctional U ξ)

instance vectorMeasure_finite (U : Operator H) [IsStarNormal U] (ξ : H) :
    IsFiniteMeasure (vectorMeasure U ξ) := by
  dsimp [vectorMeasure]
  infer_instance

/-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re := by
  let fc : C_c(spectrum ℂ U, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (vectorFunctional U ξ) fc

/-- Squared modulus of a continuous complex function, kept real-valued. -/
def normSqMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun z => Complex.normSq (f z), Complex.continuous_normSq.comp f.continuous⟩

/-- The scalar measure gives squared norms of arbitrary continuous-calculus vectors. -/
theorem integral_normSqMap (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, normSqMap f z ∂vectorMeasure U ξ = ‖cfcHom hU f ξ‖ ^ 2 := by
  have hf : complexify (normSqMap f) = star f * f := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  rw [integral_vectorMeasure, hf, map_mul, map_star]
  change (inner ℂ ξ (star (cfcHom hU f) (cfcHom hU f ξ))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

theorem phase_nonneg (z : ℂ) : 0 ≤ phase z := Int.fract_nonneg _

theorem phase_lt_one (z : ℂ) : phase z < 1 := Int.fract_lt_one _

theorem measurable_phase : Measurable phase :=
  (Complex.measurable_arg.div_const _).fract

/-- On the unit circle only the identity has phase zero. -/
theorem phase_eq_zero_iff {z : ℂ} (hz : z ∈ unitary ℂ) : phase z = 0 ↔ z = 1 := by
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hp
    have harg : z.arg = (n : ℝ) * (2 * Real.pi) := by
      exact (div_eq_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mp hn.symm
    calc
      z = (‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I z).symm
      _ = 1 := by
        rw [CStarRing.norm_of_mem_unitary hz, harg]
        push_cast
        simpa only [mul_assoc, one_mul] using Complex.exp_int_mul_two_pi_mul_I n
  · rintro rfl
    exact phase_one

/-- A bounded measurable phase is integrable for every scalar spectral measure. -/
theorem integrable_phase (U : Operator H) [IsStarNormal U] (ξ : H) :
    Integrable (fun z : spectrum ℂ U => phase z) (vectorMeasure U ξ) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_phase.comp measurable_subtype_coe).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (phase_nonneg _)] using (phase_lt_one z).le

def vectorPhase (U : Operator H) [IsStarNormal U] (ξ : H) : ℝ :=
  ∫ z, phase z ∂vectorMeasure U ξ

theorem vectorPhase_nonneg (U : Operator H) [IsStarNormal U] (ξ : H) :
    0 ≤ vectorPhase U ξ := integral_nonneg fun _ => phase_nonneg _

/-- The continuous squared distance to one on the spectrum. -/
def distanceSq (U : Operator H) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => Complex.normSq ((z : ℂ) - 1),
    Complex.continuous_normSq.comp (continuous_subtype_val.sub continuous_const)⟩

/-- Its calculus is the positive square of `U - I`. -/
theorem distanceSq_calculus (U : Operator H) [hU : IsStarNormal U] :
    cfcHom hU (complexify (distanceSq U)) = star (U - 1) * (U - 1) := by
  let idMap : C(spectrum ℂ U, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : complexify (distanceSq U) = star (idMap - 1) * (idMap - 1) := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  rw [hf, map_mul, map_star, map_sub, map_one]
  have hid : cfcHom hU idMap = U := cfcHom_id (R := ℂ) hU
  rw [hid]

/-- The scalar spectral measure recovers the norm of the displacement. -/
theorem integral_distanceSq (U : Operator H) [hU : IsStarNormal U] (ξ : H) :
    ∫ z, distanceSq U z ∂vectorMeasure U ξ = ‖U ξ - ξ‖ ^ 2 := by
  rw [integral_vectorMeasure, distanceSq_calculus]
  change (inner ℂ ξ (star (U - 1) ((U - 1) ξ))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((U - 1) ξ)

/-- Zero vector phase forces this vector to be fixed. No spectral projection or
Borel operator calculus is assumed in this implication. -/
theorem fixed_of_vectorPhase_eq_zero (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) (h : letI := isStarNormal_of_mem_unitary hU; vectorPhase U ξ = 0) :
    U ξ = ξ := by
  let := isStarNormal_of_mem_unitary hU
  have ha : (fun z : spectrum ℂ U => phase z) =ᵐ[vectorMeasure U ξ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => phase_nonneg _) (integrable_phase U ξ)).mp h
  have hz : (fun z => distanceSq U z) =ᵐ[vectorMeasure U ξ] 0 := by
    filter_upwards [ha] with z hz
    have h1 : (z : ℂ) = 1 :=
      (phase_eq_zero_iff (spectrum_subset_unitary_of_mem_unitary hU z.property)).mp hz
    simp [distanceSq, h1]
  have hi : ‖U ξ - ξ‖ ^ 2 = 0 := by
    rw [← integral_distanceSq]
    exact (integral_congr_ae hz).trans (integral_zero _ _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hi))

/-- Bounded pointwise convergence of continuous spectral functions is strongly
Cauchy. The proof is scalar dominated convergence, applied to squared distances. -/
theorem cauchySeq_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    CauchySeq (fun n => cfcHom hU (f n) ξ) := by
  let F (p : ℕ × ℕ) (z : spectrum ℂ U) : ℝ :=
    Complex.normSq (f p.1 z - f p.2 z)
  have hF : ∀ p, AEStronglyMeasurable (F p) (vectorMeasure U ξ) := by
    intro p
    exact (Complex.continuous_normSq.comp ((f p.1).continuous.sub
      (f p.2).continuous)).aestronglyMeasurable
  have hbound : ∀ p z, ‖F p z‖ ≤ (2 * C) ^ 2 := by
    intro p z
    have hd : ‖f p.1 z - f p.2 z‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hb p.1 z, hb p.2 z])
    simp only [F, Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hlim : ∀ z, Tendsto (fun p : ℕ × ℕ => F p z) atTop (𝓝 0) := by
    intro z
    rw [← prod_atTop_atTop_eq]
    simpa [F, Function.comp_def] using Complex.continuous_normSq.continuousAt.tendsto.comp
      (((ht z).comp tendsto_fst).sub ((ht z).comp tendsto_snd))
  have hi : Tendsto (fun p : ℕ × ℕ => ∫ z, F p z ∂vectorMeasure U ξ)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * C) ^ 2) (Eventually.of_forall hF)
      (Eventually.of_forall fun p => Eventually.of_forall (hbound p))
      (integrable_const _) (Eventually.of_forall hlim)
  have heq : ∀ p : ℕ × ℕ, (∫ z, F p z ∂vectorMeasure U ξ) =
      ‖cfcHom hU (f p.1) ξ - cfcHom hU (f p.2) ξ‖ ^ 2 := by
    intro p
    simpa [normSqMap, map_sub, F] using integral_normSqMap U ξ (f p.1 - f p.2)
  simp_rw [heq] at hi
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simpa only [Function.comp_def, dist_eq_norm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

/-- A uniformly bounded convergent continuous approximation defines a bounded
operator, without a separability restriction on the Hilbert space. -/
theorem exists_strongLimit (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : spectrum ℂ U → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    ∃ T : Operator H, (∀ ξ, Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (T ξ))) ∧
      ‖T‖ ≤ C := by
  have hc := fun ξ => cauchySeq_calculus U f g C hC hb ht ξ
  choose T hT using fun ξ => cauchySeq_tendsto_of_complete (hc ξ)
  have hnorm : ∀ n, ‖cfcHom hU (f n)‖ ≤ C := by
    intro n
    rw [norm_cfcHom U (f n) hU]
    exact ((f n).norm_le hC).mpr (hb n)
  let L : Operator H := ContinuousLinearMap.ofTendstoOfBoundedRange T
    (fun n => cfcHom hU (f n)) (tendsto_pi_nhds.mpr hT)
    (isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨n, rfl⟩; exact hnorm n⟩)
  refine ⟨L, hT, ContinuousLinearMap.opNorm_le_bound L hC fun ξ => ?_⟩
  apply le_of_tendsto (hT ξ).norm
  exact Eventually.of_forall fun n =>
    (cfcHom hU (f n)).le_of_opNorm_le (hnorm n) ξ

theorem phase_exp (x : ℝ) :
    phase (Complex.exp (x * Complex.I)) = Int.fract (x / (2 * Real.pi)) := by
  rw [phase, Complex.arg_exp_mul_I]
  apply Int.fract_eq_fract.mpr
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  rw [← sub_div, toIocMod_sub_self]
  simp only [zsmul_eq_mul, Int.cast_neg]
  field_simp

theorem phase_exp_normalized (x : ℝ) :
    phase (Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)) = Int.fract x := by
  rw [phase_exp]
  congr 1
  field_simp

/-- A continuous triangular cutoff on the chosen angle interval. -/
def phaseTriangle (n : ℕ) (x : ℝ) : ℝ := min x ((n : ℝ) * (1 - x))

theorem continuous_phaseTriangle (n : ℕ) : Continuous (phaseTriangle n) := by
  unfold phaseTriangle
  fun_prop

@[simp] theorem phaseTriangle_zero (n : ℕ) : phaseTriangle n 0 = 0 := by
  simp [phaseTriangle]

@[simp] theorem phaseTriangle_one (n : ℕ) : phaseTriangle n 1 = 0 := by
  simp [phaseTriangle]

/-- Although phase is discontinuous, this clipped phase is continuous on the circle. -/
theorem continuous_clippedPhase (n : ℕ) :
    Continuous (fun z : Circle => phaseTriangle n (phase z)) := by
  apply (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff.mpr
  have hc : Continuous (phaseTriangle n ∘ Int.fract) :=
    (continuous_phaseTriangle n).continuousOn.comp_fract'' (by simp)
  simpa only [Function.comp_def, Circle.coe_exp, phase_exp, id_eq] using
    hc.comp (continuous_id.div_const (2 * Real.pi))

theorem phaseTriangle_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    0 ≤ phaseTriangle n x := by
  exact le_min hx (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hx'))

theorem phaseTriangle_le_self (n : ℕ) (x : ℝ) : phaseTriangle n x ≤ x := min_le_left _ _

theorem tendsto_phaseTriangle {x : ℝ} (hx : x < 1) :
    Tendsto (fun n => phaseTriangle n x) atTop (𝓝 x) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) * (1 - x)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos (by linarith) tendsto_const_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually (eventually_ge_atTop x)] with n hn
  exact (min_eq_left hn).symm

/-- Continuous lower approximations to phase on a unitary spectrum. -/
def phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H)) (n : ℕ) :
    C(spectrum ℂ U, ℝ) :=
  ⟨fun z => phaseTriangle n (phase z), by
    have hm : ∀ z : spectrum ℂ U, ‖(z : ℂ)‖ = 1 := fun z =>
      CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hU z.property)
    exact (continuous_clippedPhase n).comp (continuous_subtype_val.subtype_mk (fun z => mem_sphere_zero_iff_norm.mpr (hm z)))⟩

theorem phaseApprox_nonneg (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : 0 ≤ phaseApprox U hU n z :=
  phaseTriangle_nonneg n (phase_nonneg _) (phase_lt_one _).le

theorem phaseApprox_le_one (U : Operator H) (hU : U ∈ unitary (Operator H))
    (n : ℕ) (z : spectrum ℂ U) : phaseApprox U hU n z ≤ 1 :=
  (phaseTriangle_le_self n _).trans (phase_lt_one _).le

theorem tendsto_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (z : spectrum ℂ U) : Tendsto (fun n => phaseApprox U hU n z) atTop (𝓝 (phase z)) :=
  tendsto_phaseTriangle (phase_lt_one _)

theorem tendsto_integral_phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) : letI := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => ∫ z, phaseApprox U hU n z ∂vectorMeasure U ξ)
      atTop (𝓝 (vectorPhase U ξ)) := by
  let := isStarNormal_of_mem_unitary hU
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (phaseApprox U hU n).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseApprox_nonneg U hU n z)]
    exact phaseApprox_le_one U hU n z
  · exact Eventually.of_forall (tendsto_phaseApprox U hU)

/-- Exponentiating the chosen phase recovers a point on the unit circle. -/
theorem exp_phase {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp ((2 * Real.pi * phase z : ℝ) * Complex.I) = z := by
  have ha : 2 * Real.pi * phase z = z.arg - 2 * Real.pi *
      (Int.floor (z.arg / (2 * Real.pi)) : ℝ) := by
    unfold phase Int.fract
    field_simp
  change (Circle.exp (2 * Real.pi * phase z) : ℂ) = z
  rw [ha, Circle.exp_sub, Circle.exp_two_pi_mul_int, div_one]
  simpa only [hz, Complex.ofReal_one, one_mul, Circle.coe_exp] using
    Complex.norm_mul_exp_arg_mul_I z

/-- An already continuous pointwise limit is identified by the scalar measures. -/
theorem tendsto_calculus (U : Operator H) [hU : IsStarNormal U]
    (f : ℕ → C(spectrum ℂ U, ℂ)) (g : C(spectrum ℂ U, ℂ))
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
    (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
    Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (cfcHom hU g ξ)) := by
  have hgb : ∀ z, ‖g z‖ ≤ C := fun z =>
    le_of_tendsto (ht z).norm (Eventually.of_forall fun n => hb n z)
  have hbound : ∀ n z, ‖normSqMap (f n - g) z‖ ≤ (2 * C) ^ 2 := by
    intro n z
    have hd : ‖f n z - g z‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith [hb n z, hgb z])
    simp only [normSqMap, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
      Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hlim : ∀ z, Tendsto (fun n => normSqMap (f n - g) z) atTop (𝓝 0) := by
    intro z
    simpa [normSqMap, Function.comp_def] using Complex.continuous_normSq.continuousAt.tendsto.comp
      ((ht z).sub (tendsto_const_nhds (x := g z)))
  have hi : Tendsto (fun n => ∫ z, normSqMap (f n - g) z ∂vectorMeasure U ξ)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ => (2 * C) ^ 2)
      (fun n => (normSqMap (f n - g)).continuous.aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (hbound n))
      (Eventually.of_forall hlim)
  simp_rw [integral_normSqMap, map_sub, sub_apply] at hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

/-- Pointwise exponential of a continuous complex-valued function. -/
def expMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℂ) :=
  ⟨fun z => Complex.exp (f z), Complex.continuous_exp.comp f.continuous⟩

/-- The normed-ring exponential on continuous functions is pointwise. -/
theorem expMap_eq_exp {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ℂ)) : expMap f = NormedSpace.exp f := by
  ext z
  symm
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ,
    expMap, ContinuousMap.coe_mk] using
    (NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z) (continuous_eval_const z) f)

/-- The continuous functional calculus respects the operator exponential. -/
theorem calculus_expMap (U : Operator H) [hU : IsStarNormal U]
    (f : C(spectrum ℂ U, ℂ)) :
    cfcHom hU (expMap f) = NormedSpace.exp (cfcHom hU f) := by
  let : NormedAlgebra ℚ (Operator H) := NormedAlgebra.restrictScalars ℚ ℂ (Operator H)
  rw [expMap_eq_exp]
  exact NormedSpace.map_exp (cfcHom hU) (cfcHom_continuous hU) f

end KervaireSpectral

end

end OAI
