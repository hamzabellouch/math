import OAI.Probability.ClassicalON.Model

namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

@[simp] theorem spin_norm {n : ℕ} (s : Spin n) : ‖s.val‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp s.property

instance sphereProbability_isProbability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (sphereProbability n) := by
  have hs : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero _
  constructor
  dsimp [sphereProbability]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_eq_zero.not.mpr hs)
    (measure_ne_top _ _)

instance referenceLaw_isProbability (n : ℕ) [NeZero n] (G : LatticeGraph) :
    IsProbabilityMeasure (referenceLaw n G) := by
  unfold referenceLaw
  infer_instance

theorem continuous_interaction (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) :
    Continuous (interaction n G b) := by
  unfold interaction
  fun_prop

theorem continuous_spinDot (n : ℕ) (G : LatticeGraph) (x y : G.vertices) :
    Continuous (fun σ : Configuration n G => ⟪(σ x).val, (σ y).val⟫_ℝ) := by
  fun_prop

theorem integrable_weight (n : ℕ) [NeZero n] (G : LatticeGraph) (b : G.edges → ℝ) :
    Integrable (fun σ => Real.exp (interaction n G b σ)) (referenceLaw n G) := by
  exact (continuous_interaction n G b).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem partition_pos (n : ℕ) [NeZero n] (G : LatticeGraph) (b : G.edges → ℝ) :
    0 < partition n G b := by
  unfold partition
  apply (integral_pos_iff_support_of_nonneg
    (fun σ => (Real.exp_pos _).le) (integrable_weight n G b)).mpr
  have hs : Function.support (fun σ => Real.exp (interaction n G b σ)) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

theorem integrable_twoPoint (n : ℕ) [NeZero n] (G : LatticeGraph)
    (b : G.edges → ℝ) (x y : G.vertices) :
    Integrable (fun σ => ⟪(σ x).val, (σ y).val⟫_ℝ *
        Real.exp (interaction n G b σ)) (referenceLaw n G) := by
  exact ((continuous_spinDot n G x y).mul (continuous_interaction n G b).rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[simp] theorem correlation_self (n : ℕ) [NeZero n] (G : LatticeGraph)
    (b : G.edges → ℝ) (x : G.vertices) : correlation n G b x x = 1 := by
  unfold correlation
  have hd : ∀ σ : Configuration n G, ⟪(σ x).val, (σ x).val⟫_ℝ = 1 := by
    intro σ
    rw [real_inner_self_eq_norm_sq, spin_norm, one_pow]
  simp_rw [hd, one_mul]
  exact div_self (partition_pos n G b).ne'

theorem hasDerivAt_integral_compact
    {Ω : Type uΩ} {F : Type uF} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f fd : ℝ → Ω → F)
    (hf : Continuous (Function.uncurry f)) (hfd : Continuous (Function.uncurry fd))
    (hd : ∀ t ω, HasDerivAt (fun u => f u ω) (fd t ω) t) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, f u ω ∂μ) (∫ ω, fd t ω ∂μ) t := by
  have hi (u : ℝ) : Integrable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdi (u : ℝ) : Integrable (fd u) μ :=
    (hfd.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := (((isCompact_closedBall t 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set Ω))).image hfd).isBounded.exists_norm_le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hi u).aestronglyMeasurable)
    (hi t) (hdi t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω u hu => hC _ ⟨(u, ω), ⟨hu, Set.mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω u _ => hd u ω)).2

def spinRotation {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Spin n ≃ₜ Spin n :=
  R.toHomeomorph.subtype fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖R x‖ = 1
    rw [R.norm_map]

@[simp] theorem spinRotation_val {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (s : Spin n) :
    (spinRotation R s).val = R s.val := rfl

theorem spinRotation_preserves_surface {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  open scoped Pointwise in
  refine ⟨(spinRotation R).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (spinRotation R).measurable hs,
    Measure.toSphere_apply' _ ((spinRotation R).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((spinRotation R) ⁻¹' s)) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext v
    constructor
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨r, hr, R t.val, ⟨spinRotation R t, ht, rfl⟩, (R.map_smul r t.val).symm⟩
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, hv⟩
      refine ⟨r, hr, R.symm t.val, ⟨(spinRotation R).symm t, ?_, rfl⟩, ?_⟩
      · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using ht
      · apply R.injective
        simpa only [map_smul, LinearIsometryEquiv.apply_symm_apply] using hv
  rw [hcone]
  have hm := R.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map R volume) _ = volume (R ⁻¹' _) at hm
  rw [R.measurePreserving.map_eq] at hm
  exact hm.symm

theorem spinRotation_preserves_probability {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R) (sphereProbability n) (sphereProbability n) :=
  (spinRotation_preserves_surface R).smul_measure _

def siteReference (n : ℕ) (p : Option (Spin n)) : Measure (Spin n) :=
  match p with
  | none => sphereProbability n
  | some s => Measure.dirac s

instance siteReference_isProbability (n : ℕ) [NeZero n] (p : Option (Spin n)) :
    IsProbabilityMeasure (siteReference n p) := by
  cases p <;> dsimp [siteReference] <;> infer_instance

structure SpinSystem (n : ℕ) (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  strength : E → ℝ
  pin : V → Option (Spin n)

abbrev SpinOperator (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

instance spinOperator_completeSpace (dimension : ℕ) : CompleteSpace (SpinOperator dimension) :=
  ContinuousLinearMap.instCompleteSpace

instance spinOperator_ratNormedAlgebra (n : ℕ) : NormedAlgebra ℚ (SpinOperator n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def rotationExp {n : ℕ} (A : SpinOperator n) (hA : A ∈ skewAdjoint (SpinOperator n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Unitary.linearIsometryEquiv
    ⟨NormedSpace.exp A, NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hA⟩

@[simp] theorem rotationExp_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    rotationExp A hA v = NormedSpace.exp A v := rfl

@[simp] theorem rotationExp_symm_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    (rotationExp A hA).symm v = NormedSpace.exp (-A) v := by
  change (star (NormedSpace.exp A)) v = _
  rw [NormedSpace.star_exp, skewAdjoint.mem_iff.mp hA]

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def reference (S : SpinSystem n V E) : Measure (V → Spin n) :=
  Measure.pi (fun x => siteReference n (S.pin x))

instance reference_isProbability [NeZero n] (S : SpinSystem n V E) :
    IsProbabilityMeasure S.reference := by
  unfold reference
  infer_instance

def energy (S : SpinSystem n V E) (K : E → SpinOperator n) (σ : V → Spin n) : ℝ :=
  ∑ e, S.strength e * ⟪(σ (S.left e)).val, K e (σ (S.right e)).val⟫_ℝ

def Z (S : SpinSystem n V E) (K : E → SpinOperator n) : ℝ :=
  ∫ σ, Real.exp (S.energy K σ) ∂S.reference

omit [Fintype V] in
theorem continuous_energy (S : SpinSystem n V E) (K : E → SpinOperator n) :
    Continuous (S.energy K) := by
  unfold energy
  fun_prop

theorem integrable_weight [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    Integrable (fun σ => Real.exp (S.energy K σ)) S.reference :=
  (S.continuous_energy K).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem Z_pos [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    0 < S.Z K := by
  unfold Z
  apply (integral_pos_iff_support_of_nonneg
    (fun σ => (Real.exp_pos _).le) (S.integrable_weight K)).mpr
  have hs : Function.support (fun σ => Real.exp (S.energy K σ)) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

def rotateConfiguration
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (V → Spin n) ≃ₜ (V → Spin n) :=
  Homeomorph.piCongrRight (fun x => spinRotation (U x))

def rotatePins (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    SpinSystem n V E :=
  { S with pin := fun x => (S.pin x).map (spinRotation (U x)) }

def gauge (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    E → SpinOperator n :=
  fun e => (U (S.left e)).symm.toContinuousLinearEquiv.toContinuousLinearMap * K e *
    (U (S.right e)).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fintype E] in
theorem rotateConfiguration_preserves_reference [NeZero n] (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (rotateConfiguration U) S.reference (S.rotatePins U).reference := by
  change MeasurePreserving (fun σ x => spinRotation (U x) (σ x))
    (Measure.pi (fun x => siteReference n (S.pin x)))
    (Measure.pi (fun x => siteReference n ((S.pin x).map (spinRotation (U x)))))
  apply measurePreserving_pi
  intro x
  cases S.pin x with
  | none => exact spinRotation_preserves_probability (U x)
  | some s =>
    exact ⟨(spinRotation (U x)).measurable, Measure.map_dirac s⟩

omit [Fintype V] in
theorem energy_gauge (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : V → Spin n) :
    S.energy (S.gauge K U) σ = (S.rotatePins U).energy K (rotateConfiguration U σ) := by
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  change ⟪(σ (S.left e)).val,
      (U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val))⟫_ℝ =
    ⟪U (S.left e) (σ (S.left e)).val, K e (U (S.right e) (σ (S.right e)).val)⟫_ℝ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    ((U (S.left e)).inner_map_map (σ (S.left e)).val
      ((U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val)))).symm

theorem Z_gauge [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    S.Z (S.gauge K U) = (S.rotatePins U).Z K := by
  unfold Z
  simp_rw [energy_gauge]
  exact (S.rotateConfiguration_preserves_reference U).integral_comp
    (rotateConfiguration U).measurableEmbedding
    (fun σ => Real.exp ((S.rotatePins U).energy K σ))

omit [Fintype V] [Fintype E] in

theorem rotatePins_eq_self (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.rotatePins U = S := by
  suffices hp : (fun x => (S.pin x).map (spinRotation (U x))) = S.pin by
    unfold rotatePins
    rw [hp]
  funext x
  cases h : S.pin x with
  | none => rfl
  | some s => simp only [Option.map_some, hU x s h]

theorem Z_gauge_of_fixes_pins [NeZero n] (S : SpinSystem n V E)
    (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.Z (S.gauge K U) = S.Z K := by
  rw [S.Z_gauge K U, S.rotatePins_eq_self U hU]

def W (S : SpinSystem n V E) (A : E → SpinOperator n) : ℝ :=
  S.Z (fun e => NormedSpace.exp (A e)) / S.Z (fun _ => 1)

@[simp] theorem W_zero [NeZero n] (S : SpinSystem n V E) : S.W 0 = 1 := by
  simp only [W, Pi.zero_apply, NormedSpace.exp_zero]
  exact div_self (S.Z_pos _).ne'

def gaugeProduct (S : SpinSystem n V E) (F : V → SpinOperator n) : E → SpinOperator n :=
  fun e => NormedSpace.exp (F (S.left e)) *
    NormedSpace.exp (F (S.right e) - F (S.left e)) *
    NormedSpace.exp (-F (S.right e))

theorem noncommuting_gauge [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.Z (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) =
      S.Z (S.gaugeProduct F) := by
  let U := fun x => rotationExp (-F x) ((skewAdjoint _).neg_mem (hF x))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-F x) s.val = s.val
    rw [hP x s hs, neg_zero, NormedSpace.exp_zero]
    rfl
  have hg : S.gauge (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) U =
      S.gaugeProduct F := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp (F (S.right e) - F (S.left e)) (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg,
      gaugeProduct, mul_apply_eq_comp]
  rw [← hg]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

def twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) : ℝ :=
  S.energy (fun e => NormedSpace.exp (t • A e) * A e ^ k) σ

omit [Fintype V] in
theorem continuous_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) : Continuous (Function.uncurry (S.twistEnergy A k)) := by
  unfold twistEnergy energy Function.uncurry
  fun_prop

omit [Fintype V] in
theorem hasDerivAt_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.twistEnergy A k u σ) (S.twistEnergy A (k+1) t σ) t := by
  unfold twistEnergy energy
  have he (e : E) : HasDerivAt
      (fun u => NormedSpace.exp (u • A e) * A e ^ k)
      (NormedSpace.exp (t • A e) * A e ^ (k+1)) t := by
    exact ((hasDerivAt_exp_smul_const (A e) t).mul_const (A e ^ k)).congr_deriv
      (by rw [pow_succ', mul_assoc])
  apply HasDerivAt.fun_sum
  intro e _
  exact (((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((he e).clm_apply (hasDerivAt_const t (σ (S.right e)).val))).const_mul
      (S.strength e)).congr_deriv (by simp)

def firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) * S.twistEnergy A 1 t σ

def secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 2 t σ + (S.twistEnergy A 1 t σ)^2)

omit [Fintype V] in
theorem continuous_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.firstWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul (S.continuous_twistEnergy A 1)

omit [Fintype V] in
theorem continuous_secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.secondWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    ((S.continuous_twistEnergy A 2).add ((S.continuous_twistEnergy A 1).pow 2))

omit [Fintype V] in
theorem hasDerivAt_weight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A t σ) t := by
  exact (S.hasDerivAt_twistEnergy A 0 t σ).exp

omit [Fintype V] in
theorem hasDerivAt_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.firstWeight A u σ) (S.secondWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul (S.hasDerivAt_twistEnergy A 1 t σ)).congr_deriv
    (by unfold firstWeight secondWeight; ring)

theorem hasDerivAt_twistZ [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => S.Z (fun e => NormedSpace.exp (u • A e)))
      (∫ σ, S.firstWeight A t σ ∂S.reference) t := by
  simpa only [twistEnergy, pow_zero, mul_one, Z] using
    hasDerivAt_integral_compact S.reference
      (fun u σ => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A)
      (S.continuous_twistEnergy A 0).rexp (S.continuous_firstWeight A)
      (S.hasDerivAt_weight A) t

theorem hasDerivAt_firstVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.firstWeight A u σ ∂S.reference)
      (∫ σ, S.secondWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.firstWeight A) (S.secondWeight A)
    (S.continuous_firstWeight A) (S.continuous_secondWeight A)
    (S.hasDerivAt_firstWeight A) t

def thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 3 t σ + 3 * S.twistEnergy A 1 t σ * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^3)

def fourthWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 4 t σ + 4 * S.twistEnergy A 1 t σ * S.twistEnergy A 3 t σ +
      3 * (S.twistEnergy A 2 t σ)^2 +
      6 * (S.twistEnergy A 1 t σ)^2 * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^4)

omit [Fintype V] in
theorem continuous_thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.thirdWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((S.continuous_twistEnergy A 3).add
      (((S.continuous_twistEnergy A 1).const_mul 3).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 3))

omit [Fintype V] in
theorem continuous_fourthWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.fourthWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((((S.continuous_twistEnergy A 4).add
      (((S.continuous_twistEnergy A 1).const_mul 4).mul
        (S.continuous_twistEnergy A 3))).add
      (((S.continuous_twistEnergy A 2).pow 2).const_mul 3)).add
      ((((S.continuous_twistEnergy A 1).pow 2).const_mul 6).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 4))

omit [Fintype V] in
theorem hasDerivAt_secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.secondWeight A u σ) (S.thirdWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    ((S.hasDerivAt_twistEnergy A 2 t σ).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 2))).congr_deriv
    (by dsimp [firstWeight, thirdWeight]; ring)

omit [Fintype V] in
theorem hasDerivAt_thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.thirdWeight A u σ) (S.fourthWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    (((S.hasDerivAt_twistEnergy A 3 t σ).add
      (((S.hasDerivAt_twistEnergy A 1 t σ).const_mul 3).mul
        (S.hasDerivAt_twistEnergy A 2 t σ))).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 3))).congr_deriv
    (by dsimp [firstWeight, fourthWeight]; ring)

theorem hasDerivAt_secondVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.secondWeight A u σ ∂S.reference)
      (∫ σ, S.thirdWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.secondWeight A) (S.thirdWeight A)
    (S.continuous_secondWeight A) (S.continuous_thirdWeight A)
    (S.hasDerivAt_secondWeight A) t

theorem hasDerivAt_thirdVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.thirdWeight A u σ ∂S.reference)
      (∫ σ, S.fourthWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.thirdWeight A) (S.fourthWeight A)
    (S.continuous_thirdWeight A) (S.continuous_fourthWeight A)
    (S.hasDerivAt_thirdWeight A) t

omit [Fintype V] [Fintype E] in

theorem exp_smul_add (g : SpinOperator n) (r s : ℝ) :
    NormedSpace.exp ((r+s) • g) = NormedSpace.exp (r • g) * NormedSpace.exp (s • g) := by
  rw [add_smul r s g]
  apply NormedSpace.exp_add_of_commute
  change (r • g) * (s • g) = (s • g) * (r • g)
  rw [Algebra.smul_mul_assoc r g (s • g), Algebra.mul_smul_comm s g g,
    smul_smul r s (g*g), Algebra.smul_mul_assoc s g (r • g),
    Algebra.mul_smul_comm r g g, smul_smul s r (g*g), mul_comm r s]

theorem W_add_gradient [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (h : E → ℝ) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (h e + f (S.right e) - f (S.left e)) • g) =
      S.W (fun e => h e • g) := by
  let U := fun x => rotationExp (-(f x • g)) ((skewAdjoint _).neg_mem (skewAdjoint.smul_mem _ hg))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-(f x • g)) s.val = s.val
    rw [hP x s hs, zero_smul ℝ g, neg_zero, NormedSpace.exp_zero]
    rfl
  have hK : S.gauge
      (fun e => NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)) U =
      (fun e => NormedSpace.exp (h e • g)) := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)
        (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← neg_smul (f (S.right e)) g,
      ← exp_smul_add,
      ← exp_smul_add]
    have hc : f (S.left e) + (h e + f (S.right e) - f (S.left e)) + -f (S.right e) =
        h e := by ring
    rw [hc]
  unfold W
  congr 1
  rw [← hK]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

theorem W_gradient [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (f (S.right e) - f (S.left e)) • g) = 1 := by
  have h := S.W_add_gradient g hg 0 f hP
  simp only [Pi.zero_apply, zero_add, zero_smul ℝ g] at h
  exact h.trans (S.W_zero)

def average (S : SpinSystem n V E) (f : (V → Spin n) → ℝ) : ℝ :=
  (∫ σ, f σ * Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1)

theorem integrable_average_integrand [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℝ} (hf : Continuous f) :
    Integrable (fun σ => f σ * Real.exp (S.energy (fun _ => 1) σ)) S.reference :=
  (hf.mul (S.continuous_energy _).rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[simp] theorem average_const [NeZero n] (S : SpinSystem n V E) (c : ℝ) :
    S.average (fun _ => c) = c := by
  unfold average
  rw [integral_const_mul]
  change c * S.Z (fun _ => 1) / S.Z (fun _ => 1) = c
  exact mul_div_cancel_right₀ c (S.Z_pos _).ne'

theorem average_add [NeZero n] (S : SpinSystem n V E)
    {f g : (V → Spin n) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    S.average (f+g) = S.average f + S.average g := by
  unfold average
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (S.integrable_average_integrand hf)
    (S.integrable_average_integrand hg), add_div]

theorem average_mono [NeZero n] (S : SpinSystem n V E)
    {f g : (V → Spin n) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ σ, f σ ≤ g σ) : S.average f ≤ S.average g := by
  apply div_le_div_of_nonneg_right _ (S.Z_pos _).le
  apply integral_mono (S.integrable_average_integrand hf) (S.integrable_average_integrand hg)
  intro σ
  exact mul_le_mul_of_nonneg_right (hfg σ) (Real.exp_pos _).le

theorem average_nonneg [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.average f :=
  div_nonneg (integral_nonneg fun σ => mul_nonneg (hf σ) (Real.exp_pos _).le) (S.Z_pos _).le

omit [Fintype V] [Fintype E] in

def axisGradient (S : SpinSystem n V E) (f : V → ℝ) (g : SpinOperator n) : E → SpinOperator n :=
  fun e => (f (S.right e) - f (S.left e)) • g

theorem Z_gradient_line [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) (t : ℝ) :
    S.Z (fun e => NormedSpace.exp (t • S.axisGradient f g e)) = S.Z (fun _ => 1) := by
  have hp : ∀ x s, S.pin x = some s → t * f x = 0 := by
    intro x s hs
    rw [hP x s hs, mul_zero]
  have h := S.W_gradient g hg (fun x => t * f x) hp
  unfold W at h
  have ha : (fun e => (t * f (S.right e) - t * f (S.left e)) • g) =
      (fun e => t • S.axisGradient f g e) := by
    funext e
    simp only [axisGradient, smul_smul, mul_sub]
  rw [ha] at h
  exact (div_eq_one_iff_eq (S.Z_pos _).ne').mp h

theorem second_gradient_identity [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => S.energy (fun e => S.axisGradient f g e ^ 2) σ +
      (S.energy (S.axisGradient f g) σ)^2) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (∫ σ, S.secondWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_firstVariation A 0
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const 0 0)
  unfold average
  have hfun : (fun σ => (S.energy (fun e => A e ^ 2) σ + (S.energy A σ)^2) *
      Real.exp (S.energy (fun _ => 1) σ)) = (fun σ => S.secondWeight A 0 σ) := by
    funext σ
    have hz (e : E) : (0:ℝ) • A e = 0 := zero_smul ℝ (A e)
    simp only [secondWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul,
      pow_zero, pow_one]
    exact mul_comm _ _
  change (∫ σ, (S.energy (fun e => A e ^ 2) σ + (S.energy A σ)^2) *
    Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1) = 0
  rw [hfun, hsecond, zero_div]

omit [Fintype V] in

theorem abs_energy_le (S : SpinSystem n V E) (K : E → SpinOperator n)
    (σ : V → Spin n) : |S.energy K σ| ≤ ∑ e, |S.strength e| * ‖K e‖ := by
  unfold energy
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |⟪(σ (S.left e)).val, K e (σ (S.right e)).val⟫_ℝ| ≤
        ‖(σ (S.left e)).val‖ * ‖K e (σ (S.right e)).val‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖(σ (S.left e)).val‖ * (‖K e‖ * ‖(σ (S.right e)).val‖) :=
      mul_le_mul_of_nonneg_left ((K e).le_opNorm _) (norm_nonneg _)
    _ = ‖K e‖ := by simp

omit [Fintype V] in

theorem abs_axis_secondEnergy_le (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (h : E → ℝ) (g : SpinOperator n) (hg : ‖g‖ ≤ 1) (σ : V → Spin n) :
    |S.energy (fun e => (h e • g)^2) σ| ≤ β * ∑ e, (h e)^2 := by
  apply (S.abs_energy_le _ σ).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [abs_of_nonneg (hb e).1]
  have hA : ‖h e • g‖ ≤ |h e| := by
    rw [norm_smul (h e) g, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hg
  have hp : ‖(h e • g)^2‖ ≤ (h e)^2 := by
    calc
      ‖(h e • g)^2‖ ≤ ‖h e • g‖^2 := by simpa only [pow_two] using norm_mul_le (h e • g) (h e • g)
      _ ≤ |h e|^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
      _ = (h e)^2 := sq_abs _
  exact mul_le_mul (hb e).2 hp (norm_nonneg _) ((hb e).1.trans (hb e).2)

theorem gradient_current_bound [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (g : SpinOperator n) (hg : g ∈ skewAdjoint (SpinOperator n)) (hgn : ‖g‖ ≤ 1)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => (S.energy (S.axisGradient f g) σ)^2) ≤
      β * ∑ e, (f (S.right e) - f (S.left e))^2 := by
  let A := S.axisGradient f g
  let C := β * ∑ e, (f (S.right e) - f (S.left e))^2
  have hc1 := (S.continuous_energy A).pow 2
  have hc2 := (S.continuous_energy (fun e => A e^2)).add hc1
  have hbound (σ : V → Spin n) : (S.energy A σ)^2 ≤
      (S.energy (fun e => A e^2) σ + (S.energy A σ)^2) + C := by
    have hh := (abs_le.mp (S.abs_axis_secondEnergy_le β hb
      (fun e => f (S.right e) - f (S.left e)) g hgn σ)).1
    change -C ≤ S.energy (fun e => A e^2) σ at hh
    linarith
  have h := S.average_mono hc1 (hc2.add continuous_const) hbound
  rw [S.average_add hc2 continuous_const, S.average_const] at h
  have hi := S.second_gradient_identity g hg f hP
  change S.average (fun σ => S.energy (fun e => A e^2) σ + (S.energy A σ)^2) = 0 at hi
  change S.average (fun σ => (S.energy A σ)^2) ≤
    S.average (fun σ => S.energy (fun e => A e^2) σ + (S.energy A σ)^2) + C at h
  rw [hi, zero_add] at h
  exact h

end SpinSystem

def fourthBell {Ω : Type uΩ} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (F 0 t ω) * (F 4 t ω + 4 * F 1 t ω * F 3 t ω + 3 * (F 2 t ω)^2 +
    6 * (F 1 t ω)^2 * F 2 t ω + (F 1 t ω)^4)

theorem iteratedDeriv_four_integral_exp
    {Ω : Type uΩ} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → ℝ → Ω → ℝ)
    (hC : ∀ k, Continuous (Function.uncurry (F k)))
    (hD : ∀ k t ω, HasDerivAt (fun u => F k u ω) (F (k+1) t ω) t) (t : ℝ) :
    iteratedDeriv 4 (fun u => ∫ ω, Real.exp (F 0 u ω) ∂μ) t =
      ∫ ω, fourthBell F t ω ∂μ := by
  let w0 := fun u ω => Real.exp (F 0 u ω)
  let w1 := fun u ω => Real.exp (F 0 u ω) * F 1 u ω
  let w2 := fun u ω => Real.exp (F 0 u ω) * (F 2 u ω + (F 1 u ω)^2)
  let w3 := fun u ω => Real.exp (F 0 u ω) *
    (F 3 u ω + 3 * F 1 u ω * F 2 u ω + (F 1 u ω)^3)
  let w4 := fourthBell F
  have c0 : Continuous (Function.uncurry w0) := (hC 0).rexp
  have c1 : Continuous (Function.uncurry w1) := (hC 0).rexp.mul (hC 1)
  have c2 : Continuous (Function.uncurry w2) :=
    (hC 0).rexp.mul ((hC 2).add ((hC 1).pow 2))
  have c3 : Continuous (Function.uncurry w3) := (hC 0).rexp.mul
    (((hC 3).add (((hC 1).const_mul 3).mul (hC 2))).add ((hC 1).pow 3))
  have c4 : Continuous (Function.uncurry w4) := (hC 0).rexp.mul
    (((((hC 4).add (((hC 1).const_mul 4).mul (hC 3))).add
      (((hC 2).pow 2).const_mul 3)).add ((((hC 1).pow 2).const_mul 6).mul
        (hC 2))).add ((hC 1).pow 4))
  have d0 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w0 v ω) (w1 u ω) u := (hD 0 u ω).exp
  have d1 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w1 v ω) (w2 u ω) u :=
    ((d0 u ω).mul (hD 1 u ω)).congr_deriv (by dsimp [w0, w1, w2]; ring)
  have d2 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w2 v ω) (w3 u ω) u :=
    ((d0 u ω).mul ((hD 2 u ω).add ((hD 1 u ω).pow 2))).congr_deriv
      (by dsimp [w0, w1, w3]; ring)
  have d3 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w3 v ω) (w4 u ω) u :=
    ((d0 u ω).mul (((hD 3 u ω).add (((hD 1 u ω).const_mul 3).mul
      (hD 2 u ω))).add ((hD 1 u ω).pow 3))).congr_deriv
      (by dsimp [w0, w1, w4, fourthBell]; ring)
  have e0 : deriv (fun u => ∫ ω, w0 u ω ∂μ) = (fun u => ∫ ω, w1 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w0 w1 c0 c1 d0 u).deriv
  have e1 : deriv (fun u => ∫ ω, w1 u ω ∂μ) = (fun u => ∫ ω, w2 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w1 w2 c1 c2 d1 u).deriv
  have e2 : deriv (fun u => ∫ ω, w2 u ω ∂μ) = (fun u => ∫ ω, w3 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w2 w3 c2 c3 d2 u).deriv
  have e3 : deriv (fun u => ∫ ω, w3 u ω ∂μ) = (fun u => ∫ ω, w4 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w3 w4 c3 c4 d3 u).deriv
  change iteratedDeriv 4 (fun u => ∫ ω, w0 u ω ∂μ) t = ∫ ω, w4 t ω ∂μ
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, e0, e1, e2, e3]

def expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) : SpinOperator n :=
  NormedSpace.exp (t • X) * X^a

theorem hasDerivAt_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) :
    HasDerivAt (expPower X a) (expPower X (a+1) t) t := by
  exact ((hasDerivAt_exp_smul_const X t).mul_const (X^a)).congr_deriv
    (by simp only [expPower, pow_succ', mul_assoc])

theorem continuous_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    Continuous (expPower X a) := by
  unfold expPower
  fun_prop

def tripleJet {n : ℕ} (X Y Z : SpinOperator n) : ℕ → ℕ → ℕ → ℕ → ℝ → SpinOperator n
  | 0, a, b, c, t => expPower X a t * expPower Y b t * expPower Z c t
  | k+1, a, b, c, t => tripleJet X Y Z k (a+1) b c t +
      tripleJet X Y Z k a (b+1) c t + tripleJet X Y Z k a b (c+1) t

theorem continuous_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) : Continuous (tripleJet X Y Z k a b c) := by
  induction k generalizing a b c with
  | zero => exact ((continuous_expPower X a).mul (continuous_expPower Y b)).mul (continuous_expPower Z c)
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

theorem hasDerivAt_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) (t : ℝ) :
    HasDerivAt (tripleJet X Y Z k a b c) (tripleJet X Y Z (k+1) a b c t) t := by
  induction k generalizing a b c with
  | zero =>
    exact (((hasDerivAt_expPower X a t).mul (hasDerivAt_expPower Y b t)).mul
      (hasDerivAt_expPower Z c t)).congr_deriv (by dsimp [tripleJet]; rw [add_mul, add_assoc])
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

@[simp] theorem expPower_zero {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    expPower X a 0 = X^a := by
  rw [expPower, zero_smul ℝ X, NormedSpace.exp_zero, one_mul]

theorem gaugeJets_zero_one {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 0 0 0 0 0 = 1 ∧
    tripleJet X (Y-X) (-Y) 1 0 0 0 0 = 0 := by
  simp [tripleJet]

theorem gaugeJet_two {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 2 0 0 0 0 = X*Y-Y*X := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [tripleJet, expPower_zero, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one, pow_two,
    add_apply, sub_apply, neg_apply, mul_apply_eq_comp, map_sub, map_neg]
  abel

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) : ℝ :=
  S.energy (fun e => tripleJet (F (S.left e))
    (F (S.right e)-F (S.left e)) (-F (S.right e)) k 0 0 0 t) σ

omit [Fintype V] in
theorem continuous_gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n) (k : ℕ) :
    Continuous (Function.uncurry (S.gaugeEnergy F k)) := by
  unfold gaugeEnergy energy
  apply continuous_finsetSum
  intro e _
  exact continuous_const.mul
    (((continuous_apply (S.left e)).comp continuous_snd).subtype_val.inner
      (((continuous_tripleJet _ _ _ k 0 0 0).comp continuous_fst).clm_apply
        (((continuous_apply (S.right e)).comp continuous_snd).subtype_val)))

omit [Fintype V] in
theorem hasDerivAt_gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.gaugeEnergy F k u σ) (S.gaugeEnergy F (k+1) t σ) t := by
  unfold gaugeEnergy energy
  apply HasDerivAt.fun_sum
  intro e _
  exact (((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((hasDerivAt_tripleJet _ _ _ k 0 0 0 t).clm_apply
      (hasDerivAt_const t (σ (S.right e)).val))).const_mul
        (S.strength e)).congr_deriv (by simp)

omit [Fintype V] in
@[simp] theorem energy_zero (S : SpinSystem n V E) (σ : V → Spin n) :
    S.energy 0 σ = 0 := by simp [energy]

omit [Fintype V] in
theorem gaugeEnergy_at_zero (S : SpinSystem n V E) (F : V → SpinOperator n)
    (σ : V → Spin n) :
    S.gaugeEnergy F 0 0 σ = S.energy (fun _ => 1) σ ∧
    S.gaugeEnergy F 1 0 σ = 0 ∧
    S.gaugeEnergy F 2 0 σ = S.energy
      (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ := by
  have h0 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).1
  have h1 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).2
  simp only [gaugeEnergy, h0, h1, gaugeJet_two]
  exact ⟨True.intro, S.energy_zero σ, True.intro⟩

theorem fourth_noncommuting_identity [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    (∫ σ, S.fourthWeight (fun e => F (S.right e)-F (S.left e)) 0 σ ∂S.reference) =
      ∫ σ, Real.exp (S.energy (fun _ => 1) σ) *
        (S.gaugeEnergy F 4 0 σ + 3 * (S.energy
          (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2)
        ∂S.reference := by
  let A : E → SpinOperator n := fun e => F (S.right e)-F (S.left e)
  have heq : (fun t => ∫ σ, Real.exp (S.twistEnergy A 0 t σ) ∂S.reference) =
      (fun t => ∫ σ, Real.exp (S.gaugeEnergy F 0 t σ) ∂S.reference) := by
    funext t
    have htP : ∀ x s, S.pin x = some s → t • F x = 0 := by
      intro x s hs
      rw [hP x s hs]
      exact smul_zero (M := ℝ) (A := SpinOperator n) t
    have h := S.noncommuting_gauge (fun x => t • F x)
      (fun x => skewAdjoint.smul_mem t (hF x)) htP
    have hd (e : E) : t • F (S.right e) - t • F (S.left e) = t • A e :=
      (smul_sub t (F (S.right e)) (F (S.left e))).symm
    have hGP : S.gaugeProduct (fun x => t • F x) =
        (fun e => tripleJet (F (S.left e)) (F (S.right e)-F (S.left e))
          (-F (S.right e)) 0 0 0 0 t) := by
      funext e
      change NormedSpace.exp (t • F (S.left e)) *
        NormedSpace.exp (t • F (S.right e) - t • F (S.left e)) *
        NormedSpace.exp (-(t • F (S.right e))) = _
      rw [hd]
      simp only [tripleJet, expPower, pow_zero, mul_one]
      rw [smul_neg t (F (S.right e))]
    rw [hGP] at h
    simpa only [Z, twistEnergy, pow_zero, mul_one, gaugeEnergy, hd] using h
  have hl := iteratedDeriv_four_integral_exp S.reference (S.twistEnergy A)
    (S.continuous_twistEnergy A) (S.hasDerivAt_twistEnergy A) 0
  have hr := iteratedDeriv_four_integral_exp S.reference (S.gaugeEnergy F)
    (S.continuous_gaugeEnergy F) (S.hasDerivAt_gaugeEnergy F) 0
  rw [heq, hr] at hl
  refine hl.symm.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro σ
  have hz := S.gaugeEnergy_at_zero F σ
  simp [fourthBell, hz.1, hz.2.1, hz.2.2]

end SpinSystem

open scoped Matrix

def matrixOperator {n : ℕ} : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] SpinOperator n :=
  (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℝ (Fin n))).trans
    (Module.End.toContinuousLinearMap (EuclideanSpace ℝ (Fin n)))
theorem matrixOperator_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    matrixOperator M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  change (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n)) M) v = _
  rw [← Matrix.toLpLin_eq_toLin, Matrix.toLpLin_apply]

def axisMatrixA : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,0; 0,0,-1; 0,1,0]
def axisMatrixB : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,1; 0,0,0; -1,0,0]
def axisMatrixC : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0; 1,0,0; 0,0,0]
def axisA : SpinOperator 3 := matrixOperator axisMatrixA
def axisB : SpinOperator 3 := matrixOperator axisMatrixB
def axisC : SpinOperator 3 := matrixOperator axisMatrixC

theorem axisA_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisA v = WithLp.toLp 2 ![0, -v 2, v 1] := by
  rw [axisA, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem matrixOperator_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    star (matrixOperator M) = matrixOperator M.transpose := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    matrixOperator_apply, matrixOperator_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem axisA_skew : axisA ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisA, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA]

theorem axisA_norm_le : ‖axisA‖ ≤ 1 := by
  apply axisA.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisA_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 0‖]

theorem axisB_skew : axisB ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisB, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixB]

theorem axisC_skew : axisC ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisC, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixC]

theorem axisB_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisB v = WithLp.toLp 2 ![v 2, 0, -v 0] := by
  rw [axisB, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem axisC_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisC v = WithLp.toLp 2 ![-v 1, v 0, 0] := by
  rw [axisC, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem axisB_norm_le : ‖axisB‖ ≤ 1 := by
  apply axisB.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisB_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 1‖]

theorem axisC_norm_le : ‖axisC‖ ≤ 1 := by
  apply axisC.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisC_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 2‖]

def tripleMoment {R : Type uR} [Ring R] (X Y Z : R) : ℕ → ℕ → ℕ → ℕ → R
  | 0, a, b, c => X^a * Y^b * Z^c
  | k+1, a, b, c => tripleMoment X Y Z k (a+1) b c +
      tripleMoment X Y Z k a (b+1) c + tripleMoment X Y Z k a b (c+1)

theorem tripleMoment_four {R : Type uR} [Ring R] (X Y Z : R) :
    tripleMoment X Y Z 4 0 0 0 = X^4+Y^4+Z^4 +
      4 • (X^3*Y+X^3*Z+X*Y^3+Y^3*Z+X*Z^3+Y*Z^3) +
      6 • (X^2*Y^2+X^2*Z^2+Y^2*Z^2) +
      12 • (X^2*Y*Z+X*Y^2*Z+X*Y*Z^2) := by
  simp only [tripleMoment, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one]
  noncomm_ring

def plane (f g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,g; 0,0,-f; -g,f,0]
def third : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0; 1,0,0; 0,0,0]

lemma plane_sub (f g h k : ℝ) : plane f g - plane h k = plane (f-h) (g-k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane] <;> ring
lemma plane_neg (f g : ℝ) : -plane f g = plane (-f) (-g) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane]

def moment4Plane (f g h k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  tripleMoment (plane f g) (plane h k - plane f g) (-plane h k) 4 0 0 0

@[simp] lemma moment4_plane_even_00 (f g h k : ℝ) :
    moment4Plane f g h k 0 0 + moment4Plane f (-g) h (-k) 0 0 = -6 * (f*k-g*h)^2 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]
  ring

@[simp] lemma moment4_plane_even_01 (f g h k : ℝ) :
    moment4Plane f g h k 0 1 + moment4Plane f (-g) h (-k) 0 1 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]
  ring

@[simp] lemma moment4_plane_even_02 (f g h k : ℝ) :
    moment4Plane f g h k 0 2 + moment4Plane f (-g) h (-k) 0 2 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]

@[simp] lemma moment4_plane_even_10 (f g h k : ℝ) :
    moment4Plane f g h k 1 0 + moment4Plane f (-g) h (-k) 1 0 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]
  ring

@[simp] lemma moment4_plane_even_11 (f g h k : ℝ) :
    moment4Plane f g h k 1 1 + moment4Plane f (-g) h (-k) 1 1 = -6 * (f*k-g*h)^2 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]
  ring

@[simp] lemma moment4_plane_even_12 (f g h k : ℝ) :
    moment4Plane f g h k 1 2 + moment4Plane f (-g) h (-k) 1 2 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]

@[simp] lemma moment4_plane_even_20 (f g h k : ℝ) :
    moment4Plane f g h k 2 0 + moment4Plane f (-g) h (-k) 2 0 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]

@[simp] lemma moment4_plane_even_21 (f g h k : ℝ) :
    moment4Plane f g h k 2 1 + moment4Plane f (-g) h (-k) 2 1 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]

@[simp] lemma moment4_plane_even_22 (f g h k : ℝ) :
    moment4Plane f g h k 2 2 + moment4Plane f (-g) h (-k) 2 2 = 0 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  norm_num [plane, pow_succ, Matrix.cons_val_two]
  ring

lemma moment4_plane_even (f g h k : ℝ) :
    moment4Plane f g h k + moment4Plane f (-g) h (-k) =
      (6 * (f*k-g*h)^2) • third^2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [third, pow_two, Matrix.cons_val_two]

theorem tripleJet_at_zero {n : ℕ} (X Y Z : SpinOperator n) (k a b c : ℕ) :
    tripleJet X Y Z k a b c 0 = tripleMoment X Y Z k a b c := by
  induction k generalizing a b c with
  | zero =>
      simp only [tripleJet, expPower, tripleMoment,
        zero_smul ℝ X, zero_smul ℝ Y, zero_smul ℝ Z, NormedSpace.exp_zero, one_mul]
  | succ k ih => simp only [tripleJet, tripleMoment, ih]

theorem map_tripleMoment {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (φ : R →+* S) (X Y Z : R) (k a b c : ℕ) :
    φ (tripleMoment X Y Z k a b c) =
      tripleMoment (φ X) (φ Y) (φ Z) k a b c := by
  induction k generalizing a b c with
  | zero => simp [tripleMoment]
  | succ k ih => simp [tripleMoment, ih]

def planeOperator (f g : ℝ) : SpinOperator 3 := matrixOperator (plane f g)

theorem planeOperator_eq (f g : ℝ) : planeOperator f g = f • axisA + g • axisB := by
  rw [planeOperator, axisA, axisB, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, axisMatrixA, axisMatrixB]

theorem plane_commutator (f g h k : ℝ) :
    plane f g * plane h k - plane h k * plane f g = (f*k-g*h) • third := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, third, Matrix.cons_val_two] <;> ring

theorem planeOperator_commutator (f g h k : ℝ) :
    planeOperator f g * planeOperator h k - planeOperator h k * planeOperator f g =
      (f*k-g*h) • axisC := by
  rw [planeOperator, planeOperator, ← map_mul, ← map_mul, ← map_sub, plane_commutator,
    map_smul]
  rfl

theorem gaugeJet_plane_four_even (f g h k : ℝ) :
    tripleJet (planeOperator f g) (planeOperator h k-planeOperator f g)
      (-planeOperator h k) 4 0 0 0 0 +
    tripleJet (planeOperator f (-g)) (planeOperator h (-k)-planeOperator f (-g))
      (-planeOperator h (-k)) 4 0 0 0 0 = (6*(f*k-g*h)^2) • axisC^2 := by
  simp only [tripleJet_at_zero, planeOperator]
  have hm (f g h k : ℝ) := map_tripleMoment matrixOperator.toRingHom
    (plane f g) (plane h k-plane f g) (-plane h k) 4 0 0 0
  change ∀ f g h k, matrixOperator (tripleMoment (plane f g)
    (plane h k-plane f g) (-plane h k) 4 0 0 0) =
      tripleMoment (matrixOperator (plane f g)) (matrixOperator (plane h k-plane f g))
        (matrixOperator (-plane h k)) 4 0 0 0 at hm
  simp only [map_sub, map_neg] at hm
  rw [← hm, ← hm, ← map_add]
  change matrixOperator (moment4Plane f g h k + moment4Plane f (-g) h (-k)) = _
  rw [moment4_plane_even, map_smul, map_pow]
  rfl

def mixedMatrixAB : Matrix (Fin 3) (Fin 3) ℝ := !![0,1/2,0;1/2,0,0;0,0,0]
def mixedMatrixAAB : Matrix (Fin 3) (Fin 3) ℝ := (-1/3 : ℝ) • axisMatrixB
def mixedMatrixABB : Matrix (Fin 3) (Fin 3) ℝ := (-1/3 : ℝ) • axisMatrixA
def mixedMatrixAABB : Matrix (Fin 3) (Fin 3) ℝ := (-1/6 : ℝ) • (axisMatrixA^2+axisMatrixB^2)

theorem plane_matrix_square (f g : ℝ) :
    plane f g ^ 2 = f^2 • axisMatrixA^2 + (2*f*g) • mixedMatrixAB + g^2 • axisMatrixB^2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAB, pow_succ, Matrix.cons_val_two] <;> ring

theorem plane_matrix_cube (f g : ℝ) :
    plane f g ^ 3 = f^3 • axisMatrixA^3 + (3*f^2*g) • mixedMatrixAAB + (3*f*g^2) • mixedMatrixABB + g^3 • axisMatrixB^3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAAB, mixedMatrixABB, pow_succ, Matrix.cons_val_two] <;> ring

theorem plane_matrix_four_even (f g : ℝ) :
    plane f g ^ 4 + plane f (-g) ^ 4 = (2*f^4) • axisMatrixA^4 +
      (12*f^2*g^2) • mixedMatrixAABB + (2*g^4) • axisMatrixB^4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAABB, pow_succ, Matrix.cons_val_two] <;> ring

theorem mixedMatrixAB_sym : mixedMatrixAB = (1/2 : ℝ) • (axisMatrixA*axisMatrixB+axisMatrixB*axisMatrixA) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA, axisMatrixB, mixedMatrixAB, Matrix.cons_val_two]

def mixedAB : SpinOperator 3 := matrixOperator mixedMatrixAB
def mixedAAB : SpinOperator 3 := matrixOperator mixedMatrixAAB
def mixedABB : SpinOperator 3 := matrixOperator mixedMatrixABB
def mixedAABB : SpinOperator 3 := matrixOperator mixedMatrixAABB

theorem planeOperator_square (f g : ℝ) :
    planeOperator f g ^ 2 = f^2 • axisA^2 + (2*f*g) • mixedAB + g^2 • axisB^2 := by
  have h := congrArg matrixOperator (plane_matrix_square f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_cube (f g : ℝ) :
    planeOperator f g ^ 3 = f^3 • axisA^3 + (3*f^2*g) • mixedAAB +
      (3*f*g^2) • mixedABB + g^3 • axisB^3 := by
  have h := congrArg matrixOperator (plane_matrix_cube f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_four_even (f g : ℝ) :
    planeOperator f g ^ 4 + planeOperator f (-g) ^ 4 = (2*f^4) • axisA^4 +
      (12*f^2*g^2) • mixedAABB + (2*g^4) • axisB^4 := by
  have h := congrArg matrixOperator (plane_matrix_four_even f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem energy_add (S : SpinSystem n V E) (K L : E → SpinOperator n) (σ : V → Spin n) :
    S.energy (K+L) σ = S.energy K σ + S.energy L σ := by
  simp [energy, inner_add_right, mul_add, Finset.sum_add_distrib]

omit [Fintype V] in
theorem energy_smul (S : SpinSystem n V E) (r : ℝ) (K : E → SpinOperator n)
    (σ : V → Spin n) : S.energy (r • K) σ = r * S.energy K σ := by
  simp only [energy, Pi.smul_apply, smul_apply, real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype V] in
theorem energy_neg (S : SpinSystem n V E) (K : E → SpinOperator n) (σ : V → Spin n) :
    S.energy (-K) σ = -S.energy K σ := by
  simp [energy]

theorem average_mul_const (S : SpinSystem n V E) (r : ℝ) (f : (V → Spin n) → ℝ) :
    S.average (fun σ => r * f σ) = r * S.average f := by
  simp only [average, mul_assoc, integral_const_mul, mul_div_assoc]

def fourthPolynomial (F : ℕ → ℝ) : ℝ :=
  F 4 + 4 * F 1 * F 3 + 3 * (F 2)^2 + 6 * (F 1)^2 * F 2 + (F 1)^4

def fourthResponse (S : SpinSystem n V E) (A : E → SpinOperator n) : ℝ :=
  S.average (fun σ => fourthPolynomial (fun k => S.energy (fun e => A e ^ k) σ))

theorem fourthResponse_integral [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) :
    S.fourthResponse A = (∫ σ, S.fourthWeight A 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold fourthResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hz (e : E) : (0:ℝ) • A e = 0 := zero_smul ℝ (A e)
  simp only [fourthWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul, pow_zero,
    fourthPolynomial]
  ring

theorem fourthResponse_gauge [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.fourthResponse (fun e => F (S.right e)-F (S.left e)) =
      S.average (fun σ => S.gaugeEnergy F 4 0 σ + 3 * (S.energy
        (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2) := by
  rw [S.fourthResponse_integral, S.fourth_noncommuting_identity F hF hP]
  unfold average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  exact mul_comm _ _

omit [Fintype V] [Fintype E] in
def crossForm (S : SpinSystem 3 V E) (f g : V → ℝ) : E → ℝ :=
  fun e => f (S.left e)*g (S.right e)-g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
def planarGradient (S : SpinSystem 3 V E) (f g : V → ℝ) : E → SpinOperator 3 :=
  fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))

def secondAxisResponse (S : SpinSystem 3 V E) (h k : E → ℝ) : ℝ :=
  S.average (fun σ => S.energy (fun e => (h e*k e) • axisC^2) σ +
    S.energy (fun e => h e • axisC) σ * S.energy (fun e => k e • axisC) σ)

end SpinSystem

end ClassicalON

end

end OAI
