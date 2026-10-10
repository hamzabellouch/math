import OAI.MeasureTheory.Falconer.Measures.DensityTruncation

namespace OAI

/-!
# Integer cap availability from radial densities

This is the measure-theoretic truncation step of `prep:integer-caps`.
An angular reference measure with cap exponent `q` and integrable radial
`p`th density moments give availability of `q` for the original pair law.
The radial density hypothesis is the input supplied by the radial
projection theorem.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem density_threshold_cap_scalar {R A e q u : ℝ}
    (hR : 0 < R) (hu : 0 < u) (hconstant : A ≤ R ^ (e / 2)) :
    R ^ (e / 2) * (A * u ^ q) ≤ R ^ e * u ^ q := by
  calc
    R ^ (e / 2) * (A * u ^ q) = A * (R ^ (e / 2) * u ^ q) := by ring
    _ ≤ R ^ (e / 2) * (R ^ (e / 2) * u ^ q) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = R ^ e * u ^ q := by
      rw [← mul_assoc, ← Real.rpow_add hR]
      congr 2
      ring

private theorem truncated_radial_cap_of_density {d : ℕ}
    (ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f : Space d → ℝ≥0∞) (x : Space d) (hf : Measurable f)
    (hdensity : (ν : Measure (Space d)).map (radialDirection x) = σ.withDensity f)
    {R A e q : ℝ} (hR : 0 < R) (_hA : 0 < A)
    (hconstant : A ≤ R ^ (e / 2))
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (H : Set (Space d))
    (hH : ∀ y ∈ H, f (radialDirection x y) ≤ ENNReal.ofReal (R ^ (e / 2))) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ e * u ^ q) := by
  intro w hw u hu hu1
  have hr : Measurable (radialDirection x) := by
    unfold radialDirection
    fun_prop
  have htrunc := truncated_radial_fiber (ν : Measure (Space d)) σ f
    (radialDirection x) hf hr hdensity (ENNReal.ofReal (R ^ (e / 2))) H hH
    (Metric.ball w u) measurableSet_ball
  calc
    (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e / 2)) * σ (Metric.ball w u) := by
      exact htrunc
    _ ≤ ENNReal.ofReal (R ^ (e / 2)) * ENNReal.ofReal (A * u ^ q) :=
      mul_le_mul_right (hσ w hw u hu hu1) _
    _ = ENNReal.ofReal (R ^ (e / 2) * (A * u ^ q)) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    _ ≤ ENNReal.ofReal (R ^ e * u ^ q) :=
      ENNReal.ofReal_le_ofReal (density_threshold_cap_scalar hR hu hconstant)

/-- Bilateral radial densities with finite integrated `p`th moments make
the reference cap exponent available in the original product measure.
The deleted mass has a positive power saving for every requested loss.
Null strips of exceptional pins make the resulting bounds valid at every
support pin, although the radial density identities hold only almost everywhere. -/
theorem capAvailable_of_bilateral_radial_densities {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞) :
    CapAvailable μ ν (fun _ => Set.univ) q := by
  obtain ⟨Xbad, hXsub, hXm, hXnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hfdensity)
  obtain ⟨Ybad, hYsub, hYm, hYnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hgdensity)
  intro e he
  obtain ⟨c, C, hc, hC, htail⟩ := exists_density_tail_power_bound _ hmoment he hp
  have hconstant : ∀ᶠ N : ℕ in atTop, A ≤ ((2 : ℝ) ^ N) ^ (e / 2) := by
    simpa using (eventually_radius_factor_absorbed (K := A) (q := 1)
      (a := e / 2) (by linarith))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hconstant
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  let R : ℝ := (2 : ℝ) ^ N
  let T : ℝ≥0∞ := ENNReal.ofReal (R ^ (e / 2))
  let r : Space d × Space d → Space d := fun z => radialDirection z.1 z.2
  let B₀ : Set (Space d × Space d) := densityFailure f r T ∪
    Prod.swap ⁻¹' densityFailure g r T
  let Z : Set (Space d × Space d) := (Xbad ×ˢ Set.univ) ∪ (Set.univ ×ˢ Ybad)
  let B : Set (Space d × Space d) := B₀ ∪ Z
  have hR : 0 < R := by dsimp [R]; positivity
  have hT : 0 < T := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)
  have hTtop : T ≠ ∞ := ENNReal.ofReal_ne_top
  have hB₀ : MeasurableSet B₀ :=
    (measurableSet_densityFailure hf measurable_radialDirection_joint T).union
      ((measurableSet_densityFailure hg measurable_radialDirection_joint T).preimage
        measurable_swap)
  have hZ : MeasurableSet Z :=
    (hXm.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hYm)
  have hZnull : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z = 0 := by
    apply measure_union_null <;> simp only [Measure.prod_prod, hXnull, hYnull, zero_mul, mul_zero]
  have hB : MeasurableSet B := hB₀.union hZ
  refine ⟨B, hB, subset_univ _, ?_, ?_⟩
  · calc
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ +
          ((μ : Measure (Space d)).prod (ν : Measure (Space d))) Z := measure_union_le _ _
      _ = ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B₀ := by rw [hZnull, add_zero]
      _ ≤ ENNReal.ofReal (C * R ^ (-c)) :=
        (bilateral_density_failure_mass (μ : Measure (Space d))
          (ν : Measure (Space d)) σ f r g r hf measurable_radialDirection_joint hg
          measurable_radialDirection_joint hfdensity hgdensity hT hTtop hp).trans (htail R hR)
  · constructor
    · intro x _ w hw u hu hu1
      by_cases hxb : x ∈ Xbad
      · have hempty : {y | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection x y) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro y hy
          exact hy.1.2 (Or.inr (Or.inl ⟨hxb, Set.mem_univ y⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (ν : Measure (Space d)).map (radialDirection x) =
          σ.withDensity (fun a => f (x, a)) := by
        by_contra h
        exact hxb (hXsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ y ∈ {y | (x, y) ∈ Set.univ \ B},
          f (x, radialDirection x y) ≤ T := by
        intro y hy
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inl (lt_of_not_ge h))
        exact hy.2 hbad
      exact truncated_radial_cap_of_density ν σ (fun a => f (x, a)) x
        (hf.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {y | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1
    · intro y _ w hw u hu hu1
      by_cases hyb : y ∈ Ybad
      · have hempty : {x | (x, y) ∈ Set.univ \ B ∧
              dist (radialDirection y x) w < u} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.2
          intro x hx
          exact hx.1.2 (Or.inr (Or.inr ⟨Set.mem_univ x, hyb⟩))
        rw [hempty, measure_empty]
        exact bot_le
      have hdensity : (μ : Measure (Space d)).map (radialDirection y) =
          σ.withDensity (fun a => g (y, a)) := by
        by_contra h
        exact hyb (hYsub h)
      have hupos : 0 < u := (inv_pos.mpr hR).trans_le hu
      have hlow : ∀ x ∈ {x | (x, y) ∈ Set.univ \ B},
          g (y, radialDirection y x) ≤ T := by
        intro x hx
        by_contra h
        have hbad : (x, y) ∈ B := Or.inl (Or.inr (lt_of_not_ge h))
        exact hx.2 hbad
      exact truncated_radial_cap_of_density μ σ (fun a => g (y, a)) y
        (hg.comp (measurable_const.prodMk measurable_id)) hdensity hR hA
        (hK N hN) hσ {x | (x, y) ∈ Set.univ \ B} hlow w hw u hupos hu1

/-- The same density truncation works inside every measurable coarse pair
filter; its fibers continue to use the original source marginals. -/
theorem capAvailable_of_bilateral_radial_densities_restrict {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (σ : Measure (Space d))
    (f g : Space d × Space d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfdensity : ∀ᵐ x ∂(μ : Measure (Space d)),
      (ν : Measure (Space d)).map (radialDirection x) =
        σ.withDensity (fun a => f (x, a)))
    (hgdensity : ∀ᵐ y ∂(ν : Measure (Space d)),
      (μ : Measure (Space d)).map (radialDirection y) =
        σ.withDensity (fun a => g (y, a)))
    {p q A : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hσ : ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, 0 < u → u ≤ 1 →
      σ (Metric.ball w u) ≤ ENNReal.ofReal (A * u ^ q))
    (hmoment : ((∫⁻ x, ∫⁻ a, f (x, a) ^ p ∂σ ∂(μ : Measure (Space d))) +
      ∫⁻ y, ∫⁻ a, g (y, a) ^ p ∂σ ∂(ν : Measure (Space d))) ≠ ∞)
    (Γ : ℕ → Set (Space d × Space d)) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ q :=
  (capAvailable_of_bilateral_radial_densities μ ν σ f g hf hg hfdensity hgdensity hp
    hA hσ hmoment).restrict hΓ (fun _ => subset_univ _)

end Falconer

end OAI
