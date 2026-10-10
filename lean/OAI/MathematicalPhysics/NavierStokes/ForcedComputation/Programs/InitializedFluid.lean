import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedProgram

namespace OAI

/-! The loaded program retains the analytic properties of its two shear fields. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal
open ShearFlows

namespace ForcedComputation

theorem force_zero (ν : ℝ) (y : SpaceTime) :
    force ν (fun _ : SpaceTime => (0 : Space)) y = 0 := by
  rw [force_eq_mixed contDiff_const]
  simp [mixedDerivative_zero]

theorem force_eq_of_eventuallyEq {U V : Velocity} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) {y : SpaceTime} (he : U =ᶠ[𝓝 y] V) (ν : ℝ) :
    force ν U y = force ν V y := by
  have hh (α) := (mixedDerivative_eventuallyEq he α).self_of_nhds
  simp only [force_eq_mixed hU, force_eq_mixed hV, hh]

theorem initializedProgram_zero_extend (loader body : Input) {t : ℝ}
    (ht : t < 1 / 32) (x : Space) : initializedProgram loader body (t, x) = 0 := by
  by_cases hn : t ≤ 0
  · exact initializedProgram_before loader body hn x
  · rw [initializedProgram_loading loader body ⟨(lt_of_not_ge hn).le, by linarith⟩]
    apply realizingVelocity_vanish_near_integers loader 0
    simpa only [Int.cast_zero, sub_zero, abs_of_pos (lt_of_not_ge hn)] using ht

theorem initializedProgram_loading_extend (loader body : Input) {t : ℝ}
    (ht : -(1 / 32 : ℝ) < t ∧ t < 1 + 1 / 32) (x : Space) :
    initializedProgram loader body (t, x) = loader.realizingVelocity (t, x) := by
  by_cases hn : t < 0
  · rw [initializedProgram_before loader body hn.le]
    symm
    apply realizingVelocity_vanish_near_integers loader 0
    simpa only [Int.cast_zero, sub_zero, abs_of_neg hn] using (show -t < 1 / 32 by linarith)
  by_cases hp : 1 < t
  · rw [initializedProgram_tail loader body hp.le]
    have hc : |t - (1 : ℤ)| < (1 / 32 : ℝ) := by
      rw [Int.cast_one, abs_of_pos (by linarith : 0 < t - 1)]
      linarith
    rw [realizingVelocity_vanish_near_integers body 1 hc,
      realizingVelocity_vanish_near_integers loader 1 hc]
  · exact initializedProgram_loading loader body ⟨le_of_not_gt hn, le_of_not_gt hp⟩ x

theorem initializedProgram_tail_extend (loader body : Input) {t : ℝ}
    (ht : 1 - 1 / 32 < t) (x : Space) :
    initializedProgram loader body (t, x) = body.realizingVelocity (t, x) := by
  by_cases hp : 1 ≤ t
  · exact initializedProgram_tail loader body hp x
  · have hc : |t - (1 : ℤ)| < (1 / 32 : ℝ) := by
      apply abs_lt.mpr
      norm_num only [Int.cast_one]
      constructor <;> linarith
    rw [initializedProgram_loading loader body ⟨by linarith, (lt_of_not_ge hp).le⟩,
      realizingVelocity_vanish_near_integers body 1 hc,
      realizingVelocity_vanish_near_integers loader 1 hc]

theorem initializedProgram_loading_germ (loader body : Input) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Space) :
    initializedProgram loader body =ᶠ[𝓝 (t, x)] loader.realizingVelocity := by
  have hl : -(1 / 32 : ℝ) < t := by linarith [ht.1]
  have hr : t < 1 + 1 / 32 := by linarith [ht.2]
  filter_upwards [(continuous_fst.tendsto (t, x)).eventually
    (Ioo_mem_nhds hl hr)] with y hy
  exact initializedProgram_loading_extend loader body hy y.2

theorem initializedProgram_tail_germ (loader body : Input) {t : ℝ}
    (ht : 1 ≤ t) (x : Space) :
    initializedProgram loader body =ᶠ[𝓝 (t, x)] body.realizingVelocity := by
  have hl : 1 - (1 / 32 : ℝ) < t := by linarith
  filter_upwards [(continuous_fst.tendsto (t, x)).eventually
    (eventually_gt_nhds hl)] with y hy
  exact initializedProgram_tail_extend loader body hy y.2

theorem initializedProgram_zero_germ (loader body : Input) {t : ℝ}
    (ht : t ≤ 0) (x : Space) :
    initializedProgram loader body =ᶠ[𝓝 (t, x)] fun _ => 0 := by
  have hr : t < (1 / 32 : ℝ) := by linarith
  filter_upwards [(continuous_fst.tendsto (t, x)).eventually
    (eventually_lt_nhds hr)] with y hy
  exact initializedProgram_zero_extend loader body hy y.2

theorem initializedForce_loading {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Space) :
    force ν (initializedProgram loader body) (t, x) = force ν loader.realizingVelocity (t, x) :=
  force_eq_of_eventuallyEq (initializedProgram_smooth hloader hbody)
    (realizingVelocity_smooth hloader) (initializedProgram_loading_germ loader body ht x) ν

theorem initializedForce_tail {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ)
    {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    force ν (initializedProgram loader body) (t, x) = force ν body.realizingVelocity (t, x) :=
  force_eq_of_eventuallyEq (initializedProgram_smooth hloader hbody)
    (realizingVelocity_smooth hbody) (initializedProgram_tail_germ loader body ht x) ν

theorem initializedForce_before {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ)
    {t : ℝ} (ht : t ≤ 0) (x : Space) :
    force ν (initializedProgram loader body) (t, x) = 0 := by
  rw [force_eq_of_eventuallyEq (initializedProgram_smooth hloader hbody)
    contDiff_const (initializedProgram_zero_germ loader body ht x) ν]
  exact force_zero ν (t, x)

theorem initializedProgram_eventually_periodic (loader body : Input)
    {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    initializedProgram loader body (t + 1, x) = initializedProgram loader body (t, x) := by
  rw [initializedProgram_tail loader body (by linarith),
    initializedProgram_tail loader body ht, realizingVelocity_time_periodic body]

theorem initializedForce_eventually_periodic {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ)
    {t : ℝ} (ht : 1 ≤ t) (x : Space) :
    force ν (initializedProgram loader body) (t + 1, x) =
      force ν (initializedProgram loader body) (t, x) := by
  rw [initializedForce_tail hloader hbody ν (by linarith),
    initializedForce_tail hloader hbody ν ht]
  exact force_time_periodic (realizingVelocity_smooth hbody)
    (realizingVelocity_time_periodic body) ν t x

theorem initializedForce_bounded {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) (ν : ℝ) :
    BoundedMixedDerivatives (force ν (initializedProgram loader body)) :=
  boundedMixed_of_stationary_tail (by exact_mod_cast hbody.period_pos)
    (force_smooth (initializedProgram_smooth hloader hbody) ν)
    (force_smooth (realizingVelocity_smooth hbody) ν)
    (force_spatially_periodic (initializedProgram_smooth hloader hbody)
      (initializedProgram_periodic hperiod) ν)
    (force_spatially_periodic (realizingVelocity_smooth hbody)
      (realizingVelocity_spatially_periodic body) ν)
    (force_time_periodic (realizingVelocity_smooth hbody)
      (realizingVelocity_time_periodic body) ν)
    (fun _ ht x => initializedForce_before hloader hbody ν ht.le x)
    (fun _ ht x => initializedForce_tail hloader hbody ν ht.le x)

theorem initializedForce_mean_zero {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) (ν : ℝ) :
    HasZeroMean body.period (force ν (initializedProgram loader body)) := by
  intro t
  by_cases hn : t ≤ 0
  · simp_rw [initializedForce_before hloader hbody ν hn]
    simp
  by_cases hp : 1 ≤ t
  · simp_rw [initializedForce_tail hloader hbody ν hp]
    exact realizingForce_mean_zero hbody ν t
  · simp_rw [initializedForce_loading hloader hbody ν
      (show t ∈ Icc (0 : ℝ) 1 from ⟨(lt_of_not_ge hn).le, (lt_of_not_ge hp).le⟩)]
    rw [← hperiod]
    exact realizingForce_mean_zero hloader ν t

theorem initializedProgram_slice (loader body : Input) (t : ℝ) :
    (fun x => initializedProgram loader body (t, x)) = (fun _ => 0) ∨
    (fun x => initializedProgram loader body (t, x)) = (fun x => loader.realizingVelocity (t, x)) ∨
    (fun x => initializedProgram loader body (t, x)) = (fun x => body.realizingVelocity (t, x)) := by
  by_cases hn : t ≤ 0
  · exact Or.inl (funext (initializedProgram_before loader body hn))
  by_cases hp : 1 ≤ t
  · exact Or.inr (Or.inr (funext (initializedProgram_tail loader body hp)))
  · exact Or.inr (Or.inl (funext (initializedProgram_loading loader body
      ⟨(lt_of_not_ge hn).le, (lt_of_not_ge hp).le⟩)))

theorem initializedProgram_integer_collars (loader body : Input) (k : ℤ)
    {t : ℝ} (ht : |t - (k : ℝ)| < (1 / 32 : ℝ)) (x : Space) :
    initializedProgram loader body (t, x) = 0 := by
  rcases initializedProgram_slice loader body t with he | he | he
  · exact congrFun he x
  · rw [congrFun he x]
    exact realizingVelocity_vanish_near_integers loader k ht x
  · rw [congrFun he x]
    exact realizingVelocity_vanish_near_integers body k ht x

theorem initializedForce_integer_collars {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ) (k : ℤ)
    {t : ℝ} (ht : |t - (k : ℝ)| < (1 / 32 : ℝ)) (x : Space) :
    force ν (initializedProgram loader body) (t, x) = 0 := by
  have he : initializedProgram loader body =ᶠ[𝓝 (t, x)] fun _ => 0 := by
    have hopen : IsOpen {y : SpaceTime | |y.1 - (k : ℝ)| < (1 / 32 : ℝ)} :=
      isOpen_lt (continuous_fst.sub continuous_const).abs continuous_const
    filter_upwards [hopen.mem_nhds ht] with y hy
    exact initializedProgram_integer_collars loader body k hy y.2
  rw [force_eq_of_eventuallyEq (initializedProgram_smooth hloader hbody) contDiff_const he ν]
  exact force_zero ν (t, x)

theorem initializedProgram_solenoidal {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) :
    Solenoidal (initializedProgram loader body) := by
  intro t x
  rcases initializedProgram_slice loader body t with he | he | he
  · rw [he]
    simp [divergence, derivative]
  · rw [he]
    exact (realizingVelocity_divergence_advection hloader).1 t x
  · rw [he]
    exact (realizingVelocity_divergence_advection hbody).1 t x

theorem initializedProgram_zero_advection {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) :
    ZeroAdvection (initializedProgram loader body) := by
  intro t x
  rcases initializedProgram_slice loader body t with he | he | he
  · rw [he]
    simp [advection]
  · rw [he]
    exact (realizingVelocity_divergence_advection hloader).2 t x
  · rw [he]
    exact (realizingVelocity_divergence_advection hbody).2 t x

theorem initializedForce_solenoidal {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) (ν : ℝ) :
    Solenoidal (force ν (initializedProgram loader body)) :=
  force_solenoidal (initializedProgram_smooth hloader hbody)
    (initializedProgram_solenoidal hloader hbody) ν

theorem initializedProgram_mean_zero {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) :
    HasZeroMean body.period (initializedProgram loader body) := by
  intro t
  rcases initializedProgram_slice loader body t with he | he | he
  · rw [he]; simp
  · rw [he, ← hperiod]; exact realizingVelocity_mean_zero hloader t
  · rw [he]; exact realizingVelocity_mean_zero hbody t

theorem initializedProgram_solution {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) (ν : ℝ) :
    IsClassicalSolution body.period ν (force ν (initializedProgram loader body))
      (initializedProgram loader body) (fun _ => 0) :=
  velocity_solves_forced_NS (initializedProgram_smooth hloader hbody)
    (initializedProgram_periodic hperiod) (initializedProgram_solenoidal hloader hbody)
    (initializedProgram_zero_advection hloader hbody)
    (initializedProgram_before loader body le_rfl) ν

theorem initializedProgram_spatial_lipschitz {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body) :
    ∃ K : ℝ≥0, ∀ t, LipschitzWith K (fun x => initializedProgram loader body (t, x)) := by
  obtain ⟨KL, hKL⟩ := smooth_periodic_lipschitz (by exact_mod_cast hloader.period_pos)
    (realizingVelocity_smooth hloader) (realizingVelocity_spatially_periodic loader)
    (realizingVelocity_time_periodic loader)
  obtain ⟨KB, hKB⟩ := smooth_periodic_lipschitz (by exact_mod_cast hbody.period_pos)
    (realizingVelocity_smooth hbody) (realizingVelocity_spatially_periodic body)
    (realizingVelocity_time_periodic body)
  refine ⟨max KL KB, fun t => ?_⟩
  rcases initializedProgram_slice loader body t with he | he | he
  · rw [he]
    exact (LipschitzWith.const (0 : Space)).weaken (zero_le)
  · rw [he]
    apply (show LipschitzWith KL (fun x => loader.realizingVelocity (t, x)) from ?_).weaken
      (le_max_left _ _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using hKL.dist_le_mul (t, x) (t, y)
  · rw [he]
    apply (show LipschitzWith KB (fun x => body.realizingVelocity (t, x)) from ?_).weaken
      (le_max_right _ _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using hKB.dist_le_mul (t, x) (t, y)

theorem initializedProgram_materialFlow {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) :
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow body.period (initializedProgram loader body) Φ := by
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hloader hbody
  obtain ⟨B, hB, hb⟩ := initializedProgram_bounded hloader hbody hperiod []
  exact exists_materialFlow_of_bounded_lipschitz (B := ⟨B, hB⟩) hK
    (fun x => (initializedProgram_smooth hloader hbody).continuous.comp
      (continuous_id.prodMk continuous_const))
    (fun t x => hb (t, x)) (initializedProgram_periodic hperiod)

theorem initializedProgram_unique {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) {ν : ℝ} (hν : 0 ≤ ν) :
    ∀ u p, IsClassicalSolution body.period ν (force ν (initializedProgram loader body)) u p →
      ∀ t, 0 ≤ t → ∀ x, u (t, x) = initializedProgram loader body (t, x) ∧ p (t, x) = 0 := by
  have hsol := initializedProgram_solution hloader hbody hperiod ν
  obtain ⟨K, hK⟩ := initializedProgram_spatial_lipschitz hloader hbody
  have hb (t : ℝ) (_ : 0 ≤ t) (x : Space) :
      ‖fderiv ℝ (fun y => initializedProgram loader body (t, y)) x‖ ≤ (K : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ (hK t)
  intro u p hu
  have he := classical_velocity_unique (by exact_mod_cast hbody.period_pos) hν hu hsol hb
  have hp := classical_pressure_unique (by exact_mod_cast hbody.period_pos) hu hsol he
  exact fun t ht x => ⟨he t ht x, hp t ht x⟩

theorem initializedProgram_energy_bounded {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (hperiod : loader.period = body.period) :
    ∃ E : ℝ, ∀ t, kineticEnergy body.period (initializedProgram loader body) t ≤ E := by
  obtain ⟨B, hB, hb⟩ := initializedProgram_bounded hloader hbody hperiod []
  exact ⟨(1 / 2 : ℝ) * volume.real (fundamentalCube body.period) * (3 * B ^ 2),
    fun t => kineticEnergy_bound (initializedProgram_smooth hloader hbody).continuous
      body.period hB hb t⟩

end ForcedComputation

end

end OAI
