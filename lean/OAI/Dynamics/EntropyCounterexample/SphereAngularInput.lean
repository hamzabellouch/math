import OAI.Dynamics.EntropyCounterexample.SphereCutoffs

namespace OAI

noncomputable section

open scoped Topology

namespace Problem340.SphereAngularInput

def horizontal (x : SphereAmbient) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

def phase (x : SphereAmbient) : ℂ := (‖horizontal x‖ : ℂ)⁻¹ * horizontal x

def angularAmbient (k : ℕ) (x : SphereAmbient) : ℂ :=
  (SphereCutoffs.preparationCutoffAmbient x : ℂ) * phase x ^ k

def angular (k : ℕ) (x : StandardSphere2) : ℂ := angularAmbient k x.1

@[fun_prop]
theorem contDiff_horizontal {n : ℕ∞} : ContDiff ℝ n horizontal := by
  have h0 : ContDiff ℝ n (fun x : SphereAmbient => (x 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff
  have h1 : ContDiff ℝ n (fun x : SphereAmbient => (x 1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff
  exact h0.add (h1.mul contDiff_const)

theorem contDiffAt_phase {n : ℕ∞} {x : SphereAmbient} (hx : horizontal x ≠ 0) :
    ContDiffAt ℝ n phase x := by
  have hn : ContDiffAt ℝ n (fun y => (‖horizontal y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiff_horizontal.contDiffAt.norm ℂ hx)
  exact (hn.inv (by simpa using hx)).mul contDiff_horizontal.contDiffAt

theorem contDiffAt_angularAmbient_of_horizontal {n : ℕ∞} {x : SphereAmbient}
    (hx : horizontal x ≠ 0) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  exact (Complex.ofRealCLM.contDiff.comp
    SphereCutoffs.contDiff_preparationCutoffAmbient).contDiffAt.mul
      ((contDiffAt_phase hx).pow k)

theorem angularAmbient_eq_zero_of_low {x : SphereAmbient} (hx : x 2 ≤ -4 / 5) (k : ℕ) :
    angularAmbient k x = 0 := by
  simp [angularAmbient, SphereCutoffs.preparationCutoffAmbient_eq_zero_of_low hx]

theorem angularAmbient_eq_zero_of_high {x : SphereAmbient} (hx : 1 / 2 ≤ x 2) (k : ℕ) :
    angularAmbient k x = 0 := by
  simp [angularAmbient, SphereCutoffs.preparationCutoffAmbient_eq_zero_of_high hx]

theorem contDiffAt_angularAmbient_of_low {n : ℕ∞} {x : SphereAmbient}
    (hx : x 2 < -4 / 5) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  filter_upwards [hh.eventually (gt_mem_nhds hx)] with y hy
  exact angularAmbient_eq_zero_of_low hy.le k

theorem contDiffAt_angularAmbient_of_high {n : ℕ∞} {x : SphereAmbient}
    (hx : 1 / 2 < x 2) (k : ℕ) : ContDiffAt ℝ n (angularAmbient k) x := by
  apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  filter_upwards [hh.eventually (lt_mem_nhds hx)] with y hy
  exact angularAmbient_eq_zero_of_high hy.le k

def regularDomain : Set SphereAmbient :=
  {x | horizontal x ≠ 0 ∨ x 2 < -4 / 5 ∨ 1 / 2 < x 2}

theorem isOpen_regularDomain : IsOpen regularDomain := by
  have hh := (@contDiff_horizontal 0).continuous
  have hz := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  exact (isOpen_ne.preimage hh).union
    ((isOpen_lt hz continuous_const).union (isOpen_lt continuous_const hz))

theorem contDiffOn_angularAmbient {n : ℕ∞} (k : ℕ) :
    ContDiffOn ℝ n (angularAmbient k) regularDomain := by
  apply isOpen_regularDomain.contDiffOn_iff.mpr
  intro x hx
  rcases hx with hx | hx | hx
  · exact contDiffAt_angularAmbient_of_horizontal hx k
  · exact contDiffAt_angularAmbient_of_low hx k
  · exact contDiffAt_angularAmbient_of_high hx k

theorem sphere_mem_regularDomain (x : StandardSphere2) : x.1 ∈ regularDomain := by
  by_cases hh : horizontal x.1 = 0
  · have h0 : x.1 0 = 0 := by simpa [horizontal] using congrArg Complex.re hh
    have h1 : x.1 1 = 0 := by simpa [horizontal] using congrArg Complex.im hh
    have hn : ‖x.1‖ = 1 := by simp
    have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.1
    have hh2 : (x.1 2) ^ 2 = 1 := by
      simpa [Fin.sum_univ_succ, hn, h0, h1, Real.norm_eq_abs] using hs.symm
    rcases (sq_eq_one_iff).mp hh2 with hp | hm
    · exact Or.inr (Or.inr (by rw [hp]; norm_num))
    · exact Or.inr (Or.inl (by rw [hm]; norm_num))
  · exact Or.inl hh

@[continuity, fun_prop]
theorem continuous_angular (k : ℕ) : Continuous (angular k) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((contDiffOn_angularAmbient (n := 0) k).contDiffAt
    (isOpen_regularDomain.mem_nhds (sphere_mem_regularDomain x))).continuousAt.comp
      continuous_subtype_val.continuousAt

theorem norm_phase_le_one (x : SphereAmbient) : ‖phase x‖ ≤ 1 := by
  by_cases hx : horizontal x = 0
  · simp [phase, hx]
  · simp [phase, norm_inv, norm_ne_zero_iff.mpr hx]

theorem norm_angularAmbient_le_one (k : ℕ) (x : SphereAmbient) :
    ‖angularAmbient k x‖ ≤ 1 := by
  rw [angularAmbient, norm_mul, norm_pow]
  refine (mul_le_of_le_one_left (by positivity) ?_).trans
    (pow_le_one₀ (norm_nonneg _) (norm_phase_le_one x))
  · simpa [abs_of_nonneg (SphereCutoffs.preparationCutoffAmbient_nonneg x)] using
      SphereCutoffs.preparationCutoffAmbient_le_one x

theorem norm_angular_le_one (k : ℕ) (x : StandardSphere2) : ‖angular k x‖ ≤ 1 :=
  norm_angularAmbient_le_one k x.1

def phaseBelt : Set SphereAmbient :=
  Metric.sphere 0 1 ∩ {x | -9 / 10 ≤ x 2 ∧ x 2 ≤ 3 / 4}

theorem isCompact_phaseBelt : IsCompact phaseBelt := by
  have hz := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  exact (isCompact_sphere (0 : SphereAmbient) 1).inter_right
    ((isClosed_le continuous_const hz).inter (isClosed_le hz continuous_const))

theorem horizontal_ne_zero_on_phaseBelt {x : SphereAmbient} (hx : x ∈ phaseBelt) :
    horizontal x ≠ 0 := by
  intro hh
  have h0 : x 0 = 0 := by simpa [horizontal] using congrArg Complex.re hh
  have h1 : x 1 = 0 := by simpa [horizontal] using congrArg Complex.im hh
  have hn : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx.1
  have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x
  have hh2 : (x 2) ^ 2 = 1 := by
    simpa [Fin.sum_univ_succ, hn, h0, h1, Real.norm_eq_abs] using hs.symm
  rcases (sq_eq_one_iff).mp hh2 with hp | hm
  · linarith [hx.2.2]
  · linarith [hx.2.1]

theorem norm_phase_eq_one {x : SphereAmbient} (hx : horizontal x ≠ 0) : ‖phase x‖ = 1 := by
  simp [phase, norm_inv, norm_ne_zero_iff.mpr hx]

theorem exists_bounds_cutoff_and_phase :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x ∈ Metric.sphere (0 : SphereAmbient) 1,
        ‖fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ ≤ A) ∧
      (∀ x ∈ phaseBelt, ‖fderiv ℝ phase x‖ ≤ B) := by
  have hχ : ContDiff ℝ 1 (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp SphereCutoffs.contDiff_preparationCutoffAmbient
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : SphereAmbient) 1).exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by norm_num)).continuousOn
  have hphase : ContinuousOn (fderiv ℝ phase) phaseBelt := by
    intro x hx
    exact ((contDiffAt_phase (n := 1) (horizontal_ne_zero_on_phaseBelt hx)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_phaseBelt.exists_bound_of_continuousOn hphase
  refine ⟨max 0 A, max 0 B, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro x hx
    exact (hA x hx).trans (le_max_right _ _)
  · intro x hx
    exact (hB x hx).trans (le_max_right _ _)

theorem fderiv_angularAmbient_eq_zero_of_low {x : SphereAmbient}
    (hx : x 2 < -4 / 5) (k : ℕ) : fderiv ℝ (angularAmbient k) x = 0 := by
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  have hz : angularAmbient k =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hh.eventually (gt_mem_nhds hx)] with y hy
    exact angularAmbient_eq_zero_of_low hy.le k
  simpa using hz.fderiv_eq (𝕜 := ℝ)

theorem fderiv_angularAmbient_eq_zero_of_high {x : SphereAmbient}
    (hx : 1 / 2 < x 2) (k : ℕ) : fderiv ℝ (angularAmbient k) x = 0 := by
  have hh : ContinuousAt (fun y : SphereAmbient => y 2) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousAt
  have hz : angularAmbient k =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hh.eventually (lt_mem_nhds hx)] with y hy
    exact angularAmbient_eq_zero_of_high hy.le k
  simpa using hz.fderiv_eq (𝕜 := ℝ)

theorem norm_fderiv_angularAmbient_le_at {A B : ℝ} {x : SphereAmbient}
    (hx : horizontal x ≠ 0)
    (hA : ‖fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ ≤ A)
    (hB : ‖fderiv ℝ phase x‖ ≤ B) (k : ℕ) :
    ‖fderiv ℝ (angularAmbient k) x‖ ≤ A + (k : ℝ) * B := by
  have hχ : DifferentiableAt ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp
      (SphereCutoffs.contDiff_preparationCutoffAmbient (n := 1))).differentiable (by norm_num) x
  have hψ : DifferentiableAt ℝ phase x :=
    (contDiffAt_phase (n := 1) hx).differentiableAt (by norm_num)
  have hunit := norm_phase_eq_one hx
  have hχnorm : ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ)‖ ≤ 1 := by
    simpa [abs_of_nonneg (SphereCutoffs.preparationCutoffAmbient_nonneg x)] using
      SphereCutoffs.preparationCutoffAmbient_le_one x
  have hpow : ‖fderiv ℝ (fun y => phase y ^ k) x‖ =
      (k : ℝ) * ‖fderiv ℝ phase x‖ := by
    rw [fderiv_fun_pow k hψ]
    simp [norm_smul, nsmul_eq_mul, norm_pow, hunit]
  unfold angularAmbient
  rw [fderiv_fun_mul hχ (hψ.fun_pow k)]
  calc
    _ ≤ ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ) •
          fderiv ℝ (fun y => phase y ^ k) x‖ +
        ‖phase x ^ k • fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ :=
      norm_add_le _ _
    _ = ‖(SphereCutoffs.preparationCutoffAmbient x : ℂ)‖ *
        ((k : ℝ) * ‖fderiv ℝ phase x‖) +
        ‖fderiv ℝ (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) x‖ := by
      simp only [norm_smul, norm_pow, hunit, one_pow, one_mul, hpow]
    _ ≤ 1 * ((k : ℝ) * B) + A := by
      exact add_le_add
        (mul_le_mul hχnorm (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg k))
          (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _)) (by norm_num)) hA
    _ = A + (k : ℝ) * B := by ring

theorem exists_uniform_angular_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (x : StandardSphere2),
      ‖angular k x‖ + ‖fderiv ℝ (angularAmbient k) x.1‖ ≤ C * (1 + (k : ℝ)) := by
  obtain ⟨A, B, hA0, hB0, hA, hB⟩ := exists_bounds_cutoff_and_phase
  refine ⟨1 + A + B, by linarith, ?_⟩
  intro k x
  have hd : ‖fderiv ℝ (angularAmbient k) x.1‖ ≤ A + (k : ℝ) * B := by
    by_cases hx : x.1 ∈ phaseBelt
    · exact norm_fderiv_angularAmbient_le_at (horizontal_ne_zero_on_phaseBelt hx)
        (hA x.1 x.2) (hB x.1 hx) k
    · have hnot : ¬ (-9 / 10 ≤ x.1 2 ∧ x.1 2 ≤ 3 / 4) := by
        intro h
        exact hx ⟨x.2, h⟩
      rw [not_and_or] at hnot
      rcases hnot with hlo | hhi
      · rw [fderiv_angularAmbient_eq_zero_of_low (by linarith : x.1 2 < -4 / 5) k, norm_zero]
        positivity
      · rw [fderiv_angularAmbient_eq_zero_of_high (by linarith : 1 / 2 < x.1 2) k, norm_zero]
        positivity
  have hv := norm_angular_le_one k x
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg hA0 hk]

theorem exists_uniform_angular_bound_on_compact {K : Set SphereAmbient}
    (hK : IsCompact K) (hU : K ⊆ regularDomain) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : ℕ) (x : SphereAmbient), x ∈ K →
      ‖angularAmbient k x‖ + ‖fderiv ℝ (angularAmbient k) x‖ ≤ C * (1 + (k : ℝ)) := by
  let belt : Set SphereAmbient := K ∩ {x | -4 / 5 ≤ x 2 ∧ x 2 ≤ 1 / 2}
  have hz := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hbelt : IsCompact belt := hK.inter_right
    ((isClosed_le continuous_const hz).inter (isClosed_le hz continuous_const))
  have hregular : ∀ x ∈ belt, horizontal x ≠ 0 := by
    intro x hx
    rcases hU hx.1 with hh | hlo | hhi
    · exact hh
    · linarith [hx.2.1]
    · linarith [hx.2.2]
  have hχ : ContDiff ℝ 1 (fun y => (SphereCutoffs.preparationCutoffAmbient y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp SphereCutoffs.contDiff_preparationCutoffAmbient
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by norm_num)).continuousOn
  have hphase : ContinuousOn (fderiv ℝ phase) belt := by
    intro x hx
    exact ((contDiffAt_phase (n := 1) (hregular x hx)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨B, hB⟩ := hbelt.exists_bound_of_continuousOn hphase
  have hA0 : 0 ≤ max 0 A := le_max_left _ _
  have hB0 : 0 ≤ max 0 B := le_max_left _ _
  refine ⟨1 + max 0 A + max 0 B, by linarith, ?_⟩
  intro k x hx
  have hd : ‖fderiv ℝ (angularAmbient k) x‖ ≤ max 0 A + (k : ℝ) * max 0 B := by
    by_cases hxb : x ∈ belt
    · exact norm_fderiv_angularAmbient_le_at (hregular x hxb)
        ((hA x hx).trans (le_max_right _ _)) ((hB x hxb).trans (le_max_right _ _)) k
    · have hnot : ¬ (-4 / 5 ≤ x 2 ∧ x 2 ≤ 1 / 2) := fun h => hxb ⟨hx, h⟩
      rcases not_and_or.mp hnot with hlo | hhi
      · rw [fderiv_angularAmbient_eq_zero_of_low (lt_of_not_ge hlo) k, norm_zero]
        positivity
      · rw [fderiv_angularAmbient_eq_zero_of_high (lt_of_not_ge hhi) k, norm_zero]
        positivity
  have hv := norm_angularAmbient_le_one k x
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg hA0 hk]

theorem exists_uniform_angular_neighborhood :
    ∃ (U : Set SphereAmbient) (C : ℝ), IsOpen U ∧
      Metric.sphere (0 : SphereAmbient) 1 ⊆ U ∧ 1 ≤ C ∧
      (∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (angularAmbient k) U) ∧
      ∀ (k : ℕ) (x : SphereAmbient), x ∈ U →
        ‖angularAmbient k x‖ + ‖fderiv ℝ (angularAmbient k) x‖ ≤ C * (1 + (k : ℝ)) := by
  have hs := isCompact_sphere (0 : SphereAmbient) 1
  have hsub : Metric.sphere (0 : SphereAmbient) 1 ⊆ regularDomain :=
    fun x hx => sphere_mem_regularDomain ⟨x, hx⟩
  obtain ⟨δ, hδ, hδU⟩ := hs.exists_cthickening_subset_open isOpen_regularDomain hsub
  obtain ⟨C, hC, hbound⟩ := exists_uniform_angular_bound_on_compact hs.cthickening hδU
  refine ⟨Metric.thickening δ (Metric.sphere (0 : SphereAmbient) 1), C,
    Metric.isOpen_thickening, Metric.self_subset_thickening hδ _, hC, ?_, ?_⟩
  · intro k
    exact (contDiffOn_angularAmbient (n := ⊤) k).mono
      ((Metric.thickening_subset_cthickening _ _).trans hδU)
  · intro k x hx
    exact hbound k x (Metric.thickening_subset_cthickening _ _ hx)

theorem phase_eq_normalize (x : SphereAmbient) :
    phase x = NormedSpace.normalize (horizontal x) := by
  simp [phase, NormedSpace.normalize, Complex.real_smul]

theorem phase_eq_of_positive_scale {x : SphereAmbient} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : horizontal x = r • z) :
    phase x = NormedSpace.normalize z := by
  rw [phase_eq_normalize, hx, NormedSpace.normalize_smul_of_pos hr]

end Problem340.SphereAngularInput

end

end OAI
