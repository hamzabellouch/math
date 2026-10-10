import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevLocalFlow
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerTorus
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! # Returning from the interaction equation to the Schrödinger equation -/

open Filter Topology Set

namespace DefocusingNLS

/-- A differentiable Sobolev curve under the free group loses exactly two derivatives. -/
theorem hasDerivAt_lowerSobolev_schrodingerCurve
    (v : ℝ → FourierL2) (v' : FourierL2) (t : ℝ) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => schrodingerFlow s (lowerSobolevInclusion (v s)))
      (schrodingerFlow t (lowerSobolevGenerator (v t)) +
        schrodingerFlow t (lowerSobolevInclusion v')) t := by
  let w : ℝ → FourierL2 := fun s =>
    schrodingerFlow s (lowerSobolevInclusion (v s - v t))
  have hw : HasDerivAt w (schrodingerFlow t (lowerSobolevInclusion v')) t := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hl := ((lowerSobolevInclusion.restrictScalars ℝ).continuous.tendsto v').comp
      hv.tendsto_slope
    have hp := (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[≠] t ≤ 𝓝 t)).prodMk_nhds hl
    have h := continuous_schrodingerFlow_uncurry.continuousAt.tendsto.comp hp
    change Tendsto (fun s => schrodingerFlow s (lowerSobolevInclusion (slope v t s)))
      (𝓝[≠] t) (𝓝 (schrodingerFlow t (lowerSobolevInclusion v'))) at h
    have hreal (s c : ℝ) (z : FourierL2) : schrodingerFlow s (c • z) = c • schrodingerFlow s z :=
      (schrodingerFlow s).toLinearMap.map_smul_of_tower c z
    apply h.congr'
    filter_upwards with s
    simp [w, slope, hreal]
  have hfixed := hasDerivAt_lowerSobolev_schrodingerFlow (v t) t
  convert hfixed.add hw using 1
  funext s
  dsimp [w]
  rw [← map_add, ← map_add]
  congr 2
  abel

/-- The local interaction solution gives the nonlinear Schrödinger equation in `H^(k-2)`. -/
theorem hasDerivAt_of_schrodingerInteraction
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v : ℝ → FourierL2) (t : ℝ)
    (hv : HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t) :
    HasDerivAt (fun s => lowerSobolevInclusion (schrodingerFlow s (v s)))
      (lowerSobolevGenerator (schrodingerFlow t (v t)) -
        Complex.I • lowerSobolevInclusion
          (sobolevOddPower k hk m (schrodingerFlow t (v t)))) t := by
  have h := hasDerivAt_lowerSobolev_schrodingerCurve v _ t hv
  convert h using 1
  · funext s
    exact lowerSobolevInclusion_schrodingerFlow s (v s)
  · rw [lowerSobolevGenerator_schrodingerFlow]
    unfold schrodingerInteractionField
    rw [map_smul, lowerSobolevInclusion_schrodingerFlow, map_smul,
      ← schrodingerFlow_add]
    simp [sub_eq_add_neg]

/-- A continuous Sobolev curve remains continuous after free evolution. -/
theorem continuousOn_schrodingerFlow_curve (v : ℝ → FourierL2) (J : Set ℝ)
    (hv : ContinuousOn v J) : ContinuousOn (fun s => schrodingerFlow s (v s)) J := by
  intro t ht
  have hp : ContinuousWithinAt (fun s : ℝ => (s, v s)) J t :=
    (continuousWithinAt_id : ContinuousWithinAt (id : ℝ → ℝ) J t).prodMk (hv t ht)
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun s : ℝ => (s, v s))
    (g := fun p : ℝ × FourierL2 => schrodingerFlow p.1 p.2)
    (continuous_schrodingerFlow_uncurry.continuousAt (x := (t, v t))) hp

/-- Every initial Sobolev vector admits a local solution of the actual semilinear equation. -/
theorem exists_local_sobolevSchrodingerSolution
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → FourierL2, u 0 = f₀ ∧
      ContinuousOn u (Ioo (-T) T) ∧
      ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun s => lowerSobolevInclusion (u s))
          (lowerSobolevGenerator (u t) -
            Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t := by
  obtain ⟨T, hT, v, hv₀, hv⟩ := exists_sobolevInteractionSolution k hk m f₀
  let u : ℝ → FourierL2 := fun s => schrodingerFlow s (v s)
  refine ⟨T, hT, u, by simp [u, hv₀], ?_, ?_⟩
  · have hvc : ContinuousOn v (Ioo (-T) T) := fun t ht => (hv t ht).continuousAt.continuousWithinAt
    exact continuousOn_schrodingerFlow_curve v _ hvc
  · intro t ht
    exact hasDerivAt_of_schrodingerInteraction k hk m v t (hv t ht)

/-- The nonlinear Sobolev equation gives the usual time derivative at every torus point. -/
theorem hasDerivAt_nonlinearTorusFunction
    (k : ℝ) (hk : 8 < k) (m : ℕ) (u : ℝ → FourierL2)
    (t : ℝ) (x : SchrodingerTorus)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k (by linarith) m (u t))) t) :
    HasDerivAt (fun s => sobolevTorusFunction k (u s) x)
      (Complex.I * torusFourierLaplacian k (u t) x -
        Complex.I * oddPowerNonlinearity m (sobolevTorusFunction k (u t) x)) t := by
  let E := (sobolevPointEvaluation (k - 2) (by linarith) x).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt t hu
  have hinc (f : FourierL2) : E (lowerSobolevInclusion f) = sobolevTorusFunction k f x := by
    change sobolevPointEvaluation (k - 2) (by linarith) x (lowerSobolevInclusion f) = _
    rw [← sobolevTorusFunction_apply, sobolevTorusFunction_lower_inclusion]
  have hgen (f : FourierL2) : E (lowerSobolevGenerator f) =
      Complex.I * torusFourierLaplacian k f x := by
    change sobolevPointEvaluation (k - 2) (by linarith) x (lowerSobolevGenerator f) = _
    simp only [torusFourierLaplacian, sobolevTorusFunction_apply (k - 2) (by linarith), map_smul,
      smul_eq_mul]
    simp [← mul_assoc]
  have hderiv : E (lowerSobolevGenerator (u t) -
      Complex.I • lowerSobolevInclusion (sobolevOddPower k (by linarith) m (u t))) =
      Complex.I * torusFourierLaplacian k (u t) x -
        Complex.I * oddPowerNonlinearity m (sobolevTorusFunction k (u t) x) := by
    change sobolevPointEvaluation (k - 2) (by linarith) x _ = _
    rw [map_sub, map_smul]
    change E (lowerSobolevGenerator (u t)) -
      Complex.I * E (lowerSobolevInclusion (sobolevOddPower k (by linarith) m (u t))) = _
    rw [hgen, hinc]
    rw [sobolevOddPower_apply]
  simpa only [Function.comp_def, hinc, hderiv] using h

/-- The ordinary twelve-torus Laplacian and the actual odd power satisfy the defocusing PDE. -/
theorem nonlinearTorusFunction_schrodinger_equation
    (k : ℝ) (hk : 8 < k) (m : ℕ) (u : ℝ → FourierL2)
    (t : ℝ) (x : SchrodingerTorus)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k (by linarith) m (u t))) t) :
    Complex.I * deriv (fun s => sobolevTorusFunction k (u s) x) t +
      (∑ j : Fin 12, deriv (deriv
        (fun r => sobolevTorusFunction k (u t) (torusCoordinateLine x j r))) 0) -
      oddPowerNonlinearity m (sobolevTorusFunction k (u t) x) = 0 := by
  rw [(hasDerivAt_nonlinearTorusFunction k hk m u t x hu).deriv,
    sum_coordinate_second_derivative_eq_laplacian k hk]
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

end DefocusingNLS

end OAI
