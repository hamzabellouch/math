import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerGenerator

namespace OAI

/-!
# The free equation on the actual twelve-torus

The Fourier Sobolev model embeds continuously into continuous functions for
`k>6`. For `k>8`, free evolution is differentiable in the continuous-function
norm, and its derivative is `i` times the continuous Fourier Laplacian.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- The Fourier representation is a bounded linear map into continuous functions. -/
noncomputable def sobolevTorusEmbedding (k : ℝ) (hk : 6 < k) :
    FourierL2 →L[ℂ] C(SchrodingerTorus, ℂ) :=
  LinearMap.mkContinuous
    { toFun := sobolevTorusFunction k
      map_add' := by
        intro f g
        ext x
        simp only [ContinuousMap.add_apply, sobolevTorusFunction_apply k hk, map_add]
      map_smul' := by
        intro c f
        ext x
        simp only [ContinuousMap.smul_apply, sobolevTorusFunction_apply k hk,
          map_smul, RingHom.id_apply] }
    ‖sobolevObservationVector k hk‖ (by
      intro f
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro x
      change ‖sobolevTorusFunction k f x‖ ≤ ‖sobolevObservationVector k hk‖ * ‖f‖
      rw [sobolevTorusFunction_apply k hk]
      exact sobolevPointEvaluation_bound k hk x f)

@[simp] theorem sobolevTorusEmbedding_apply (k : ℝ) (hk : 6 < k) (f : FourierL2) :
    sobolevTorusEmbedding k hk f = sobolevTorusFunction k f := rfl

/-- Lowering the index of a Sobolev vector preserves its continuous torus function. -/
theorem sobolevTorusFunction_lower_inclusion (k : ℝ) (f : FourierL2) :
    sobolevTorusFunction (k - 2) (lowerSobolevInclusion f) = sobolevTorusFunction k f := by
  unfold sobolevTorusFunction
  congr 1
  funext n
  simp only [sobolevTorusTerm, sobolevFourierCoefficient_lower_inclusion]

theorem lowerSobolevInclusion_schrodingerFlow (t : ℝ) (f : FourierL2) :
    lowerSobolevInclusion (schrodingerFlow t f) =
      schrodingerFlow t (lowerSobolevInclusion f) := by
  ext n
  simp only [lowerSobolevInclusion_apply, schrodingerFlow_apply]
  ring

theorem lowerSobolevGenerator_schrodingerFlow (t : ℝ) (f : FourierL2) :
    lowerSobolevGenerator (schrodingerFlow t f) =
      schrodingerFlow t (lowerSobolevGenerator f) := by
  ext n
  simp only [lowerSobolevGenerator_apply, schrodingerFlow_apply]
  ring

/-- The spectral Laplacian, represented as a continuous function for `k>8`. -/
noncomputable def torusFourierLaplacian (k : ℝ) (f : FourierL2) :
    C(SchrodingerTorus, ℂ) :=
  sobolevTorusFunction (k - 2) (-Complex.I • lowerSobolevGenerator f)

/-- The Fourier Laplacian has precisely the multiplier `-|n|²`. -/
theorem sobolevFourierCoefficient_laplacian (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    sobolevFourierCoefficient (k - 2) (-Complex.I • lowerSobolevGenerator f) n =
      -((‖n‖ ^ 2 : ℝ) : ℂ) * sobolevFourierCoefficient k f n := by
  rw [← sobolevFourierCoefficient_lower_inclusion k f n]
  unfold sobolevFourierCoefficient
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def,
    lowerSobolevGenerator_apply,
    lowerSobolevInclusion_apply, Complex.ofReal_div, Complex.ofReal_inv]
  have hi := Complex.I_sq
  linear_combination
    (((1 + ‖n‖ ^ 2) ^ (-(k - 2) / 2) : ℝ) : ℂ) *
      (((1 + ‖n‖ ^ 2 : ℝ) : ℂ)⁻¹ * f n * ((‖n‖ ^ 2 : ℝ) : ℂ)) * hi

/-- The Laplacian Fourier series converges absolutely and defines the stated function. -/
theorem hasSum_torusFourierLaplacian (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) :
    HasSum (fun n => -((‖n‖ ^ 2 : ℝ) : ℂ) * sobolevFourierCoefficient k f n *
      torusCharacter n x) (torusFourierLaplacian k f x) := by
  have h := hasSum_sobolevPointEvaluation (k - 2) (by linarith) x
    (-Complex.I • lowerSobolevGenerator f)
  simpa only [sobolevFourierCoefficient_laplacian,
    ← sobolevTorusFunction_apply, torusFourierLaplacian] using h

/-- The free evolution, represented by continuous functions on the torus. -/
noncomputable def freeTorusEvolution (k : ℝ) (f : FourierL2) (t : ℝ) :
    C(SchrodingerTorus, ℂ) := sobolevTorusFunction k (schrodingerFlow t f)

/-- Free evolution solves the spectral Schrödinger equation in the continuous-function norm. -/
theorem hasDerivAt_freeTorusEvolution (k : ℝ) (hk : 8 < k) (f : FourierL2) (t : ℝ) :
    HasDerivAt (freeTorusEvolution k f)
      (Complex.I • torusFourierLaplacian k (schrodingerFlow t f)) t := by
  let E := (sobolevTorusEmbedding (k - 2) (by linarith)).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_lowerSobolev_schrodingerFlow f t)
  have hfun : (fun s => E (schrodingerFlow s (lowerSobolevInclusion f))) =
      freeTorusEvolution k f := by
    funext s
    change sobolevTorusFunction (k - 2) (schrodingerFlow s (lowerSobolevInclusion f)) = _
    rw [← lowerSobolevInclusion_schrodingerFlow, sobolevTorusFunction_lower_inclusion]
    rfl
  have hderiv : E (schrodingerFlow t (lowerSobolevGenerator f)) =
      Complex.I • torusFourierLaplacian k (schrodingerFlow t f) := by
    change sobolevTorusEmbedding (k - 2) (by linarith)
      (schrodingerFlow t (lowerSobolevGenerator f)) = _
    rw [← lowerSobolevGenerator_schrodingerFlow]
    unfold torusFourierLaplacian
    rw [← sobolevTorusEmbedding_apply (k - 2) (by linarith), map_smul, smul_smul]
    simp
  simpa only [Function.comp_def, hfun, hderiv] using h

/-- At every point of the torus, the time derivative equals `i` times the Fourier Laplacian. -/
theorem hasDerivAt_freeTorusEvolution_point (k : ℝ) (hk : 8 < k) (f : FourierL2)
    (x : SchrodingerTorus) (t : ℝ) :
    HasDerivAt (fun s => freeTorusEvolution k f s x)
      (Complex.I * torusFourierLaplacian k (schrodingerFlow t f) x) t := by
  let E : C(SchrodingerTorus, ℂ) →L[ℝ] ℂ :=
    (ContinuousMap.evalCLM (R := ℂ) x).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_freeTorusEvolution k hk f t)
  simpa [E, Function.comp_def] using h

end DefocusingNLS

end OAI
