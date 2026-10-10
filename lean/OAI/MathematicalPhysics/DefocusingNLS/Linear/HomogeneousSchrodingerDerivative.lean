import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchrodingerContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLaplacianFrequency
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDifferentiation
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Strong Schrödinger differentiation for the physical Laplacian domain -/

open Filter MeasureTheory Set
open scoped Laplacian RealInnerProductSpace

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_homogeneousSchrodingerPhase (t : ℝ) (ξ : E) :
    HasDerivAt (fun s => homogeneousSchrodingerPhase s ξ)
      (homogeneousSchrodingerPhase t ξ * ((-(‖ξ‖ ^ 2 : ℝ) : ℂ) * Complex.I)) t := by
  have h := (((hasDerivAt_id t).neg.mul_const (‖ξ‖ ^ 2)).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1 <;> simp only [homogeneousSchrodingerPhase, Pi.neg_apply, id_eq, neg_mul, one_mul,
    Complex.ofReal_neg]

private theorem physical_derivative (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q qL : HomogeneousY a k)
    (hL : (qL : E → ℂ) =ᵐ[volume] (fun ξ => (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * q ξ))
    (t : ℝ) (x : E) :
    HasDerivAt (fun s => homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousSchrodingerOperator a k s q) x)
      (homogeneousPhysicalCLM a k ha ha1 hk
        (Complex.I • homogeneousSchrodingerOperator a k t qL) x) t := by
  let P := fun ξ : E => Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I)
  have hP : Continuous P := by dsimp only [P]; fun_prop
  have hnP (ξ : E) : ‖P ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  let F := fun s ξ => P ξ * homogeneousSchrodingerPhase s ξ * q ξ
  let D := fun s ξ => P ξ * homogeneousSchrodingerPhase s ξ * (Complex.I * qL ξ)
  have hq := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp q)).1
  have hqL := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp qL)).1
  have hFm (s : ℝ) : AEStronglyMeasurable (F s) volume :=
    (hP.mul (homogeneousSchrodingerPhase_continuous s)).aestronglyMeasurable.mul hq.aestronglyMeasurable
  have hDm (s : ℝ) : AEStronglyMeasurable (D s) volume :=
    (hP.mul (homogeneousSchrodingerPhase_continuous s)).aestronglyMeasurable.mul
      (hqL.const_mul Complex.I).aestronglyMeasurable
  have hDi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (x₀ := t) (s := univ) (F := F) (F' := D) (bound := fun ξ => ‖qL ξ‖)
    (by simp) (Eventually.of_forall hFm)
    (hq.norm.mono' (hFm t) (ae_of_all _ fun ξ => by
      dsimp only [F]; simp only [norm_mul, hnP, homogeneousSchrodingerPhase_norm, one_mul]; exact le_rfl))
    (hDm t)
    (ae_of_all _ fun ξ s _ => by
      dsimp only [D]; simp only [norm_mul, hnP, homogeneousSchrodingerPhase_norm, Complex.norm_I, one_mul]; exact le_rfl)
    hqL.norm
    (by
      filter_upwards [hL] with ξ hξ
      intro s _
      have hd := ((hasDerivAt_homogeneousSchrodingerPhase s ξ).const_mul (P ξ)).mul_const (q ξ)
      convert hd using 1
      dsimp only [D]
      rw [hξ]
      ring)
  let N : ℂ := (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ)
  have he (s : ℝ) : homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousSchrodingerOperator a k s q) x = N * ∫ ξ, F s ξ := by
    rw [homogeneousSchrodingerOperator_physical]
    simp only [inverseRadianFourier, radianFourierIntegral, inner_neg_right, neg_neg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [F, P]
    ring
  have hd : homogeneousPhysicalCLM a k ha ha1 hk
      (Complex.I • homogeneousSchrodingerOperator a k t qL) x = N * ∫ ξ, D t ξ := by
    rw [map_smul]
    change Complex.I * homogeneousPhysicalCLM a k ha ha1 hk
      (homogeneousSchrodingerOperator a k t qL) x = _
    rw [homogeneousSchrodingerOperator_physical]
    simp only [inverseRadianFourier, radianFourierIntegral, inner_neg_right, neg_neg]
    change Complex.I * (N * ∫ ξ, P ξ * (homogeneousSchrodingerPhase t ξ * qL ξ)) = _
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [D]
    ring
  simp_rw [he]
  rw [hd]
  exact hDi.2.const_mul N

theorem hasDerivAt_homogeneousSchrodinger (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q qL : HomogeneousY a k)
    (hL : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk qL x =
      Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) x) (t : ℝ) :
    HasDerivAt (fun s => homogeneousSchrodingerOperator a k s q)
      (Complex.I • homogeneousSchrodingerOperator a k t qL) t := by
  apply hasDerivAt_homogeneous_of_physical a k ha ha1 hk
    (fun s => homogeneousSchrodingerOperator a k s q)
    (fun s => Complex.I • homogeneousSchrodingerOperator a k s qL)
    ((continuous_homogeneousSchrodingerOperator a k qL).const_smul Complex.I)
  exact physical_derivative a k ha ha1 hk q qL (homogeneous_laplacian_frequency a k ha ha1 hk q qL hL)

end DefocusingNLS

end OAI
