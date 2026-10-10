import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorGround
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGroundComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ThirdOrderScale

namespace OAI

/-! The actual parallel gadget approximates its intended finite Hamiltonian,
including the residual left by the common counterterm. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaThirdOrderBottom_eq (g : ℝ) (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Perturbation.thirdOrderBottom ((qmaMatrixOperator L).restrictScalars ℝ)
      (qmaPaddedInverse g) (qmaComplementOperator L D V) (qmaCouplingOperator V) =
        MediatorGraph.normalizedBottom (qmaThirdMatrix L D V (g:ℂ)) := by
  unfold Perturbation.thirdOrderBottom MediatorGraph.normalizedBottom
  congr 1
  ext e
  constructor <;> rintro ⟨p,hp,he⟩ <;> refine ⟨p,hp,?_⟩
  · rw [qmaActual_thirdOrderForm] at he
    simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using he
  · rw [qmaActual_thirdOrderForm]
    simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using he

theorem qmaThirdSeries_target_ground (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) {R K : ℝ} (hK : 1 ≤ K) (hR : 4*K ≤ R)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (hC : ∀ e, (C e).conjTranspose = C e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (J e))
    (hLstar : (qmaThirdSeriesLow H A B C R J).conjTranspose = qmaThirdSeriesLow H A B C R J)
    (hL : ‖spinMatrixOperator (qmaThirdSeriesLow H A B C R J)‖ ≤ K*R)
    (hPsq : ∑ e, ‖spinMatrixOperator (qmaThirdSeriesPair (A e) (B e) (J e))‖^2 ≤ K)
    (hTarget : ‖spinMatrixOperator (qmaThirdSeriesTarget H A B C J)‖ ≤ K)
    (hPert : ‖qmaPerturbationOperator (qmaThirdSeriesLow H A B C R J)
      (fun e => (R^2 : ℝ) • C e)
      (fun e => (R^2 : ℝ) • qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤ K*R^2)
    (hCouple : ∑ e, ‖spinMatrixOperator ((R^2 : ℝ) •
      qmaThirdSeriesPair (A e) (B e) (J e))‖ ≤ R^3*(K/R))
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix (R^3)
        (qmaThirdSeriesLow H A B C R J) (fun e => (R^2 : ℝ) • C e)
        (fun e => (R^2 : ℝ) • qmaThirdSeriesPair (A e) (B e) (J e)))-
      MediatorGraph.normalizedBottom (qmaThirdSeriesTarget H A B C J)| ≤ 5*K^4/R := by
  let L := qmaThirdSeriesLow H A B C R J
  let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
  let D := fun e => (R^2 : ℝ) • C e
  let V := fun e => (R^2 : ℝ) • P e
  let M := qmaThirdMatrix L D V (R^3 : ℝ)
  let T := qmaThirdSeriesTarget H A B C J
  let E := ((R:ℂ)⁻¹)^2 • (∑ e, P e*L*P e)
  have hRp : 0 < R := by linarith
  have hKp : 0 ≤ K := by linarith
  have hident : M = T+E := qmaThirdMatrix_target H A B C R J hRp.ne' hA hB hAB hAC hBC hP
  have hE : ‖spinMatrixOperator E‖ ≤ K^2/R :=
    qmaThirdResidual_polynomial_bound L P hRp hKp hPsq hL
  have hsmallE : K^2/R ≤ K := by
    apply (div_le_iff₀ hRp).mpr
    nlinarith
  have hM : ‖spinMatrixOperator M‖ ≤ 2*K := by
    rw [hident,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans ((add_le_add hTarget (hE.trans hsmallE)).trans_eq (by ring))
  have hDstar (e : κ) : (D e).conjTranspose = D e := by
    change ((R^2 : ℝ) • C e).conjTranspose = (R^2 : ℝ) • C e
    simp only [Matrix.conjTranspose_smul,star_trivial,hC]
  have hVstar (e : κ) : (V e).conjTranspose = V e := by
    change ((R^2 : ℝ) • P e).conjTranspose = (R^2 : ℝ) • P e
    have hPe : (P e).conjTranspose = P e := hP e
    rw [Matrix.conjTranspose_smul,star_trivial,hPe]
  have hbound (p : EuclideanSpace ℂ σ) (hp : ‖p‖ = 1) :
      |qmaQuadratic M (fun i => p i)| ≤ 2*K := by
    have hb := (qmaQuadratic_norm_bound M p).trans
      (mul_le_mul_of_nonneg_right hM (sq_nonneg ‖p‖))
    simpa only [hp,one_pow,mul_one] using hb
  have hg : 0 < R^3 := pow_pos hRp 3
  have hground := qmaPhysical_thirdOrder_ground (R^3) L D V hg hLstar hDstar hVstar
    (show 0 ≤ K*R^2 by positivity) (show 0 ≤ 2*K by positivity)
    (Perturbation.thirdOrder_scale_small hK hR) hPert hCouple hbound u hu
  rw [qmaThirdOrderBottom_eq] at hground
  have hMT : |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom T| ≤ K^2/R := by
    apply qmaNormalizedBottom_norm_error M T u hu
    simpa only [hident,add_sub_cancel_left] using hE
  have hK24 : K^2 ≤ K^4 := by
    exact pow_le_pow_right₀ hK (by omega : (2:ℕ) ≤ 4)
  calc
    _ ≤ |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix (R^3) L D V)-
          MediatorGraph.normalizedBottom M|+
        |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom T| := abs_sub_le _ _ _
    _ ≤ (2*(K*R^2)^2/R^3+2*(2*K))*(K/R)^2+K^2/R := add_le_add hground hMT
    _ ≤ 4*K^4/R+K^4/R := add_le_add (Perturbation.thirdOrder_scale_error hK hR)
      (div_le_div_of_nonneg_right hK24 hRp.le)
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
