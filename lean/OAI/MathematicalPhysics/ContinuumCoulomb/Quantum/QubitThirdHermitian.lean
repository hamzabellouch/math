import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorSeriesMatrix

namespace OAI

/-! The polynomial counterterms preserve Hermiticity for real couplings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

omit [Fintype σ] [DecidableEq σ] in
theorem qmaThirdPair_star (A B : Matrix σ σ ℂ) (j : ℝ)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) :
    (qmaThirdSeriesPair A B j).conjTranspose = qmaThirdSeriesPair A B j := by
  have hj : (j:ℂ)/2 = ((j/2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesPair
  rw [hj]
  change (A+(j/2:ℝ) • B).conjTranspose = A+(j/2:ℝ) • B
  rw [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,star_trivial,hA,hB]

theorem qmaThirdCounter_star (A B C : Matrix σ σ ℂ) (r j : ℝ)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) (hC : C.conjTranspose = C)
    (hAB : A*B = B*A) :
    (qmaThirdSeriesCounter A B C r j).conjTranspose = qmaThirdSeriesCounter A B C r j := by
  have hc : 1+((j:ℂ)/2)^2 = ((1+(j/2)^2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesCounter
  rw [hc]
  change ((r:ℝ) • ((1+(j/2)^2:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))-
    (1+(j/2)^2:ℝ) • C).conjTranspose = _
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_one,star_trivial,hA,hB,hC,← hAB]
  rfl

theorem qmaThirdLow_star (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℝ) (J : κ → ℝ) (hH : H.conjTranspose = H)
    (hA : ∀ e, (A e).conjTranspose = A e) (hB : ∀ e, (B e).conjTranspose = B e)
    (hC : ∀ e, (C e).conjTranspose = C e) (hAB : ∀ e, A e*B e = B e*A e) :
    (qmaThirdSeriesLow H A B C r (fun e => J e)).conjTranspose =
      qmaThirdSeriesLow H A B C r (fun e => J e) := by
  simp only [qmaThirdSeriesLow,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hH]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaThirdCounter_star (A e) (B e) (C e) r (J e) (hA e) (hB e) (hC e) (hAB e)

end ContinuumCoulomb

end

end OAI
