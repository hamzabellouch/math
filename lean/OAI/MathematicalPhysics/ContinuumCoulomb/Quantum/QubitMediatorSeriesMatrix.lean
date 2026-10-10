import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumThirdCounterterm
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorMatrix

namespace OAI

/-! Exact simultaneous cancellation for the polynomial third-order gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

def qmaThirdSeriesLow (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℂ) (J : κ → ℂ) : Matrix σ σ ℂ :=
  H+∑ e, qmaThirdSeriesCounter (A e) (B e) (C e) r (J e)

def qmaThirdSeriesTarget (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (J : κ → ℂ) : Matrix σ σ ℂ := H+∑ e, J e • (A e*B e*C e)

theorem qmaThirdSeries_sum_effective (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℂ) (J : κ → ℂ) (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e) :
    qmaThirdSeriesLow H A B C r J-
      ∑ e, r • (qmaThirdSeriesPair (A e) (B e) (J e)*qmaThirdSeriesPair (A e) (B e) (J e))+
      ∑ e, qmaThirdSeriesPair (A e) (B e) (J e)*C e*qmaThirdSeriesPair (A e) (B e) (J e) =
        qmaThirdSeriesTarget H A B C J := by
  calc
    _ = H+∑ e, (qmaThirdSeriesCounter (A e) (B e) (C e) r (J e)-
        r • (qmaThirdSeriesPair (A e) (B e) (J e)*qmaThirdSeriesPair (A e) (B e) (J e))+
        qmaThirdSeriesPair (A e) (B e) (J e)*C e*qmaThirdSeriesPair (A e) (B e) (J e)) := by
      simp only [qmaThirdSeriesLow,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      abel
    _ = _ := by
      unfold qmaThirdSeriesTarget
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      exact qmaThirdSeries_effective _ _ _ _ _ (hA e) (hB e) (hAB e) (hAC e) (hBC e)

def qmaThirdMatrix (L : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) (g : ℂ) : Matrix σ σ ℂ :=
  L-g⁻¹ • (∑ e, (V e).conjTranspose*V e)+
    (g⁻¹)^2 • ((∑ e, (V e).conjTranspose*L*V e)+(∑ e, (V e).conjTranspose*D e*V e))

theorem qmaThirdMatrix_scaled (L : Matrix σ σ ℂ) (P C : κ → Matrix σ σ ℂ)
    (r : ℝ) (hr : r ≠ 0) (hP : ∀ e, (P e).conjTranspose = P e) :
    qmaThirdMatrix L (fun e => (r^2 : ℝ) • C e) (fun e => (r^2 : ℝ) • P e) (r^3 : ℝ) =
      L-(r : ℂ) • (∑ e, P e*P e)+(∑ e, P e*C e*P e)+
        ((r : ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hfirst : ((r:ℂ)^3)⁻¹*((r:ℂ)^2*(r:ℂ)^2) = r := by field_simp
  have hthird : (((r:ℂ)^3)⁻¹)^2*((r:ℂ)^2*((r:ℂ)^2*(r:ℂ)^2)) = 1 := by field_simp
  have hremain : (((r:ℂ)^3)⁻¹)^2*((r:ℂ)^2*(r:ℂ)^2) = ((r:ℂ)⁻¹)^2 := by field_simp
  have hs (s : ℝ) (M : Matrix σ σ ℂ) : s • M = (s:ℂ) • M := rfl
  unfold qmaThirdMatrix
  simp only [hs,Complex.ofReal_pow,Matrix.conjTranspose_smul,star_pow,Complex.star_def,Complex.conj_ofReal,
    hP,smul_mul_assoc,mul_smul_comm,smul_smul,← Finset.smul_sum,
    smul_add,hfirst,hthird,hremain,one_smul]
  abel

theorem qmaThirdMatrix_target (H : Matrix σ σ ℂ) (A B C : κ → Matrix σ σ ℂ)
    (r : ℝ) (J : κ → ℂ) (hr : r ≠ 0)
    (hA : ∀ e, A e*A e = 1) (hB : ∀ e, B e*B e = 1)
    (hAB : ∀ e, A e*B e = B e*A e) (hAC : ∀ e, A e*C e = C e*A e)
    (hBC : ∀ e, B e*C e = C e*B e)
    (hP : ∀ e, (qmaThirdSeriesPair (A e) (B e) (J e)).conjTranspose =
      qmaThirdSeriesPair (A e) (B e) (J e)) :
    let L := qmaThirdSeriesLow H A B C r J
    let P := fun e => qmaThirdSeriesPair (A e) (B e) (J e)
    qmaThirdMatrix L (fun e => (r^2 : ℝ) • C e) (fun e => (r^2 : ℝ) • P e) (r^3 : ℝ) =
      qmaThirdSeriesTarget H A B C J+((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e) := by
  dsimp only
  rw [qmaThirdMatrix_scaled _ _ _ r hr hP]
  have h := qmaThirdSeries_sum_effective H A B C (r:ℂ) J hA hB hAB hAC hBC
  rw [← Finset.smul_sum] at h
  rw [h]

end ContinuumCoulomb

end

end OAI
