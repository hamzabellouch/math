import OAI.Probability.InvariantIsing.Spectral.SpectralWardLimits

namespace OAI

/-! The spectral off-diagonal residual as a direct minus fresh replica
expectation, matching the finite rotation calculation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def spectralOffWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (x : SpectralArray (m + 1)) : ℝ :=
  Φ (spectralSpinArray x 0 1) *
    (ρ a * (x (0,1) b.castSucc : ℝ) - ρ b * (x (0,1) a.castSucc : ℝ) +
      (eig a - eig b) * ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
        (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ)))

def spectralOffWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (x : SpectralArray (m + 1)) : ℝ :=
  (eig a - eig b) * Φ (spectralSpinArray x 0 1) *
    (x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ)

lemma continuous_spectralOffWardDirect {m : ℕ} (ρ eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) : Continuous (spectralOffWardDirect ρ eig a b Φ) := by
  unfold spectralOffWardDirect spectralSpinArray
  fun_prop

lemma continuous_spectralOffWardFresh {m : ℕ} (eig : Fin m → ℝ) (a b : Fin m)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) : Continuous (spectralOffWardFresh eig a b Φ) := by
  unfold spectralOffWardFresh spectralSpinArray
  fun_prop

lemma spectralOffWardResidual_eq_direct_fresh {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (ρ eig : Fin m → ℝ) (a b : Fin m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    spectralOffWardResidual Q ρ eig a b Φ =
      (∫ x, spectralOffWardDirect ρ eig a b Φ x ∂(Q : Measure _)) -
        2 * ∫ x, spectralOffWardFresh eig a b Φ x ∂(Q : Measure _) := by
  let u := fun x : SpectralArray (m + 1) => Φ (spectralSpinArray x 0 1) * (x (0,1) b.castSucc : ℝ)
  let v := fun x : SpectralArray (m + 1) => Φ (spectralSpinArray x 0 1) * (x (0,1) a.castSucc : ℝ)
  let w := fun x : SpectralArray (m + 1) => Φ (spectralSpinArray x 0 1) *
    ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
      (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ))
  let z := fun x : SpectralArray (m + 1) => Φ (spectralSpinArray x 0 1) *
    ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))
  have hu : Integrable u (Q : Measure _) := compact_integrable (by dsimp only [u, spectralSpinArray]; fun_prop)
  have hv : Integrable v (Q : Measure _) := compact_integrable (by dsimp only [v, spectralSpinArray]; fun_prop)
  have hw : Integrable w (Q : Measure _) := compact_integrable (by dsimp only [w, spectralSpinArray]; fun_prop)
  have hz : Integrable z (Q : Measure _) := compact_integrable (by dsimp only [z, spectralSpinArray]; fun_prop)
  have hd : spectralOffWardDirect ρ eig a b Φ = fun x => ρ a * u x - ρ b * v x + (eig a - eig b) * w x := by
    funext x
    dsimp only [spectralOffWardDirect, u, v, w]
    ring
  have hf : spectralOffWardFresh eig a b Φ = fun x => (eig a - eig b) * z x := by
    funext x
    dsimp only [spectralOffWardFresh, z]
    ring
  have hp : (fun x : SpectralArray (m + 1) => Φ (spectralSpinArray x 0 1) *
      ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
        (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ) -
        2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ)))) = fun x => w x - 2 * z x := by
    funext x
    dsimp only [w, z]
    ring
  unfold spectralOffWardResidual
  rw [hd, hf, hp]
  have hdi : (∫ x, ρ a * u x - ρ b * v x + (eig a - eig b) * w x ∂(Q : Measure _)) =
      (∫ x, ρ a * u x - ρ b * v x ∂(Q : Measure _)) +
        ∫ x, (eig a - eig b) * w x ∂(Q : Measure _) :=
    integral_add ((hu.const_mul (ρ a)).sub (hv.const_mul (ρ b))) (hw.const_mul (eig a - eig b))
  rw [hdi, integral_sub (hu.const_mul (ρ a)) (hv.const_mul (ρ b)), integral_sub hw (hz.const_mul 2)]
  simp only [integral_const_mul]
  dsimp only [u, v]
  ring

end InvariantIsing

end

end OAI
