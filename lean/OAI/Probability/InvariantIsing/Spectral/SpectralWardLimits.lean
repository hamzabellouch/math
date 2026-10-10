import OAI.Probability.InvariantIsing.Spectral.SpectralPartition

namespace OAI

/-! Weak closure of the spectral Ward residual, with converging block
proportions and eigenvalues. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralOffWardResidual {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (ρ eig : Fin m → ℝ) (a b : Fin m) (Φ : ℝ → ℝ) : ℝ :=
  ρ a * (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure _)) -
  ρ b * (∫ x, Φ (spectralSpinArray x 0 1) * (x (0,1) a.castSucc : ℝ) ∂(Q : Measure _)) +
  (eig a - eig b) * (∫ x, Φ (spectralSpinArray x 0 1) *
    ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
      (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ) -
      2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))) ∂(Q : Measure _))

lemma spectralOffWardResidual_weak_limit {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀))
    (a b : Fin m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    Tendsto (fun n => spectralOffWardResidual (L n) (ρ n) (eig n) a b Φ) atTop
      (𝓝 (spectralOffWardResidual Q ρ₀ eig₀ a b Φ)) := by
  have hI (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
      Tendsto (fun n => ∫ x, F x ∂(L n : Measure _)) atTop
        (𝓝 (∫ x, F x ∂(Q : Measure _))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hS : Continuous (fun x : SpectralArray (m + 1) => spectralSpinArray x 0 1) := by
    unfold spectralSpinArray
    fun_prop
  have hIa := hI (fun x => Φ (spectralSpinArray x 0 1) * (x (0,1) a.castSucc : ℝ))
    ((hΦ.comp hS).mul (by fun_prop))
  have hIb := hI (fun x => Φ (spectralSpinArray x 0 1) * (x (0,1) b.castSucc : ℝ))
    ((hΦ.comp hS).mul (by fun_prop))
  have hIp := hI (fun x => Φ (spectralSpinArray x 0 1) *
    ((x (0,0) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) +
      (x (0,1) a.castSucc : ℝ) * (x (1,1) b.castSucc : ℝ) -
      2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ))))
    ((hΦ.comp hS).mul (by fun_prop))
  exact (((tendsto_pi_nhds.mp hρ a).mul hIb).sub
    ((tendsto_pi_nhds.mp hρ b).mul hIa)).add
      (((tendsto_pi_nhds.mp heig a).sub (tendsto_pi_nhds.mp heig b)).mul hIp)

theorem spectralOffWardResidual_zero_of_vanishing_bound {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀))
    (a b : Fin m) (Φ : ℝ → ℝ) (hΦ : Continuous Φ)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n, |spectralOffWardResidual (L n) (ρ n) (eig n) a b Φ| ≤ ε n) :
    spectralOffWardResidual Q ρ₀ eig₀ a b Φ = 0 := by
  have ht := spectralOffWardResidual_weak_limit hL hρ heig a b Φ hΦ
  have hz := squeeze_zero (fun n => abs_nonneg (spectralOffWardResidual (L n) (ρ n) (eig n) a b Φ)) hb hε
  exact abs_eq_zero.mp (tendsto_nhds_unique ht.abs hz)

end InvariantIsing

end

end OAI
