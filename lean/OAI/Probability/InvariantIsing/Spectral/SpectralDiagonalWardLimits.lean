import OAI.Probability.InvariantIsing.Spectral.SpectralPartition

namespace OAI

/-! Weak closure of the one-replica diagonal Ward residual. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralDiagonalWardResidual {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (ρ eig : Fin m → ℝ) (a b : Fin m) : ℝ :=
  ρ a * (∫ x, (x (0,0) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) -
  ρ b * (∫ x, (x (0,0) a.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) +
  (eig a - eig b) * (∫ x, (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ) -
    (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1))))

lemma spectralDiagonalWardResidual_constant_diagonal {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1))) (ρ eig : Fin m → ℝ) (a b : Fin m)
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i c, (x (i,i) c : ℝ) = q c) :
    spectralDiagonalWardResidual Q ρ eig a b =
      ρ a * q b.castSucc - ρ b * q a.castSucc +
      (eig a - eig b) * (q a.castSucc * q b.castSucc -
        ∫ x, (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) := by
  have hi (c : Fin m) : (∫ x, (x (0,0) c.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) = q c.castSucc := by
    calc
      _ = ∫ _x, q c.castSucc ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hd] with x hx
        exact hx 0 c.castSucc
      _ = _ := by simp
  have hm : Integrable (fun x : SpectralArray (m + 1) =>
      (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)) (Q : Measure (SpectralArray (m + 1))) :=
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x : SpectralArray (m + 1) => (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ), by fun_prop⟩).integrable _
  have hp : (∫ x, (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ) -
      (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1)))) =
      q a.castSucc * q b.castSucc -
        ∫ x, (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1))) := by
    calc
      _ = ∫ x, q a.castSucc * q b.castSucc -
          (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ) ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hd] with x hx
        rw [hx 0 a.castSucc, hx 0 b.castSucc]
      _ = _ := by rw [integral_sub (integrable_const _) hm]; simp
  simp only [spectralDiagonalWardResidual, hi, hp]

lemma spectralDiagonalWardResidual_weak_limit {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀)) (a b : Fin m) :
    Tendsto (fun n => spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b) atTop
      (𝓝 (spectralDiagonalWardResidual Q ρ₀ eig₀ a b)) := by
  have hI (F : SpectralArray (m + 1) → ℝ) (hF : Continuous F) :
      Tendsto (fun n => ∫ x, F x ∂(L n : Measure (SpectralArray (m + 1)))) atTop
        (𝓝 (∫ x, F x ∂(Q : Measure (SpectralArray (m + 1))))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩)
  have hIa := hI (fun x => (x (0,0) a.castSucc : ℝ)) (by fun_prop)
  have hIb := hI (fun x => (x (0,0) b.castSucc : ℝ)) (by fun_prop)
  have hIp := hI (fun x => (x (0,0) a.castSucc : ℝ) * (x (0,0) b.castSucc : ℝ) -
    (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)) (by fun_prop)
  exact (((tendsto_pi_nhds.mp hρ a).mul hIb).sub
    ((tendsto_pi_nhds.mp hρ b).mul hIa)).add
      (((tendsto_pi_nhds.mp heig a).sub (tendsto_pi_nhds.mp heig b)).mul hIp)

theorem spectralDiagonalWardResidual_zero_of_vanishing_bound {m : ℕ}
    {L : ℕ → ProbabilityMeasure (SpectralArray (m + 1))}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))} (hL : Tendsto L atTop (𝓝 Q))
    {ρ eig : ℕ → Fin m → ℝ} {ρ₀ eig₀ : Fin m → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ρ₀)) (heig : Tendsto eig atTop (𝓝 eig₀)) (a b : Fin m)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ n, |spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b| ≤ ε n) :
    spectralDiagonalWardResidual Q ρ₀ eig₀ a b = 0 := by
  have ht := spectralDiagonalWardResidual_weak_limit hL hρ heig a b
  have hz := squeeze_zero (fun n => abs_nonneg (spectralDiagonalWardResidual (L n) (ρ n) (eig n) a b)) hb hε
  exact abs_eq_zero.mp (tendsto_nhds_unique ht.abs hz)

end InvariantIsing

end

end OAI
