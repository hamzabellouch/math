import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactOrbitalDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedCompactQuadrature

namespace OAI

/-! The transported fourth-order rule applied to the actual compact
orbital transition density, with all source bounds discharged. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_compact_orbital_quadrature {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (R : ℝ), 1 ≤ R → ∀ (v w : PlanarPosition),
      ∀ (scale S : ℝ), 1 ≤ S → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf (compactOrbitalDensity freq R v w) (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf (compactOrbitalDensity freq R v w) (G x)))| ≤
        (24*((2*Real.pi+1)*(64*B*R^3))*D^4*(216*m*S+13824*R^3)+
          2048*Real.pi*C*(64*B*R^3))*h^4 := by
  obtain ⟨B,hB,hb⟩ := compactOrbitalDensity_jets_bounded hfreq
  obtain ⟨C,hC,hquad⟩ := manufactured_compact_source_quadrature
  refine ⟨B,C,hB,hC,?_⟩
  intro R hR v w scale S hS m u G hG hfix D hD hGD ι _ index hindex h hh hh1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hBR : B ≤ 64*B*R^3 := by
    have hpow : 1 ≤ R^3 := one_le_pow₀ hR
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ B by linarith)
    nlinarith
  have he := hquad (compactOrbitalDensity freq R v w)
    (compactOrbitalDensity_C4 freq R v w) (compactOrbitalDensity_hasCompactSupport freq hR0 v w)
    (64*B*R^3) (by positivity)
    (fun k hk x => ((hb R hR v w k hk).1 x).trans hBR)
    (fun k hk => (hb R hR v w k hk).2) v (2*R) (by linarith)
    (fun x hx => by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using
        compactOrbitalDensity_support freq hR0 v w (subset_tsupport _ hx))
    freq scale S hS m u G hG hfix D hD hGD index hindex h hh hh1
  convert he using 1
  ring

end ContinuumCoulomb

end

end OAI
