import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactOrbitalQuadrature
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactNuclearPairing

namespace OAI

/-! Fourth-order nuclear replacement for the actual cutoff orbital
transition densities, with every analytic source estimate discharged. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufactured_compact_orbital_nuclear_error (hpublished : PublishedC4FlowInput)
    {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (R : ℝ), 1 ≤ R → ∀ (v w : PlanarPosition),
      ∀ (rho H S scale : ℝ), 0 < rho → 0 ≤ H → 1 ≤ S →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      (∀ x, |manufacturedCharge (manufacturedWellField freq scale S u) x| ≤ rho/2) →
      tsupport (manufacturedWellField freq scale S u) ⊆ slabDomain H S →
      ∀ (G : Position → ℝ → Position),
      IsUnitTimeFlow (moserVelocity rho (manufacturedWellField freq scale S u)) G →
      Function.Bijective (fun x => G x 1) →
      ContDiff ℝ 4 (fun x => G x 1) →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x 1 = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k (fun x => G x 1) x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) = slabDomain H S →
      |∫ y, (gridNuclearPotential index (fun x => G x 1) rho h y-
          (slabPotential rho H S y+manufacturedWellField freq scale S u y))*
          compactOrbitalDensity freq R v w y| ≤
        rho*(24*((2*Real.pi+1)*(64*B*R^3))*D^4*(216*m*S+13824*R^3)+
          2048*Real.pi*C*(64*B*R^3))*h^4 := by
  obtain ⟨B,C,hB,hC,hq⟩ := manufactured_compact_orbital_quadrature hfreq
  refine ⟨B,C,hB,hC,?_⟩
  intro R hR v w rho H S scale hrho hH hS m u hcharge hsupp G hflow hbij hG hfix D hD hGD
    ι _ index hindex h hh hh1 hcover
  rw [manufactured_compact_nuclear_pairing hpublished hrho hH (by linarith) hh
    (manufacturedWellField freq scale S u) ((manufacturedWellField_C7 freq scale S u).of_le (by norm_num))
    (manufacturedWellField_compact freq scale (by linarith) u) hcharge hsupp G hflow hbij hfix hG.continuous
    index hindex hcover (compactOrbitalDensity_C4 freq R v w)
    (compactOrbitalDensity_hasCompactSupport freq (by linarith) v w)
    (compactOrbitalDensity_nonnegative hfreq R v w)]
  rw [abs_mul,abs_neg,abs_of_pos hrho]
  exact (mul_le_mul_of_nonneg_left
    (hq R hR v w scale S hS m u (fun x => G x 1) hG hfix D hD hGD index hindex h hh hh1)
    hrho.le).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
