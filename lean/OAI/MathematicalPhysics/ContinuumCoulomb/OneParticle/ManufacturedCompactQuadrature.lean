import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceExceptionalVolume

namespace OAI

/-! Fourth-order quadrature for a compact orbital density under the actual
manufactured transport. The bound depends on the compact source radius and
the well-support volume, and is independent of the horizontal slab area. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem manufactured_compact_source_quadrature :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B) →
      (∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B) →
      ∀ (v : PlanarPosition) (R : ℝ), 1 ≤ R →
      (∀ x, q x ≠ 0 → ‖x-planarCenter v‖ ≤ R) →
      ∀ (freq scale S : ℝ), 1 ≤ S → ∀ (m : ℕ) (u : Fin m → PlanarPosition),
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      (∀ x, x ∉ tsupport (manufacturedWellField freq scale S u) → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ 1 →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))| ≤
        (24*((2*Real.pi+1)*B)*D^4*(216*m*S+1728*R^3)+2048*Real.pi*C*B)*h^4 := by
  classical
  obtain ⟨C,hC,hgrid⟩ := compact_source_grid_error
  refine ⟨C,hC,?_⟩
  intro q hq hc B hB hb hi v R hR hsupp freq scale S hS m u G hG hfix D hD hGD
    ι _ index hindex h hh hh1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hg := hgrid q hq hc B hB hb hi v R hR0 hsupp G hG
    (tsupport (manufacturedWellField freq scale S u)) hfix D hD hGD
    index hindex h hh (hh1.trans hR)
  have hv := source_exceptional_volume index hindex hh hh1 hR0.le hS freq scale u v
  have hvol : (Fintype.card {i // sourceExceptionalCell
      (tsupport (manufacturedWellField freq scale S u)) v R (gaussCellCenter h (index i)) h}:ℝ)*h^3 ≤
      216*m*S+1728*R^3 := by
    apply hv.trans
    have hsize : (4*R+2*h)^3 ≤ (6*R)^3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    nlinarith only [hsize]
  have hnearterm := mul_le_mul_of_nonneg_left hvol
    (show 0 ≤ 24*((2*Real.pi+1)*B)*D^4*h^4 by positivity)
  have hRpow : 1 ≤ R^2 := one_le_pow₀ hR
  have hfar : 2048*Real.pi*C*B*h^4/R^2 ≤ 2048*Real.pi*C*B*h^4 := by
    exact div_le_self (by positivity) hRpow
  apply hg.trans
  nlinarith only [hnearterm,hfar]

end ContinuumCoulomb

end

end OAI
