import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSupportedMean

namespace OAI

/-! The complete retained norm-block mean for the original coefficients.
The supported parametrization and every free coefficient estimate are
constructed from the precisely stated published Voronoi coefficient bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_actual_norm_block_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (I T : ℝ),
      0 < I → 0 < T →
      (∀ nd ∈ S, I/2 ≤ metaplecticDualNorm nd ∧ metaplecticDualNorm nd ≤ I) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          D*(3*I)^(3*ε/2)*norm r^(2*ε)*(1+Real.sqrt (2*I/(norm r*T))) := by
  obtain ⟨C,hC,hcodes⟩ := metaplectic_retained_support_partition ha
  obtain ⟨D,hD,hmean⟩ := metaplectic_supported_block_mean hε hMV hM
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro r hr hsr S I T hI hT hdyad ℓ τ
  obtain ⟨U,hU,he⟩ := hcodes r hr hsr S
  have huc (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      IsCoprime z.2.2.val r := (hU z hz).2.2.1
  have hus (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      ∃ k : ℕ, z.2.1.2.2.2.val ∣ r^k := (hU z hz).2.1
  have hub (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      ‖a r (metaplecticRetainedDecode r z).1‖ ≤
        C*3^((max ((z.2.1.1:ℤ)-1) 0:ℤ)/3:ℝ)*Real.sqrt (norm z.2.1.2.2.2) :=
    (hU z hz).2.2.2.2
  have hud (z : MetaplecticRetainedCode r) (hz : z ∈ U) :
      I/2 ≤ metaplecticDualNorm (metaplecticRetainedDecode r z) ∧
        metaplecticDualNorm (metaplecticRetainedDecode r z) ≤ I :=
    hdyad _ (hU z hz).1
  have hb := hmean a C hC.le r hr U huc hus hub I T hI hT hud ℓ τ
  have hid (t : ℝ) :
      (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ-t) (metaplecticDualNorm nd)) =
      ∑ z ∈ U, metaplecticNormalizedDualCoefficient a r ℓ (metaplecticRetainedDecode r z)*
        mellinPhase (τ-t) (metaplecticDualNorm (metaplecticRetainedDecode r z)) := he ℓ (τ-t)
  simp_rw [hid]
  exact hb

end CubicFirstMoment

end

end OAI
