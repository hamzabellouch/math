import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointBadProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

theorem preparedShortForecastCertificateSpecialization
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {B0 Bcert Elog gainLog Vlog : ℝ} {Q : ℕ}
    (hcert : ∀ B : ℝ, B0 ≤ B →
      PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M)
        prep U b S B Elog Vlog Q)
    (hbase : B0 ≤ Bcert) (hlog : Elog = gainLog + 8) :
    PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M)
      prep U b S Bcert (gainLog + 8) Vlog Q := by
  rw [← hlog]
  exact hcert Bcert hbase

end Erdos3.VectorPolynomial

end

end OAI
