import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevLipschitzCover
import OAI.Analysis.CircleDomains.Sobolev.LipschitzPieceGradient

namespace OAI

/-! The actual local Sobolev function and its weak gradient are represented,
on countably many closed pieces of full measure, by global Lipschitz functions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma locally_sobolev_lipschitz_representatives {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) :
    ∃ (K : ℕ × ℕ → Set EuclideanPlane) (g : ℕ × ℕ → EuclideanPlane → ℝ),
      (∀ n, IsClosed (K n) ∧ LipschitzWith (64*(n.2:ℝ≥0)) (g n) ∧ EqOn u (g n) (K n) ∧
        ∀ᵐ p ∂volume.restrict (K n), ∀ i : Fin 2,
          fderiv ℝ (g n) p (EuclideanSpace.single i 1) = V p i) ∧
      ∀ᵐ p ∂volume, p ∈ ⋃ n, K n := by
  obtain ⟨K, hK, hcover⟩ := locally_sobolev_closed_lipschitz_cover hu hw hLp
  choose g hg heq using fun n => (hK n).2.extend_real
  refine ⟨K, g, ?_, hcover⟩
  intro n
  exact ⟨(hK n).1, hg n, heq n,
    lipschitz_piece_gradient_eq hu hw hLp (hK n).1.measurableSet (hg n) (heq n)⟩

end CircleDomainRigidity

end

end OAI
