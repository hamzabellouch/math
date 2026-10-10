import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeIntrinsicTiles

namespace OAI

/-! # Exact endpoints of the counted sampler after dilation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- Dilation of the stored three samplers gives exactly the first endpoint,
the selected second-sheet anchor, and the second endpoint. -/
theorem TiledProbeChainData.dilated_endpoints
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (k : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (S : ℕ → MulAut F.N.carrier) (n : ℕ) (u : F.N.carrier)
    (y : (closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
        (β 0) (scale n) 1)) :
    u * S n (D.probe n 0 y) = coneProbeFirst (S n) u (ι y.2.val)
      (F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift
        (D.bQ.equivFun.symm y.1.val)))) ∧
    (u * S n (k n)) * S n (D.probe n 1 y) =
      coneProbeSecond (S n) u (ι (anchor n (D.index n y.2))) (k n) ∧
    ((u * S n (k n)) * S n (D.probe n 1 y)) * S n (D.probe n 2 y) =
      coneProbeSecond (S n) u (ι y.2.val) (k n) := by
  have hback (z : I) : ι ((φ n).symm z) = (k n)⁻¹ * ι z * k n :=
    (intrinsic_probe_inverse_flow ι (φ n).toMulEquiv (k n) (hφ n) z).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [D.first]
    rfl
  · rw [D.second, hback]
    simp only [coneProbeSecond, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  · rw [D.second, D.third, hback, hback]
    simp [coneProbeSecond, map_mul, mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
