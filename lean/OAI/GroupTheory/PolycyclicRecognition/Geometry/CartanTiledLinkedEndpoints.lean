import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeProbeIntrinsicTiles
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeEndpoints

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

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)] [FiniteDimensional ℝ W]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The logarithmic prefixes selected by concentration have exactly the
three group endpoints used by the source count and the two image paths. -/
theorem TiledProbeChainData.linked_endpoints
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (k u : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (S : ℕ → MulAut F.N.carrier)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (ψ : ∀ n, Y n →
      (closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
        (β 0) (scale n) 1))
    (E' : Fin 3 → Set W) (γ : M.Bases) (t' : Fin M.letterCount → ℝ)
    (P : ∀ j, M.BoxProbeChains T F hunimod eW bN (E' j) γ t' scale
      (fun n y => S n (D.probe n j (ψ n y))))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ)
    (L : M.LinkedProbeChains T F hunimod eW bN E' γ t' scale
      (fun j n y => S n (D.probe n j (ψ n y))) P origin base ε)
    (horigin : ∀ n y, F.ExpN (F.N.equiv (origin n y)) = u n)
    (hbase : ∀ n y, F.ExpN (F.N.equiv (base n y)) = u n * S n (k n))
    (n : ℕ) (y : Y n) :
    F.ExpN (F.N.equiv (L.vertex 0 n y (Fin.last (P 0).length))) =
      coneProbeFirst (S n) (u n) (ι (ψ n y).2.val)
        (F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift
          (D.bQ.equivFun.symm (ψ n y).1.val)))) ∧
    F.ExpN (F.N.equiv (L.vertex 1 n y (Fin.last (P 1).length))) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n (ψ n y).2))) (k n) ∧
    F.ExpN (F.N.equiv (L.vertex 2 n y (Fin.last (P 2).length))) =
      coneProbeSecond (S n) (u n) (ι (ψ n y).2.val) (k n) := by
  obtain ⟨h₀, h₁, h₂⟩ := LinkedProbeChains.endpoint T M F hunimod eW bN E' γ t'
    scale (fun j n y => S n (D.probe n j (ψ n y))) P origin base ε L n y
  obtain ⟨e₀, e₁, e₂⟩ := TiledProbeChainData.dilated_endpoints T M F hunimod eW C
    ExpI bN E β ambient t scale φ ι tiles anchor D k hφ S n (u n) (ψ n y)
  exact ⟨h₀.trans ((congrArg (fun z => z * S n (D.probe n 0 (ψ n y)))
      (horigin n y)).trans e₀),
    h₁.trans ((congrArg (fun z => z * S n (D.probe n 1 (ψ n y)))
      (hbase n y)).trans e₁),
    h₂.trans ((congrArg (fun z => (z * S n (D.probe n 1 (ψ n y))) *
      S n (D.probe n 2 (ψ n y))) (hbase n y)).trans e₂)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
