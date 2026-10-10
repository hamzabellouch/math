import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceCell

namespace OAI

/-! # Actual chains on the quotient/kernel source cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))

local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale) (φ := φ)
    (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q)
    (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale) (φ := φ)
    (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q)
    (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n

variable [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup Q.carrier]
  [SecondCountableTopology Q.carrier]

/-- Pull the stored chains back along the actual source coordinates. No
selection of new generator words is needed on the probability cell. -/
def TiledProbeChainData.sourceChains (k : Fin 3) :
    M.BoxProbeChains T F hunimod eW bN (E k) ambient t scale
      (fun n (y : Y n) => D.probe n k (ψ n y)) :=
  BoxProbeChains.reparametrize T M F hunimod eW bN (E k) ambient t scale
    (fun n => D.probe n k) (Classical.choice (D.chains k)) ψ
    (fun n => (ψ n).continuous.measurable)

end PolycyclicRecognition.CartanWordModel

end

end OAI
