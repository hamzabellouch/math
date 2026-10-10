import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingParameters

namespace OAI

/-! # The three actual chains for the polar flow partition -/

noncomputable section
namespace PolycyclicRecognition

/-- Normalized templates ordered as source, reverse anchor, within-tile. -/
def normalizedPolarTemplates {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (K : ProperCone ℝ (StrongDual ℝ W)) (ε : ℝ) (j : Fin 3) : Set W :=
  (fun z => threePolarRadii ε j • z) '' conePolarTemplate K

end PolycyclicRecognition

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
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

local notation "C" => heightConePreimage T eW K

/-- The same maximal polar ideal basis from the flow tiling supplies all
three actual measurable chain families. Their common ambient basis and
amplitude envelope are constructed from the largest polar radius. -/
theorem exists_polar_tiled_probe_chains
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1)
    (ha₀ : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)) :
    ∃ ambient : M.Bases,
      Nonempty (M.TiledProbeChainData T F hunimod eW C ExpI bN
        (normalizedPolarTemplates K ε) (fun _ => β) ambient
        (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor) := by
  classical
  let E := normalizedPolarTemplates K ε
  let t := fun i => ε * M.polarProbeWidths T hunimod eW K i
  have hrad (j : Fin 3) : 0 ≤ threePolarRadii ε j ∧ threePolarRadii ε j ≤ ε := by
    fin_cases j <;> dsimp [threePolarRadii] <;> constructor <;> linarith
  have hprop (j : Fin 3) := M.polar_probe_template_properties T hunimod eW K (hrad j).1
  have hw (j : Fin 3) : (M.supportIn T hunimod eW).weightSupport (E j) =
      fun i => threePolarRadii ε j * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K (hrad j).1 i
  have hβ' (j : Fin 3) : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) β := by
    rw [hw]
    exact M.maximizing_coneIdealBasis_smul C bI _ β hβ (hrad j).1
  obtain ⟨ambient, ha⟩ := exists_maximizing_wordBasis M.letter M.wordList bN
    (fun w => bracketWordExponent t w)
  have hdom (j : Fin 3) (i) : (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i := by
    rw [hw]
    exact mul_le_mul_of_nonneg_right (hrad j).2 (M.polar_width_nonneg T hunimod eW K i)
  refine ⟨ambient, ?_⟩
  exact M.nonempty_tiledProbeChainData T F hunimod eW C hExp realize haarN dynkinN
    ExpI ι hι hcompat bN bI E (fun j => (hprop j).1)
    (fun j => ⟨0, (hprop j).2.2.1⟩)
    (fun j => (hprop j).2.2.2.1) (fun j => (hprop j).2.2.2.2)
    (fun _ => β) hβ' ambient t hdom ha scale hr R hR φ k hφ
    tiles anchor tile hm hd hu ha₀ ht

end PolycyclicRecognition.CartanWordModel

end
end

end OAI
