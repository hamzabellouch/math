import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarSourceFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceDilationUniqueness

namespace OAI

/-! # Linked source frames for an exponential-compatible dilation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Manifold Pointwise Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

variable (D : M.MeasuredCone F (heightConePreimage T eW K))
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  {ε : ℝ} (β : M.ConeIdealBases (heightConePreimage T eW K)) (Rbox : ℝ) (scale : ℕ → ℝ)
  (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
  (P : M.PolarTiledSamplerData (EG := EG) (G := G) (W := W) (I := D.I.carrier) T F hunimod eW K
    (fun v : M.coneWordIdeal (heightConePreimage T eW K) => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN ε β Rbox scale φ)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)

variable (Eall : Set W) (γ : M.Bases) (δ : ℝ) (w : W)
  (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier) (base step : ℕ → F.N.carrier)

omit Eall γ δ w S base step in
/-- The original box hypotheses construct the linked frames for any
continuous dilation satisfying the canonical exponential formula. -/
theorem PolarTiledSamplerData.nonempty_linkedSource_of_exp
    (hε : 0 ≤ ε)
    (hbijN : Function.Bijective F.ExpN)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    {Eall : Set W} (hEall : IsCompact Eall) (hne : Eall.Nonempty)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (w : W) (hBE : (fun z => z + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport Eall i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier)
    (hS : ∀ n v, S n (F.ExpN (F.N.equiv v)) = F.ExpN (F.N.equiv
      (cartanIdealWeightDilation T H (scale n • cartanHeightSection T H (eW.symm w)) v)))
    (hφ : ∀ n z, D.maps.inclusion (φ n z) =
      (S n).symm (step n) * D.maps.inclusion z * ((S n).symm (step n))⁻¹) :
    Nonempty (P.LinkedSource T M F hunimod eW K D bN β Rbox scale φ chartN
      Eall γ δ w S base step) := by
  have hS' : S = fun n => M.sourceDilation T F hbijN chartN hchartN dynkinN
      (scale n • cartanHeightSection T H (eW.symm w)) := by
    funext n
    exact M.sourceDilation_eq_of_exp T F hbijN chartN hchartN dynkinN
      (scale n • cartanHeightSection T H (eW.symm w)) (S n) (hS n)
  subst S
  exact PolarTiledSamplerData.nonempty_linkedSource T M F hunimod eW K D bN β Rbox scale φ P chartN
    hε hbijN hchartN haarN dynkinN hEall hne γ hγ w hBE hw hδ hs hs1
    R hR0 hR base step hbase hstep hφ

end PolycyclicRecognition.CartanWordModel

end

end OAI
