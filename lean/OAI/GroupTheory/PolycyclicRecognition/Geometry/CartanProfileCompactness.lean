import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfilePointwiseBounds

namespace OAI

/-! # Compact containment of the actual Cartan profiles -/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology NNReal

variable {EG G I W A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- Uniformly bounded normalized suffix lengths give a compact set of the
actual profiles. All chart metric and continuity hypotheses are discharged
from the recorded published Lie inputs. -/
theorem exists_compact_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hnonneg : ∀ i, 0 ≤ scale i)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ i u, LipschitzWith K (J i u))
    (x suffix : ℕ → A → G) (B : ℝ)
    (hsuffix : ∀ i u, dist 1 (suffix i u) / Real.exp (scale i) ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let φ := fun i z => F.inclusionD (F.ExpD (F.D.equiv
      ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z)))
    ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧ ∀ i u,
      ∃ f ∈ S, ∀ z, f z = rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i) (φ i) z := by
  dsimp only
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let b := WordBasisSelections.basis X (boundedBracketWords k) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let φ := fun i z => F.inclusionD (F.ExpD (F.D.equiv
    ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z)))
  have hφ (i : ℕ) : Continuous (φ i) :=
    F.closedD.continuous.comp (continuous_model_exp_coordinates haarD F.ExpD F.isExpD
      F.D.equiv (F.D.tangent_nilpotent inferInstance) (exponentialRescaleBasis b cost (scale i)))
  have hz (i : ℕ) : φ i 0 = 1 := by simp [φ, F.isExpD.map_zero]
  have hequi := equicontinuous_cartan_d_profiles T F hExpG realize haarD dynkinD X hk
    hletters b₀ β hβ scale hscale J hJ x suffix
  obtain ⟨S, hS, hmem⟩ := exists_compact_containing_rescaled_profiles J hJ x suffix scale φ hφ hz
    hequi ((K : ℝ) * B) (fun i u =>
      (rescaledMapProfile_zero_norm_le (hJ i u) (x i u) (suffix i u) (scale i) (φ i) (hz i)).trans
        (mul_le_mul_of_nonneg_left (hsuffix i u) K.coe_nonneg)) (by
      intro z
      obtain ⟨D, _, hD⟩ := exists_cartan_d_chart_metric_bound T F hExpG realize haarD dynkinD
        X hk hletters b₀ ‖z‖
      refine ⟨D, ?_⟩
      intro i
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      have hv : ‖(exponentialRescaleBasis b cost (scale i)).equivFun
          ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z)‖ ≤ ‖z‖ := by
        rw [LinearEquiv.apply_symm_apply]
      exact hD β hβ (scale i) (hnonneg i)
        ((exponentialRescaleBasis b cost (scale i)).equivFun.symm z) hv)
  refine ⟨S, hS, ?_⟩
  intro i u
  exact ⟨_, hmem i u, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
