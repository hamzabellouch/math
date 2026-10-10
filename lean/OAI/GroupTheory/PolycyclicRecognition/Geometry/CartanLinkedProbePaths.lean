import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSelectedProbePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles

namespace OAI

/-! # Image paths from the actual linked profile bounds -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/- The original sampling center is retained throughout all three paths. -/
theorem exists_linked_probe_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {K : ℝ≥0} (hLip : LipschitzWith K (fun g : G => (π g).toAdd))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (η : ℕ → ℝ)
    (D : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base η)
    (sampleBasis : ℕ → Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hExpD : Continuous F.ExpD) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (y : Y n) (x : G)
        (sample : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)
        (f : G → G) (hf : LipschitzWith Λ f),
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ j z, z ∈ Q →
          ‖F.sampledProbeProfile hExpD (fun g => (π (f g)).toAdd)
              ((hLip.comp hf).continuous) x (Real.log (scale n))
              (sampleBasis n) (br n) sample (D.vertex k n y j) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (1 : G) (basedImage f
            (x * F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.sampledProbeSuffix (sampleBasis n) sample
                (D.vertex k n y (Fin.last (P k).length)) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))),
          PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
          ∀ s, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path s)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, he⟩ := M.exists_selected_probe_paths T F hunimod eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    pivot E V hEc hE hpivot hV hVconv hEV b₀ γ t probe P Λ
  refine ⟨Q, C, hQ, hQV, hC, he.mono ?_⟩
  intro n hn k y x sample f hf A offset ε hgood
  let anchor := F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0)
  have hexp (j : Fin ((P k).length + 1)) :
      anchor * F.inclusionN (F.ExpN (F.N.equiv ((P k).vertex n y j))) =
        F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y j) := by
    have h := congrArg F.inclusionN
      (LinkedProbeChains.exp_eq_start_mul T M F hunimod eW b₀ E γ t scale probe P origin base η D k n y j)
    rw [map_mul] at h
    simp only [anchor, CartanFactorModel.sampledProbeSuffix, map_mul]
    rw [h, mul_assoc]
  have hp := hn k y x anchor f hf A offset ε (fun j z hz => ?_)
  · obtain ⟨path, hm, hh⟩ := hp
    have hend : basedImage f
        (x * F.sampledProbeSuffix (sampleBasis n) sample (D.vertex k n y 0) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * F.sampledProbeSuffix (sampleBasis n) sample
            (D.vertex k n y (Fin.last (P k).length)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) =
      basedImage f (x * anchor * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (x * (anchor * F.inclusionN (probe k n y)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
      have hl := hexp (Fin.last (P k).length)
      rw [(P k).vertex_last] at hl
      rw [← hl]
    exact ⟨path.cast rfl hend, hm.cast rfl hend, hh⟩
  · have hg := hgood j z hz
    rw [CartanFactorModel.sampledProbeProfile_apply] at hg
    simp only [F.compatibleD] at hg
    have hx := hexp j
    simp only [CartanFactorModel.sampledProbeSuffix, map_mul] at hx
    rw [← hx] at hg
    exact hg

end PolycyclicRecognition.CartanWordModel

end

end OAI
