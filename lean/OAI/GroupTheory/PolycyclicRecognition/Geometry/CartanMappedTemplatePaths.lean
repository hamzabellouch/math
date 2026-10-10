import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateProfilePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths

namespace OAI

/-! # Actual image paths from the selected affine profiles -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Good profiles on all selected prefixes give paths in the actual target
space, centered at the image of the starting point. Their height region is
the affine image of the translated template, with the offset cancelled. -/
theorem exists_mapped_template_profile_paths
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
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (pivot : H) (E V : Set W) (hEc : IsCompact E) (hE : Convex ℝ E)
    (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    {B : ℝ} (hB : 0 ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ) (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) →
        ∀ (f : G → G) (Λ : ℝ≥0), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x (vertex i)
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        let start := x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        let finish := x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        ∃ path : Path (1 : G) (basedImage f start finish),
          PathMetricBound path ((Λ * (C * scale n)) * 2 ^ N)
            ((Λ * (C * (1 + Real.log (2 + scale n)))) * 2 ^ N) ∧
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + (K * Λ) * (C * Real.log (2 + scale n)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpaths⟩ := M.exists_compact_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB
  refine ⟨Q, C, hQ, hQV, hC, ?_⟩
  filter_upwards [hpaths] with n hn
  intro N x vertex mode coeff hstep hamp f Λ hf A offset ε hgood
  obtain ⟨path, hmetric, hheight⟩ := hn N x vertex mode coeff hstep hamp
    (fun g => (π (f g)).toAdd) (K * Λ) (hLip.comp hf) A offset ε hgood
  obtain ⟨mapped, hmapped, hbound⟩ := basedImage_map_path f hf path hmetric
  refine ⟨mapped, ?_, ?_⟩
  · convert hbound using 1 <;> ring
  · intro t
    obtain ⟨w, hw, hh⟩ := hheight t
    refine ⟨A (w - _), ⟨w, hw, rfl⟩, ?_⟩
    rw [hmapped, basedImage_height]
    exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
