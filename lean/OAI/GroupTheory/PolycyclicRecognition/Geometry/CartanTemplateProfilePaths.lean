import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSelectedProfilePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSupports

namespace OAI

/-! # Profile-controlled paths for a compact template -/

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

/-- The support directions and their exponents are obtained from the actual
compact template; no direction or path selection is assumed. -/
theorem exists_compact_template_profile_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (pivot : H) (E V : Set W) (hEc : IsCompact E) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
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
        (∀ j, |coeff j| ≤ B * Real.exp (scale n * (M.supportIn T hunimod eW).weightSupport E (mode j))) →
        ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile J x (vertex i) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ N)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ N) ∧
          ∀ t, ∃ w ∈ E,
            ‖J (path t) - J (x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - h pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  obtain ⟨u, hu, hs⟩ := M.exists_cartan_template_supports T hunimod eW E hEc ⟨_, hpivot⟩
  let v := fun i => u i - pivot
  have hv i : eW (heightProjection T.character (pivot + v i : H)) ∈ E := by
    have he : pivot + v i = u i := by dsimp [v]; abel
    simpa only [he] using hu i
  have hweight i : cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) =
      (M.supportIn T hunimod eW).weightSupport E i := by
    rw [show pivot + v i = u i by dsimp [v]; abel, eW.symm_apply_apply,
      cartanHeightWeight_projection, ← hs]
    rfl
  obtain ⟨Q, C, hQ, hQV, hC, _, hp⟩ := M.exists_selected_profile_paths T F eW hExp realize haarD dynkinD π hπ
    X hDnil bD₀ βD hβD scale hscale hscale0 pivot v E V hE hpivot hV hVconv hEV hv
    ((M.supportIn T hunimod eW).weightSupport E) hweight hB
  refine ⟨Q, C, hQ, hQV, hC, ?_⟩
  filter_upwards [hp] with n hn
  intro N x vertex mode coeff hstep hamp J K hJ A offset ε hgood
  exact hn N x vertex mode coeff hstep hamp J K hJ A offset ε
    (fun i z hz _ => hgood i z hz)

end PolycyclicRecognition.CartanWordModel

end

end OAI
