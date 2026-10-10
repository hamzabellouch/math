import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSelectedProfilePaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GoodFiniteWordVertices

namespace OAI

/-! # Cartan paths along the good vertices of a conjugated word

The profile on the second sheet is evaluated at `n * k`. The recurrence
word moves `n` by conjugation, so multiplying its vertices by `k` gives
the ordinary root-generator chain required by the Cartan path theorem.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem exists_good_conjugated_word_paths
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
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {B : ℝ} (hB : 0 ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ᶠ n in atTop, ∀ (m : ℕ) (mode : Fin m → Fin M.letterCount) (coeff : Fin m → ℝ),
        (∀ j, |coeff j| ≤ B * Real.exp (scale n * s (mode j))) →
        ∀ (Good : Set F.N.carrier) (x : G) (k n₀ : F.N.carrier),
        let u := fun j => F.ExpN (F.N.equiv (coeff j • M.letter (mode j)))
        let word := fun j => k * u j * k⁻¹
        WordSheetsGood Good n₀ (List.ofFn word) →
        ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ q ∈ Good, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile J x (F.inclusionN (q * k)) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (height (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path
            (x * F.inclusionN (n₀ * k) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.inclusionN (n₀ * (List.ofFn word).prod * k) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ m)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ m) ∧
          ∀ t, ∃ w ∈ E,
            ‖J (path t) - J (x * F.inclusionN (n₀ * k) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - height pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  classical
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpivotQ, hp⟩ := M.exists_selected_profile_paths T F eW hExp realize
    haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0 pivot v E V hE hpivot
    hV hVconv hEV hv s hs hB
  refine ⟨Q, C, hQ, hQV, hC, hpivotQ, ?_⟩
  filter_upwards [hp] with n hn
  intro m mode coeff hc Good x k n₀ hg J K hJ A offset ε hgood
  let u := fun j => F.ExpN (F.N.equiv (coeff j • M.letter (mode j)))
  let word := fun j => k * u j * k⁻¹
  let vertex := fun j : Fin (m + 1) => F.inclusionN (finiteWordVertex n₀ word j * k)
  have hstep (j : Fin m) : vertex j.succ = vertex j.castSucc *
      Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    dsimp only [vertex]
    rw [finiteWordVertex_step]
    calc
      F.inclusionN ((finiteWordVertex n₀ word j.castSucc * word j) * k) =
          F.inclusionN (finiteWordVertex n₀ word j.castSucc * k) * F.inclusionN (u j) := by
        dsimp only [word]
        simp only [map_mul, map_inv]
        group
      _ = _ := by rw [show F.inclusionN (u j) =
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) from
            F.compatibleN (coeff j • M.letter (mode j))]
  obtain ⟨path, hmetric, hrange⟩ := hn m x vertex mode coeff hstep hc J K hJ A offset ε
    (fun j z hz hzE => hgood _ (hg.finite_vertices j) z hz hzE)
  have hstart : x * F.inclusionN (n₀ * k) *
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
        x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    simp only [vertex, finiteWordVertex_zero]
  have hend : x * F.inclusionN (n₀ * (List.ofFn word).prod * k) *
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
        x * vertex (Fin.last m) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    simp only [vertex, finiteWordVertex_last]
  refine ⟨path.cast hstart hend, hmetric, ?_⟩
  intro t
  obtain ⟨w, hw, he⟩ := hrange t
  refine ⟨w, hw, ?_⟩
  change ‖J (path t) - J (x * F.inclusionN (n₀ * k) *
    Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
    scale n • A (w - _)‖ ≤ _
  simpa only [vertex, finiteWordVertex_zero] using he

end PolycyclicRecognition.CartanWordModel

end

end OAI
