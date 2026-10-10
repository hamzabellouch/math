import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGoodWordPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulSourceWord
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoupledBundleStates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SheetEndpointHeight

namespace OAI

/-! # Actual profile paths for the successful coupled source bundles -/

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

theorem exists_successful_bundle_profile_paths
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
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ᶠ n in atTop, ∀ (Good : Set F.N.carrier) (x : G) (initial : F.N.carrier)
        (k : Fin h → F.N.carrier) (t : Fin (h * m + h * m) → ℝ),
        let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
        let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
          allLetters M.letter s (scale n) (bundleConjugator m k)
        let φ := fun i => MulAut.conj (k i)
        let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
          (bundleParameterChart h m) (scale n) t
        let boundary := sourceBundleBoundary initial φ products
        initial ∈ Good → ‖t‖ ≤ ρ →
        SwitchSuccessful (fun _ => Good) 0 (h * m) initial
          (sampledSwitchParameters sample (h * m) t) →
        ∀ (i : Fin h) (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ q ∈ Good, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile J x (F.inclusionN (q * k i)) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (height (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path
            (x * F.inclusionN (boundary i.val * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.inclusionN (boundary (i.val + 1) * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ m)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ m) ∧
          ‖J (x * F.inclusionN (boundary (i.val + 1) * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
            J (x * F.inclusionN (boundary i.val * k i) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))‖ ≤
            2 * scale n * ε ∧
          ∀ u, ∃ w ∈ E,
            ‖J (path u) - J (x * F.inclusionN (boundary i.val * k i) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - height pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  classical
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpivotQ, hp⟩ := M.exists_good_conjugated_word_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs (B := 2 * ρ) (by positivity)
  refine ⟨Q, C, hQ, hQV, hC, hpivotQ, ?_⟩
  filter_upwards [hp, hpivotQ] with n hn hnQ
  intro Good x initial k t hi ht hsuccess i J K hJ A offset ε hgood
  let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
  let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
    allLetters M.letter s (scale n) (bundleConjugator m k)
  let φ := fun i => MulAut.conj (k i)
  let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
    (bundleParameterChart h m) (scale n) t
  let boundary := sourceBundleBoundary initial φ products
  let diff := fun j : Fin m => t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
    t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))
  let coeff := fun j => diff j * Real.exp (scale n * s (letters j))
  let word := fun j => k i * F.ExpN (F.N.equiv (coeff j • M.letter (letters j))) * (k i)⁻¹
  have hsample (i : Fin h) (j : Fin m) (u : ℝ) :
      sample (finProdFinEquiv (i, j)).val u = φ i
        (F.ExpN (F.N.equiv (u • (Real.exp (scale n * s (letters j)) • M.letter (letters j))))) :=
    coupledRootIntervalSample_bundle (F.ExpN ∘ F.N.equiv) letters M.letter s (scale n) k i j u
  have hsub (j : ℕ) (u v : ℝ) : sample j u * (sample j v)⁻¹ = sample j (u - v) := by
    apply coupledRootIntervalSample_sub
    · intro w
      simp only [Function.comp_apply, map_neg, F.isExpN.map_neg]
    · intro w u v
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv w) u v
  have hg : WordSheetsGood Good (boundary i.val) (List.ofFn word) := by
    have hg := successful_sourceBundle_word_good F.N.equiv F.ExpN M.letter s letters
      (scale n) φ sample hsub hsample Good initial hi t hsuccess i
    simpa only [word, coeff, diff, smul_smul, φ, MulAut.conj_apply] using hg
  have hcoeff (j : Fin m) : |coeff j| ≤ 2 * ρ * Real.exp (scale n * s (letters j)) := by
    have h₁ := (norm_le_pi_norm t (Fin.castAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    have h₂ := (norm_le_pi_norm t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))).trans ht
    rw [Real.norm_eq_abs] at h₁ h₂
    have hd : |diff j| ≤ 2 * ρ := by
      exact (abs_sub _ _).trans (by linarith)
    dsimp only [coeff]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
  obtain ⟨path, hmetric, hrange⟩ := hn m letters coeff hcoeff Good x (k i) (boundary i.val)
    hg J K hJ A offset ε hgood
  have hword : sampledBlockWord sample t i = List.ofFn word := by
    simp only [sampledBlockWord, hsample, word, coeff, diff, smul_smul, φ, MulAut.conj_apply]
  have hblock := sampledBlockWord_source_product F.N.equiv F.ExpN M.letter s letters
    (scale n) φ sample hsample t i
  have hnext : boundary (i.val + 1) = boundary i.val * (List.ofFn word).prod := by
    dsimp only [boundary, sourceBundleBoundary, products]
    rw [wordPrefix_succ, dite_eq_left i.isLt, ← hblock, hword]
    simp only [mul_assoc]
  have hend : x * F.inclusionN (boundary (i.val + 1) * k i) *
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) =
        x * F.inclusionN (boundary i.val * (List.ofFn word).prod * k i) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by rw [hnext]
  have hfinish : boundary (i.val + 1) ∈ Good := by
    rw [hnext]
    simpa only [List.take_of_length_le (by simp : (List.ofFn word).length ≤ m)] using
      hg.take_prod_mem m
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  let br := exponentialRescaleBasis b cost (Real.log (scale n))
  let z₀ := br.equivFun (scale n • pivot)
  have hz₀ : z₀ ∈ Q := hnQ
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hkill (u w : H) : height ⁅u, w⁆ = 0 := by
    change eW (heightProjection T.character ⁅(u : GroupLieAlgebra (𝓘(ℝ, EG)) G), w⁆) = 0
    rw [T.height_lie, map_zero]
  have hz₀E : height (b.equivFun.symm z₀) ∈ E := by
    rw [word_length_chart_pivot_height X (boundedBracketWords d) βD height hkill (hscale0 n)]
    exact hpivot
  have hφ₀ : Exp ((br.equivFun.symm z₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) =
      Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    simp only [z₀, LinearEquiv.symm_apply_apply, SetLike.val_smul]
  have hendpoint := common_profile_endpoint_height J x
    (F.inclusionN (boundary i.val * k i)) (F.inclusionN (boundary (i.val + 1) * k i))
    (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (Real.log (scale n))
    (fun z => Exp ((br.equivFun.symm z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z₀
    _ hφ₀ (hgood _ hg.start z₀ hz₀ hz₀E) (hgood _ hfinish z₀ hz₀ hz₀E)
  rw [Real.exp_log (hscale0 n)] at hendpoint
  refine ⟨path.cast rfl hend, hmetric, hendpoint, ?_⟩
  intro u
  exact hrange u

end PolycyclicRecognition.CartanWordModel

end

end OAI
