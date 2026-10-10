import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCommonBundlePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ReachableTuplePaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths

namespace OAI

/-! # Actual centered target geometry of successful coupled bundles -/

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

theorem exists_target_bundle_geometry
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
    ∃ Q : Set (Fin (finrank ℝ H) → ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧
      ∀ {Λ Kπ : ℝ≥0} (p : ℕ → NormalizedPair G Λ),
      LipschitzWith Kπ (fun g => (π g).toAdd) →
      ∀ (Good : ℕ → Set F.N.carrier) (x : ℕ → G)
        (k : ℕ → Fin h → F.N.carrier) (A : Fin h → W →ₗ[ℝ] W)
        (offset : Fin h → W) (ε δ : ℕ → ℝ)
        (initial : ℕ → F.N.carrier) (S : ℕ → Set (Fin h → F.N.carrier)),
      (∀ n, initial n ∈ Good n) →
      (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin h,
        dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (F.inclusionN (k n i) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
            δ n * scale n) →
      (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
        ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
            (F.inclusionN (q * k n i)) (Real.log (scale n))
            (fun z => Exp ((br n).equivFun.symm z)) z -
          (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
      (∀ᶠ n in atTop, ∀ v ∈ S n,
        ∃ t : Fin (h * m + h * m) → ℝ, ‖t‖ ≤ ρ ∧
          SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
            (sampledSwitchParameters
              (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
                (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
                M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
          ∀ i : Fin h, v i = sourceBundleBoundary (initial n)
            (fun i => MulAut.conj (k n i))
            (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
              (bundleParameterChart h m) (scale n) t) (i.val + 1)) →
      (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          dist (γ t) (γ u) ≤ dist 1 g * |t - u|) →
      ∃ (D : ℝ) (η : ℕ → ℝ), 0 ≤ D ∧ (∀ n, 0 ≤ η n) ∧
        Tendsto η atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ∀ y ∈ (fun v : Fin h → F.N.carrier => fun i =>
            basedImage (p n).val.1
              (x n * F.inclusionN (initial n) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.inclusionN (v i) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) '' S n,
          ∃ paths : ∀ i : Fin h, Path (1 : G)
              ((basedTuplePosition y i.val)⁻¹ * basedTuplePosition y (i.val + 1)),
            (∀ i, PathMetricBound (paths i) (D * scale n)
              (D * (1 + Real.log (2 + scale n)))) ∧
            (∀ i u, ∃ w ∈ (fun z => A i (z - height pivot)) '' E,
              ‖(π (paths i u)).toAdd - scale n • w‖ ≤
                2 * scale n * η n + D * (1 + Real.log (2 + scale n))) ∧
            ∀ i : Fin h,
              ‖(π ((basedTuplePosition y i.val)⁻¹ * basedTuplePosition y (i.val + 1))).toAdd‖ ≤
                η n * scale n := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, _, hp⟩ := M.exists_common_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  refine ⟨Q, hQ, hQV, ?_⟩
  intro Λ Kπ p hLip Good x k A offset ε δ initial S hi hε0 hε hδ0 hδ hb hg hr hpath
  obtain ⟨D, η, hD, hη0, hη, hpaths⟩ := hp (fun n g => (π ((p n).val.1 g)).toAdd)
    (Kπ * Λ) (fun n => hLip.comp (p n).property.1.1) Good x k A offset ε δ
    hε0 hε hδ0 hδ hb hg hpath
  let D' := max D (Λ * D)
  have hD' : 0 ≤ D' := hD.trans (le_max_left _ _)
  refine ⟨D', η, hD', hη0, hη, ?_⟩
  filter_upwards [hpaths, hr] with n hn hr
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
    linarith
  have ht := reachable_image_tuple_paths F.inclusionN (p n).val.1 (p n).property.1.1 π
    (x n) (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) (initial n) (S n)
    (fun t : Fin (h * m + h * m) → ℝ => ‖t‖ ≤ ρ ∧
      SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
        (sampledSwitchParameters
          (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
            (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
            M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t))
    (fun t => sourceBundleBoundary (initial n) (fun i => MulAut.conj (k n i))
      (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
        (bundleParameterChart h m) (scale n) t))
    (fun _ _ => sourceBundleBoundary_zero _ _ _) ?_
    (fun i => (fun z => A i (z - eW (heightProjection T.character pivot))) '' E)
    (scale n) (D * scale n) (D * (1 + Real.log (2 + scale n)))
    (2 * scale n * η n + D * (1 + Real.log (2 + scale n))) (η n * scale n)
    (fun t ht i => hn (initial n) t (hi n) ht.1 ht.2 i)
  · intro y hy
    obtain ⟨paths, hm, hh, he⟩ := ht y hy
    refine ⟨paths, ?_, ?_, he⟩
    · intro i
      apply (hm i).mono
      · calc Λ * (D * scale n) = (Λ * D) * scale n := by ring
             _ ≤ D' * scale n := mul_le_mul_of_nonneg_right (le_max_right _ _) (hscale0 n).le
      · calc Λ * (D * (1 + Real.log (2 + scale n))) =
                (Λ * D) * (1 + Real.log (2 + scale n)) := by ring
             _ ≤ D' * (1 + Real.log (2 + scale n)) :=
               mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
    · intro i u
      obtain ⟨w, hw, he⟩ := hh i u
      refine ⟨w, hw, he.trans ?_⟩
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  · intro v hv
    obtain ⟨t, ht, hs, he⟩ := hr v hv
    exact ⟨t, ⟨ht, hs⟩, fun i => (he i).symm⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
