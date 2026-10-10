import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSuccessfulBundlePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BridgedProfileBounds

namespace OAI

/-! # Common-pivot paths for the actual successful source bundles

The chart is selected before the good sets. Both endpoint bridges use the
same root displacement, and their error tends to zero with that displacement.
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

theorem exists_common_bundle_profile_paths
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
      ∀ (J : ℕ → G → W) (K : ℝ≥0), (∀ n, LipschitzWith K (J n)) →
      ∀ (Good : ℕ → Set F.N.carrier) (x : ℕ → G)
        (k : ℕ → Fin h → F.N.carrier) (A : Fin h → W →ₗ[ℝ] W)
        (offset : Fin h → W) (ε δ : ℕ → ℝ),
      (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, 0 ≤ δ n) → Tendsto δ atTop (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin h,
        dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
          (F.inclusionN (k n i) *
            Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ δ n * scale n) →
      (∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
        ‖rescaledMapProfile (J n) (x n) (F.inclusionN (q * k n i))
            (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
          (A i (height (b.equivFun.symm z)) + offset i)‖ ≤ ε n) →
      (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          dist (γ t) (γ u) ≤ dist 1 g * |t - u|) →
      ∃ (D : ℝ) (η : ℕ → ℝ), 0 ≤ D ∧
        (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, ∀ (initial : F.N.carrier)
          (t : Fin (h * m + h * m) → ℝ),
          let allLetters := fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2
          let sample := coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
            allLetters M.letter s (scale n) (bundleConjugator m (k n))
          let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart h m) (scale n) t
          let boundary := sourceBundleBoundary initial (fun i => MulAut.conj (k n i)) products
          initial ∈ Good n → ‖t‖ ≤ ρ →
          SwitchSuccessful (fun _ => Good n) 0 (h * m) initial
            (sampledSwitchParameters sample (h * m) t) →
          ∀ i : Fin h, ∃ path : Path
              (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
              (x n * F.inclusionN (boundary (i.val + 1)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
            PathMetricBound path (D * scale n) (D * (1 + Real.log (2 + scale n))) ∧
            (∀ u, ∃ w ∈ (fun z => A i (z - height pivot)) '' E,
              ‖J n (path u) - J n (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
                scale n • w‖ ≤
                  2 * scale n * η n + D * (1 + Real.log (2 + scale n))) ∧
            ‖J n (x n * F.inclusionN (boundary (i.val + 1)) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              J n (x n * F.inclusionN (boundary i.val) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))‖ ≤ η n * scale n := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, _, hp⟩ := M.exists_successful_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  refine ⟨Q, C, hQ, hQV, hC, ?_⟩
  intro J K hJ Good x k A offset ε δ hε0 hε hδ0 hδ hbridge hgood hpath
  let C' : ℝ := max (C * 2 ^ m) (K * C)
  have hC' : 0 ≤ C' := (mul_nonneg hC (by positivity)).trans (le_max_left _ _)
  let η := fun n => 2 * ε n + 2 * K * δ n
  refine ⟨4 * (C' + 1), η, by positivity, fun n =>
    add_nonneg (mul_nonneg (by norm_num) (hε0 n))
      (mul_nonneg (by positivity) (hδ0 n)), ?_, ?_⟩
  · have he : Tendsto (fun n => 2 * ε n) atTop (𝓝 (2 * 0)) := tendsto_const_nhds.mul hε
    have hd : Tendsto (fun n => 2 * (K : ℝ) * δ n) atTop (𝓝 (2 * K * 0)) :=
      tendsto_const_nhds.mul hδ
    simpa only [mul_zero, add_zero] using he.add hd
  have hscale1 := hscale.eventually (eventually_ge_atTop 1)
  have hδ1 : ∀ᶠ n in atTop, δ n ≤ 1 := hδ.eventually (eventually_le_nhds (by norm_num))
  filter_upwards [hp, hbridge, hgood, hscale1, hδ1] with n hn hb hg hr hd
  intro initial t hi ht hsuccess i
  obtain ⟨path, hm, hend, himage⟩ := hn (Good n) (x n) initial (k n) t hi ht hsuccess
    i (J n) K (hJ n) (A i) (offset i) (ε n) (hg i)
  let pivotG := Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let products := sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
    (bundleParameterChart h m) (scale n) t
  let boundary := sourceBundleBoundary initial (fun i => MulAut.conj (k n i)) products
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith)
    linarith
  have hm' : PathMetricBound path (C' * scale n) (C' * (1 + Real.log (2 + scale n))) := by
    apply hm.mono
    · calc (C * scale n) * 2 ^ m = (C * 2 ^ m) * scale n := by ring
           _ ≤ C' * scale n := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    · calc (C * (1 + Real.log (2 + scale n))) * 2 ^ m =
              (C * 2 ^ m) * (1 + Real.log (2 + scale n)) := by ring
           _ ≤ C' * (1 + Real.log (2 + scale n)) :=
             mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
  have hdist (q : F.N.carrier) :
      dist (x n * F.inclusionN q * pivotG)
        (x n * F.inclusionN (q * k n i) * pivotG) ≤ δ n * scale n := by
    simpa only [map_mul, mul_assoc, dist_mul_left] using hb i
  have himage' : ∀ u, ∃ w ∈ (fun z => A i (z -
      eW (heightProjection T.character pivot))) '' E,
      ‖J n (path u) - J n (x n * F.inclusionN (boundary i.val * k n i) * pivotG) -
        scale n • w‖ ≤ 2 * scale n * ε n + C' * (1 + Real.log (2 + scale n)) := by
    intro u
    obtain ⟨w, hw, he⟩ := himage u
    refine ⟨A i (w - eW (heightProjection T.character pivot)), ⟨w, hw, rfl⟩, he.trans ?_⟩
    have hlog0 : 0 ≤ Real.log (2 + scale n) := Real.log_nonneg (by linarith)
    calc 2 * scale n * ε n + K * (C * Real.log (2 + scale n)) =
          2 * scale n * ε n + (K * C) * Real.log (2 + scale n) := by ring
         _ ≤ 2 * scale n * ε n + C' * (1 + Real.log (2 + scale n)) := by
           gcongr
           · exact le_max_right _ _
           · linarith
  have hzero : (0 : W) ∈ (fun z => A i (z - eW (heightProjection T.character pivot))) '' E :=
    ⟨eW (heightProjection T.character pivot), hpivot, by simp only [sub_self, map_zero]⟩
  exact exists_bridged_profile_bounds (exists_short_path_of_minimizing_paths hpath) path
    hC' hr (hδ0 n) hd (hε0 n) hm' (hdist (boundary i.val))
    (by rw [dist_comm]; exact hdist (boundary (i.val + 1)))
    (J n) (hJ n) _ hzero himage' hend

end PolycyclicRecognition.CartanWordModel

end

end OAI
