import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCommonBundlePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceProfile
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceBundleTerminalPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CenteredSourceTerminals
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoupledBundleStates

namespace OAI

/-! # Source terminal paths from the actual successful coupled states

The source identity profile removes every source good-profile hypothesis.
Only successful recurrence parameters and the proved pivot bridge rate remain.
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

theorem exists_source_bundle_terminal_bounds
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
    {m h : ℕ} (letters : Fin m → Fin M.letterCount) (ρ : ℝ) (hρ : 0 ≤ ρ)

    (hh : 0 < h) (hbijN : Function.Bijective F.ExpN)
    {Kπ : ℝ≥0} (hLip : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (Good : ℕ → Set F.N.carrier) (x : ℕ → G) (k : ℕ → Fin h → F.N.carrier)
    (initial : ℕ → F.N.carrier) (hinitial : ∀ n, initial n ∈ Good n)
    (S : ℕ → Set (Fin h → F.N.carrier))
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (hbridge : ∀ᶠ n in atTop, ∀ i : Fin h,
      dist (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (k n i) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤
          δ n * scale n)
    (hreach : ∀ᶠ n in atTop, ∀ v ∈ S n,
      ∃ t : Fin (h * m + h * m) → ℝ, ‖t‖ ≤ ρ ∧
        SwitchSuccessful (fun _ => Good n) 0 (h * m) (initial n)
          (sampledSwitchParameters
            (coupledRootIntervalSample (F.ExpN ∘ F.N.equiv)
              (fun j : Fin (h * m) => letters (finProdFinEquiv.symm j).2)
              M.letter s (scale n) (bundleConjugator m (k n))) (h * m) t) ∧
        ∀ i : Fin h, v i = sourceBundleBoundary (initial n)
          (fun i => MulAut.conj (k n i))
          (sourceBundleProduct F.N.equiv F.ExpN M.letter s letters
            (bundleParameterChart h m) (scale n) t) (i.val + 1)) :
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    let E₀ := (fun w => w - height pivot) '' E
    let pivotG := fun n => Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let origin := fun n => x n * F.inclusionN (initial n) * pivotG n
    let last : Fin h := ⟨h - 1, by omega⟩
    let terminals := fun n => relativeTupleTerminals F.inclusionN
      (origin n) (x n) (pivotG n) last (S n)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ terminals n,
      ∃ path : Path (1 : G) z,
        PathMetricBound path (C * scale n) (C * (1 + Real.log (2 + scale n))) ∧
        ∀ u, ∃ w ∈ E₀, ‖(π (path u)).toAdd - scale n • w‖ ≤
          ε * scale n + C * (1 + Real.log (2 + scale n)) := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  dsimp only
  obtain ⟨Q, C, _, _, _, hc⟩ := M.exists_common_bundle_profile_paths
    T F eW hExp realize haarD dynkinD π hπ X hDnil bD₀ βD hβD scale hscale hscale0
    pivot v E V hE hpivot hV hVconv hEV hv s hs letters ρ hρ
  have hgood : ∀ᶠ n in atTop, ∀ i (q : F.N.carrier), q ∈ Good n → ∀ z ∈ Q,
      (eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap))
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z) ∈ E →
      ‖rescaledMapProfile (fun g => (π g).toAdd) (x n) (F.inclusionN (q * k n i))
          (Real.log (scale n))
          (fun z => Exp (((exponentialRescaleBasis
            (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log (scale n))).equivFun.symm z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) z -
        ((LinearMap.id : W →ₗ[ℝ] W)
          ((eW.toLinearMap.comp ((heightProjection T.character).comp H.incl.toLinearMap))
            ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z)) + 0)‖ ≤ 0 := by
    filter_upwards [] with n i q _ z _ _
    rw [F.source_height_profile_eq T eW π hπ hbijN X (boundedBracketWords d) βD
      (hscale0 n) (x n) (q * k n i) z]
    simp only [LinearMap.id_coe, id_eq, add_zero, sub_self, norm_zero, le_refl]
  obtain ⟨D, η, hD, hη0, hη, hp⟩ := hc (fun _ g => (π g).toAdd) Kπ (fun _ => hLip)
    Good x k (fun _ => LinearMap.id) (fun _ => 0) (fun _ => 0) δ
    (fun _ => le_rfl) tendsto_const_nhds hδ0 hδ hbridge hgood hpath
  let D' := D * 2 ^ h
  have hD' : 0 ≤ D' := mul_nonneg hD (by positivity)
  have hDD : D ≤ D' := le_mul_of_one_le_right hD (by exact_mod_cast Nat.one_le_two_pow)
  refine ⟨D', hD', ?_⟩
  intro ε hε
  have hηsmall : ∀ᶠ n in atTop, 2 * η n ≤ ε :=
    (tendsto_const_nhds.mul hη).eventually (eventually_le_nhds (by simpa using hε))
  filter_upwards [hp, hreach, hηsmall] with n hn hr he
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨t, ht, hsuccess, heq⟩ := hr w hw
  have paths := hn (initial n) t (hinitial n) ht hsuccess
  choose path hmetric hheight _ using paths
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  have hE₀ : (0 : W) ∈ (fun w => w - height pivot) '' E :=
    ⟨height pivot, hpivot, sub_self _⟩
  have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
    have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
    linarith
  obtain ⟨γ, hγ, hγheight⟩ := exists_source_bundle_terminal_path F.inclusionN π
    (F.inclusionN_height_eq_one T eW π hπ hbijN) (initial n)
    (fun i => MulAut.conj (k n i)) _ (x n)
    (Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) _ hE₀
    (scale n) (D * scale n) (D * (1 + Real.log (2 + scale n)))
    (2 * scale n * η n + D * (1 + Real.log (2 + scale n)))
    (mul_nonneg hD (hscale0 n).le) (mul_nonneg hD hlog)
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hscale0 n).le) (hη0 n))
      (mul_nonneg hD hlog)) path hmetric hheight
  have hlast : (⟨h - 1, by omega⟩ : Fin h).val + 1 = h := by dsimp; omega
  have hterminal := heq ⟨h - 1, by omega⟩
  rw [hlast] at hterminal
  refine ⟨γ.cast rfl ?_, ?_, ?_⟩
  · dsimp only
    rw [hterminal]
  · change PathMetricBound γ (D' * scale n) (D' * (1 + Real.log (2 + scale n)))
    simpa only [D', mul_right_comm D (scale n) (2 ^ h),
      mul_right_comm D (1 + Real.log (2 + scale n)) (2 ^ h)] using hγ
  · intro u
    obtain ⟨w, hw, hh⟩ := hγheight u
    refine ⟨w, hw, hh.trans ?_⟩
    calc 2 * scale n * η n + D * (1 + Real.log (2 + scale n)) =
          (2 * η n) * scale n + D * (1 + Real.log (2 + scale n)) := by ring
         _ ≤ ε * scale n + D' * (1 + Real.log (2 + scale n)) :=
           add_le_add (mul_le_mul_of_nonneg_right he (hscale0 n).le)
             (mul_le_mul_of_nonneg_right hDD hlog)

end PolycyclicRecognition.CartanWordModel

end

end OAI
