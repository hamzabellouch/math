import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformImagePaths

namespace OAI

/-! # One compact profile domain for the three probe chains -/

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

/-- The first, anchor and within-tile chains share one compact set of
profile coordinates and one pair of metric and height constants. -/
theorem exists_three_template_profile_paths
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
    (pivot : H) (E : Fin 3 → Set W) (V : Set W) (hEc : ∀ k, IsCompact (E k))
    (hE : ∀ k, Convex ℝ (E k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ E k)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : ∀ k, E k ⊆ V)
    {B : ℝ} (hB : 0 ≤ B) (N₀ : ℕ) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (k : Fin 3) (N : ℕ), N ≤ N₀ → ∀ (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport (E k) (mode j))) →
        ∀ (f : G → G), LipschitzWith Λ f →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ i z, z ∈ Q →
          ‖rescaledMapProfile (fun g => (π (f g)).toAdd) x (vertex i)
              (Real.log (scale n)) (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (h (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        let start := x * vertex 0 * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        let finish := x * vertex (Fin.last N) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))
        ∃ path : Path (1 : G) (basedImage f start finish),
          PathMetricBound path (C * scale n)
            (C * (1 + Real.log (2 + scale n))) ∧
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E k,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  classical
  dsimp only
  have hall := fun k : Fin 3 => M.exists_bounded_mapped_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot (E k) V (hEc k) (hE k) (hpivot k) hV hVconv (hEV k) hB N₀ Λ
  dsimp only at hall
  choose Q L hQ hQV hL hpaths using hall
  let Qall := ⋃ k : Fin 3, Q k
  let Lall := ∑ k : Fin 3, L k
  have hLall : 0 ≤ Lall := Finset.sum_nonneg (fun k _ => hL k)
  have hLle (k : Fin 3) : L k ≤ Lall :=
    Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ k)
  have hev := (Filter.eventually_all).mpr hpaths
  refine ⟨Qall, Lall, isCompact_iUnion hQ, ?_, hLall, ?_⟩
  · intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact hQV k hk
  · filter_upwards [hev] with n hn
    intro k N hN x vertex mode coeff hstep hamp f hf A offset ε hgood
    obtain ⟨path, hm, hh⟩ := hn k N hN x vertex mode coeff hstep hamp f hf A offset ε
      (fun i z hz => hgood i z (mem_iUnion.mpr ⟨k, hz⟩))
    have hlog : 0 ≤ 1 + Real.log (2 + scale n) := by
      have := Real.log_nonneg (show 1 ≤ 2 + scale n by linarith [hscale0 n])
      linarith
    refine ⟨path, hm.mono (mul_le_mul_of_nonneg_right (hLle k) (hscale0 n).le)
      (mul_le_mul_of_nonneg_right (hLle k) hlog), ?_⟩
    intro t
    obtain ⟨z, hz, he⟩ := hh t
    exact ⟨z, hz, he.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hLle k) hlog))⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
