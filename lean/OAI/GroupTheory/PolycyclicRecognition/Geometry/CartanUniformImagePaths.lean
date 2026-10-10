import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMappedTemplatePaths

namespace OAI

/-! # Uniform constants for the selected bounded-length paths -/

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

/-- One pair of path constants works for every chain of bounded length.
It controls both coarse metric bounds and the logarithmic height error. -/
theorem exists_bounded_mapped_template_profile_paths
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
    {B : ℝ} (hB : 0 ≤ B) (N₀ : ℕ) (Λ : ℝ≥0) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | h (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ (N : ℕ), N ≤ N₀ → ∀ (x : G) (vertex : Fin (N + 1) → G)
        (mode : Fin N → Fin M.letterCount) (coeff : Fin N → ℝ),
        (∀ j, vertex j.succ = vertex j.castSucc *
          Exp (coeff j • (M.letter (mode j) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
        (∀ j, |coeff j| ≤ B * Real.exp (scale n *
          (M.supportIn T hunimod eW).weightSupport E (mode j))) →
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
          ∀ t, ∃ z ∈ (fun w => A (w - h pivot)) '' E,
            ‖(π (path t)).toAdd - scale n • z‖ ≤
              2 * scale n * ε + C * (1 + Real.log (2 + scale n)) := by
  dsimp only
  obtain ⟨Q, C, hQ, hQV, hC, hpaths⟩ := M.exists_mapped_template_profile_paths T F eW
    hExp realize haarD dynkinD π hπ hLip X hDnil bD₀ βD hβD scale hscale hscale0
    hunimod pivot E V hEc hE hpivot hV hVconv hEV hB
  let L := max ((Λ : ℝ) * C * 2 ^ N₀) ((K : ℝ) * Λ * C)
  have hL : 0 ≤ L := (by positivity : 0 ≤ (Λ : ℝ) * C * 2 ^ N₀).trans
    (le_max_left _ _)
  refine ⟨Q, L, hQ, hQV, hL, ?_⟩
  filter_upwards [hpaths] with n hn
  intro N hN x vertex mode coeff hstep hamp f hf A offset ε hgood
  obtain ⟨path, hm, hh⟩ := hn N x vertex mode coeff hstep hamp f Λ hf A offset ε hgood
  have hpow : (2 : ℝ) ^ N ≤ 2 ^ N₀ := pow_le_pow_right₀ (by norm_num) hN
  have hcoef : (Λ : ℝ) * C * 2 ^ N ≤ L :=
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg Λ.coe_nonneg hC)).trans
      (le_max_left _ _)
  have hlog : 0 ≤ Real.log (2 + scale n) := Real.log_nonneg (by linarith [hscale0 n])
  have hsum : 0 ≤ 1 + Real.log (2 + scale n) := by linarith
  refine ⟨path, hm.mono ?_ ?_, ?_⟩
  · calc
      _ = ((Λ : ℝ) * C * 2 ^ N) * scale n := by ring
      _ ≤ L * scale n := mul_le_mul_of_nonneg_right hcoef (hscale0 n).le
  · calc
      _ = ((Λ : ℝ) * C * 2 ^ N) * (1 + Real.log (2 + scale n)) := by ring
      _ ≤ L * (1 + Real.log (2 + scale n)) := mul_le_mul_of_nonneg_right hcoef hsum
  · intro t
    obtain ⟨z, hz, he⟩ := hh t
    refine ⟨z, hz, he.trans (add_le_add le_rfl ?_)⟩
    calc
      _ = ((K : ℝ) * Λ * C) * Real.log (2 + scale n) := by ring
      _ ≤ L * Real.log (2 + scale n) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
      _ ≤ L * (1 + Real.log (2 + scale n)) := by nlinarith

end PolycyclicRecognition.CartanWordModel

end

end OAI
