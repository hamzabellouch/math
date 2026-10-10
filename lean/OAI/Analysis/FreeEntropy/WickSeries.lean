import OAI.Analysis.FreeEntropy.FisherResidual

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 def noiseWickIsometry {n : ℕ} (σ : Fin n → N) (hσ : Function.Injective σ) :
    LabelHilbert.Space (List (Fin n)) →ₗᵢ[ℂ] Space B N G :=
  LabelHilbert.embedding (fun js => noiseWord ((js.map σ).reverse)) (by
    intro js ks h
    apply List.map_injective_iff.mpr hσ
    exact List.reverse_injective (noiseWord_injective h))

@[simp] theorem noiseWickIsometry_single {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (js : List (Fin n)) (z : ℂ) :
    noiseWickIsometry (B := B) (G := G) σ hσ (lp.single 2 js z) =
      z • basis (noiseWord ((js.map σ).reverse)) := by
  have hz : z • (basis (noiseWord ((js.map σ).reverse)) : Space B N G) =
      lp.single 2 (noiseWord ((js.map σ).reverse)) z := by
    simp [basis, ← lp.single_smul]
  rw [hz]
  exact LabelHilbert.embedding_single _ _ js z

 theorem noiseWickIsometry_norm_sq {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n))) :
    ‖noiseWickIsometry (B := B) (G := G) σ hσ a‖ ^ 2 = ∑' js, ‖a js‖ ^ 2 := by
  rw [LinearIsometry.norm_map]
  convert lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a using 1 <;> norm_cast

 theorem noiseWickIsometry_hasSum {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n))) :
    HasSum (fun js => a js • (basis (noiseWord ((js.map σ).reverse)) : Space B N G))
      (noiseWickIsometry σ hσ a) := by
  simpa only [LinearIsometry.coe_toContinuousLinearMap, noiseWickIsometry_single] using
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) a).mapL
      (noiseWickIsometry (B := B) (G := G) σ hσ).toContinuousLinearMap

 theorem noiseWickIsometry_inner_hasSum {n : ℕ} (σ : Fin n → N)
    (hσ : Function.Injective σ) (a : LabelHilbert.Space (List (Fin n)))
    (x : Space B N G) :
    HasSum (fun js => conj (a js) * inner ℂ (basis (noiseWord ((js.map σ).reverse))) x)
      (inner ℂ (noiseWickIsometry σ hσ a) x) := by
  have h := ((noiseWickIsometry_hasSum (B := B) (G := G) σ hσ a).mapL (innerSL ℂ x))
  have hc := Complex.hasSum_conj'.mpr h
  simpa only [innerSL_apply_apply, inner_smul_right, map_mul, inner_conj_symm] using hc

theorem wick_series_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (a : LabelHilbert.Space (List (Fin n))) (w : List (Fin n)) :
    inner ℂ (noiseWickIsometry σ hσ a)
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      ∑' js, conj (a js) * (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  have h := noiseWickIsometry_inner_hasSum σ hσ a
    (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
      (tracialVector B N G).vacuum)
  simp only [wick_testing J X hX σ hσ hs u, ← mul_assoc] at h
  exact h.tsum_eq.symm

 def wickCoefficientVector {n : ℕ} (a : List (Fin n) → ℂ)
    (ha : Summable (fun js => ‖a js‖ ^ 2)) : LabelHilbert.Space (List (Fin n)) :=
  ⟨a, (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr (by simpa using ha)⟩

 theorem fisher_wick_series_bound {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (hu : 0 < u)
    (ξ : Fin n → Space B N G)
    (hξ : ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun k => semicircularN (σ k)) u) ξ)
    (v : Fin n → ℝ)
    (hv : ∀ i, ‖heatTuple X (fun k => semicircularN (σ k)) u i
      (tracialVector B N G).vacuum‖ ^ 2 = v i)
    (hvu : ∀ i, u ≤ v i)
    (a : Fin n → LabelHilbert.Space (List (Fin n)))
    (hseries : ∀ i w,
      inner ℂ (heatTuple X (fun k => semicircularN (σ k)) u i
        (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
          (tracialVector B N G).vacuum) -
        (v i : ℂ) * derivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) i w =
      ∑' js, conj (a i js) * (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w) :
    0 ≤ (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ∧
      (∑ i, ‖ξ i‖ ^ 2) - (∑ i, (v i)⁻¹) ≤
        (u ^ 2)⁻¹ * ∑ i, ∑' js, ‖a i js‖ ^ 2 := by
  have hr (i : Fin n) (w : List (Fin n)) :=
    (hseries i w).trans (wick_series_testing J X hX σ hσ hs u (a i) w).symm
  simpa only [noiseWickIsometry_norm_sq] using
    fisher_residual_bound (tracialVector B N G) hξ v u hu hv hvu
      (fun i => noiseWickIsometry σ hσ (a i)) hr

end FreeTensor
end FiniteEntropySeparation

end

end OAI
