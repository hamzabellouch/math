import OAI.Analysis.FreeEntropy.NoiseRotation

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

theorem fisher_cumulant_deficit {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hsa : ∀ i, IsSelfAdjoint (X i))
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hc : ∀ i, cumulants (wordMoment (tracialVector B N G) X) [i] = 0)
    (hcov : ∀ i j, cumulants (wordMoment (tracialVector B N G) X) [i,j] =
      if j=i then (v i : ℂ) else 0)
    (K u : ℝ) (hK : 0 ≤ K) (hu : 0 < u) (hKu : 2*K^2 ≤ u)
    (hR : ∀ m, degreeNorm (cumulants (wordMoment (tracialVector B N G) X)) m ≤ K^m)
    (hvar : ∀ i, ‖heatTuple X (fun k => semicircularN (σ k)) u i
      (tracialVector B N G).vacuum‖^2 = v i + u) :
    0 ≤ (freeFisher (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u)).toReal -
      ∑ i, (v i + u)⁻¹ ∧
    (freeFisher (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u)).toReal -
      ∑ i, (v i + u)⁻¹ ≤ 2*K^6/u^4 := by
  let R := cumulants (wordMoment (tracialVector B N G) X)
  let a : Fin n → List (Fin n) → ℂ := fun i => wickCoefficients (residual R v i) u
  have hKu' : K^2 < u := by nlinarith [sq_nonneg K]
  have ha (i : Fin n) : Summable (fun js => ‖a i js‖^2) :=
    wickCoefficient_summable hc hcov hK hR hu hKu' i
  let av : Fin n → LabelHilbert.Space (List (Fin n)) := fun i => wickCoefficientVector (a i) (ha i)
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist J X hX σ hσ hs u hu
  have ht (i : Fin n) (w : List (Fin n)) :=
    heat_cumulant_residual_hasSum J X hX hsa σ hσ hs u hu.le v i w
  have he (i : Fin n) (w : List (Fin n)) :
      inner ℂ (heatTuple X (fun k => semicircularN (σ k)) u i (tracialVector B N G).vacuum)
        (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w (tracialVector B N G).vacuum) -
      ((v i + u : ℝ) : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w =
      ∑' js, conj (av i js) * (Real.sqrt u : ℂ)^js.length * reverseDerivativeMoment
        (tracialVector B N G) (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
    change _ = ∑' js, conj (wickCoefficients (residual R v i) u js) *
      (Real.sqrt u : ℂ)^js.length * _
    simp_rw [wickCoefficients_cancel _ u hu]
    exact (ht i w).tsum_eq.symm
  have hb := fisher_wick_series_bound J X hX σ hσ hs u hu ξ hξ
    (fun i => v i + u) hvar (fun i => by linarith [hv i]) av he
  have hf : (freeFisher (tracialVector B N G)
      (heatTuple X (fun k => semicircularN (σ k)) u)).toReal = ∑ i, ‖ξ i‖^2 := by
    rw [freeFisher_eq_of_conjugate _ hξ, ENNReal.toReal_ofReal (sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [hf]
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hb' : ∑ i, ∑' js, ‖av i js‖^2 ≤ 2*K^6/u^2 :=
    wickCoefficient_total_bound hc hcov hK hR hu hKu
  calc
    _ ≤ (u^2)⁻¹ * (2*K^6/u^2) := mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by rw [show u^4 = u^2*u^2 by ring]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def cumulantConstant : ℝ := 128*Real.sqrt (Real.sqrt p)
def covarianceFisher (u : ℝ) : ℝ := ∑ i : Fin (p+1), (variance p i + u)⁻¹
def fisherDeficit (u : ℝ) : ℝ := (freeFisher (τ p) (X p u)).toReal - covarianceFisher p u
 theorem X_variance (u : ℝ) (hu : 0 ≤ u) (i : Fin (p+1)) :
    ‖X p u i (τ p).vacuum‖^2 = variance p i + u := by
  simpa [doublyNoised, heatTuple, variance] using doublyNoised_variance p u 0 hu (le_refl 0) i
 theorem fisherDeficit_bounds (hp : 2 ≤ p) (u : ℝ) (hu : 0 < u)
    (hKu : 2*(cumulantConstant p)^2 ≤ u) :
    0 ≤ fisherDeficit p u ∧ fisherDeficit p u ≤ 2*(cumulantConstant p)^6/u^4 :=
  fisher_cumulant_deficit ∅ (C p) (C_mem_background p ∅) (C_selfAdjoint p)
    (initialIndex p) (initialIndex_injective p) (by simp)
    (variance p) (variance_nonneg p) (signalCumulants_centered p hp) (signalCumulants_covariance p hp)
    (cumulantConstant p) u (by dsimp [cumulantConstant]; positivity) hu hKu
    (signalCumulants_norm_le p hp) (X_variance p u hu.le)
end Model
end FiniteEntropySeparation

end

end OAI
