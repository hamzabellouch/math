import OAI.Analysis.FreeEntropy.GUEFreeLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
 theorem heatMatrix_meanSquare_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k:ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0≤R)
    (hA : ∀ k i,matrixOpNorm (A k i)≤R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i,X i∈backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i,σ i∉J)
    (hbase : ∀ w,Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (wordMoment (tracialVector B N G) X w)))
    (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫ x, ‖matrixTraceWord (heatMatrix (A k) u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
  have hj (v : List (Fin (n+n))) :
      Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointFinMatrix (A k) x) v-
        wordMoment (tracialVector B N G) (jointTuple X σ) v‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
    have hm := expectedMatrixWord_free_tendsto hD0 hD A hR hA J X hX σ hσ hs hbase (v.map finSumFinEquiv.symm)
    have h := matrixTraceWord_mean_square_tendsto hD0 hD A hR hA (v.map finSumFinEquiv.symm) hm
    simpa only [← jointFinMatrix_trace,sumJointMoment,List.map_map,Function.comp_def,Equiv.apply_symm_apply,List.map_id',List.map_id_fun] using h
  have hpoly (k:ℕ) (v : List (Fin (n+n))) : IsComplexPolynomial (fun x : MatrixIndex n (D k) → ℝ => matrixTraceWord (jointFinMatrix (A k) x) v) := by
    simpa only [jointFinMatrix_trace] using matrixTraceWord_polynomial (A k) (v.map finSumFinEquiv.symm)
  have h := reparam_L2_tendsto (heatCoefficients u) (fun k x => matrixTraceWord (jointFinMatrix (A k) x))
    (wordMoment (tracialVector B N G) (jointTuple X σ)) hpoly hj w
  simpa only [reparam_matrixTraceWord,heatMatrix_linear,reparam_wordMoment,heat_linear_tuple] using h
 theorem heatMatrix_probability_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k:ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0≤R)
    (hA : ∀ k i,matrixOpNorm (A k i)≤R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i,X i∈backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i,σ i∉J)
    (hbase : ∀ w,Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (wordMoment (tracialVector B N G) X w)))
    (u : ℝ) (w : List (Fin n)) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (heatMatrix (A k) u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => probability_error_le_mean_square _ hε ?_)
    (by simpa using (heatMatrix_meanSquare_tendsto hD0 hD A hR hA J X hX σ hσ hs hbase u w).div_const (ε^2))
  apply IsComplexPolynomial.norm_sq
    (IsComplexPolynomial.sub ?_ (IsComplexPolynomial.const _)) |>.integrable
  have hp := reparam_polynomial (heatCoefficients u) (fun x => matrixTraceWord (jointFinMatrix (A k) x)) (fun v => by
    simpa only [jointFinMatrix_trace] using matrixTraceWord_polynomial (A k) (v.map finSumFinEquiv.symm)) w
  simpa only [reparam_matrixTraceWord,heatMatrix_linear] using hp
end FreeTensor
end FiniteEntropySeparation

end

end OAI
