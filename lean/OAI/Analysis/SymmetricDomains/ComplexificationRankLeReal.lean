import Mathlib
import OAI.Analysis.SymmetricDomains.HorizontalGraphComplexification
import OAI.Analysis.SymmetricDomains.AnalyticGermMatrixRank

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Matrix Module

theorem complexification_real_partial {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (q : (Fin n → ℝ) → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hext : (fun x : Fin n → ℝ => f (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q) :
    ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), ∀ i : Fin n,
      fderiv ℂ f (fun j => (x j : ℂ)) (Pi.single i 1) =
        fderiv ℝ q x (Pi.single i 1) := by
  have he : Filter.Tendsto (Flatten.realEmbedding n) (𝓝 0) (𝓝 0) := by
    have he := (Flatten.realEmbedding n).continuous.continuousAt (x := 0)
    rw [ContinuousAt,map_zero] at he
    exact he
  have hqeq : (fun x => f (Flatten.realEmbedding n x)) =ᶠ[𝓝 0] q := hext
  filter_upwards [he hf.eventually_analyticAt, hqeq.fderiv (𝕜 := ℝ)] with x hfx hx
  intro i
  have hd := (hfx.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x
    (Flatten.realEmbedding n).hasFDerivAt
  have hsingle : Flatten.realEmbedding n (Pi.single i 1) = Pi.single i (1 : ℂ) := by
    ext j
    by_cases hji : j = i <;> simp [Flatten.realEmbedding,hji]
  have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (Pi.single i 1))
    (hd.fderiv.symm.trans hx)
  change fderiv ℂ f (Flatten.realEmbedding n x) (Flatten.realEmbedding n (Pi.single i 1)) = _ at hv
  rw [hsingle] at hv
  exact hv

@[simp] theorem meromorphicPartial_germ {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) (i : Fin n) :
    meromorphicPartial i (meromorphicGermOf f hf) =
      meromorphicGermOf (fun z => fderiv ℂ f z (Pi.single i 1))
        (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : Fin n → ℂ)).analyticAt _).comp hf.fderiv) := by
  simp only [meromorphicPartial,meromorphicGermOf,meromorphicDirectionalDerivation_algebraMap,
    analyticDirectionalDerivation_ofFun]

theorem complexification_rank_le_real_rank {n N : ℕ}
    (f : Fin N → (Fin n → ℂ) → ℂ) (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (q : (Fin n → ℝ) → Fin N → ℂ)
    (hext : (fun (x : Fin n → ℝ) j => f j (fun i => (x i : ℂ))) =ᶠ[𝓝 0] q)
    (B : Set (Fin n → ℝ)) (hB : B ∈ 𝓝 0) :
    ∃ x ∈ B, Matrix.rank (fun j i => meromorphicPartial i (meromorphicGermOf (f j) (hf j))) ≤
      Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) := by
  have he : ∀ j, ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), ∀ i : Fin n,
      fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1) =
        fderiv ℝ (fun y => q y j) x (Pi.single i 1) := by
    intro j
    apply complexification_real_partial (f j) (fun y => q y j) (hf j)
    exact hext.mono fun x hx => congrFun hx j
  let C := B ∩ {x | ∀ j i, fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1) =
    fderiv ℝ (fun y => q y j) x (Pi.single i 1)}
  have hC : C ∈ 𝓝 0 := inter_mem hB (Filter.eventually_all.mpr he)
  obtain ⟨x,hx,hr⟩ := analytic_germ_matrix_rank_le_real_rank
    (fun j i z => fderiv ℂ (f j) z (Pi.single i 1))
    (fun j i => ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : Fin n → ℂ)).analyticAt _).comp (hf j).fderiv)
    C hC
  refine ⟨x,hx.1,?_⟩
  simp only [meromorphicPartial_germ]
  have heq : (fun j i => fderiv ℂ (f j) (fun k => (x k : ℂ)) (Pi.single i 1)) =
      (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) :=
    funext fun j => funext (hx.2 j)
  exact hr.trans_eq (congrArg (fun M : Matrix (Fin N) (Fin n) ℂ => M.rank) heq)

end Release061

end

end OAI
