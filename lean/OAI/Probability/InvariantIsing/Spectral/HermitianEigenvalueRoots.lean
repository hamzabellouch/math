import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternRotation
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace OAI

/-! Ordered Hermitian eigenvalues are uniquely determined by their real characteristic roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace InvariantIsing

lemma hermitian_eigenvalues₀_eval {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (t : ℝ) :
    A.charpoly.eval t = ∏ i : Fin (Fintype.card (Fin N)), (t-hA.eigenvalues₀ i) := by
  have hp := hA.roots_charpoly_eq_eigenvalues₀
  have hs := hA.splits_charpoly
  rw [hs.eval_eq_prod_roots_of_monic (Matrix.charpoly_monic A) t,hp]
  rw [Multiset.map_map]
  rfl

lemma hermitian_eigenvalues₀_unique {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (e : Fin (Fintype.card (Fin N)) → ℝ) (he : Antitone e)
    (hroot : ∀ t : ℝ, A.charpoly.eval t = ∏ i, (t-e i)) : hA.eigenvalues₀ = e := by
  have hp : A.charpoly = ∏ i, (X-C (e i)) := by
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using hroot t
  have hr : A.charpoly.roots = Multiset.map e Finset.univ.val := by
    rw [hp,Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero]
  have ho := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hr] at ho
  simp only [Fin.univ_val_map,Multiset.map_coe,List.map_ofFn,Function.comp_def,
    RCLike.re_to_real,Multiset.coe_sort] at ho
  have hsort : (List.ofFn e).mergeSort (fun x y => decide (x ≥ y)) = List.ofFn e := by
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq,← List.sortedGE_iff_pairwise]
    exact he.sortedGE_ofFn
  rw [hsort] at ho
  exact List.ofFn_inj.mp ho.symm

lemma hermitian_eigenvalues₀_norm_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (i : Fin (Fintype.card (Fin N))) : |hA.eigenvalues₀ i| ≤ ‖A‖ := by
  let j : Fin N := (Fintype.equivOfCardEq (Fintype.card_fin _)) i
  let : Nonempty (Fin N) := ⟨j⟩
  have hm := hA.eigenvalues_mem_spectrum_real j
  have hh := spectrum.norm_le_norm_of_mem hm
  simpa only [Real.norm_eq_abs,Matrix.IsHermitian.eigenvalues,j,Equiv.symm_apply_apply] using hh

lemma hermitian_eval_tendsto {N : ℕ} {A : ℕ → Matrix (Fin N) (Fin N) ℝ}
    {B : Matrix (Fin N) (Fin N) ℝ} (hA : Filter.Tendsto A Filter.atTop (nhds B)) (t : ℝ) :
    Filter.Tendsto (fun n => (A n).charpoly.eval t) Filter.atTop (nhds (B.charpoly.eval t)) := by
  simp only [Matrix.eval_charpoly]
  exact ((continuous_const.sub continuous_id).matrix_det.tendsto B).comp hA

end InvariantIsing

end

end OAI
