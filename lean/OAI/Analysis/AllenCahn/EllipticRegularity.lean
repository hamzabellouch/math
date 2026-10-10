import OAI.Analysis.AllenCahn.DyadicDerivatives

namespace OAI

noncomputable section
namespace RegularitySupport.DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff
open MeasureTheory
open scoped ENNReal

lemma iteratedFDeriv_apply_bound_of_difference_bound {n k : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : ContDiff ℝ ∞ f) (hM : 0 ≤ M) (hb : DifferenceBound (2 * k) f M)
    (x : Space n) (v : Fin k → Space n) :
    |iteratedFDeriv ℝ k f x v| ≤ M * ∏ i : Fin k, ‖v i‖ := by
  induction k generalizing f M with
  | zero =>
    have h := hb [] (by simp) x
    simpa [iteratedFDeriv_zero_apply, iterDifference, differenceScale] using h
  | succ k ih =>
    let h : Space n := v (Fin.last k)
    have hder : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hg : ContDiff ℝ ∞ (fun y => fderiv ℝ f y h) := hder.clm_apply contDiff_const
    have hbd : DifferenceBound (2 * k + 2) f M := by convert hb using 1
    have hh := differenceBound_fderiv_apply hbd hM h
    have hi := ih hg (mul_nonneg hM (norm_nonneg h)) hh (Fin.init v)
    rw [iteratedFDeriv_succ_apply_right, ← iteratedFDeriv_clm_apply_const_apply hder (i := k) (by exact WithTop.coe_le_coe.mpr le_top)]
    calc
      _ ≤ M * ‖h‖ * ∏ i : Fin k, ‖Fin.init v i‖ := hi
      _ = M * ∏ i : Fin (k + 1), ‖v i‖ := by
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.init, h]
        ring

lemma iteratedFDeriv_bound_of_difference_bound {n k : ℕ} {f : Space n → ℝ} {M : ℝ}
    (hf : ContDiff ℝ ∞ f) (hM : 0 ≤ M) (hb : DifferenceBound (2 * k) f M)
    (x : Space n) : ‖iteratedFDeriv ℝ k f x‖ ≤ M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hM
  intro v
  simpa only [Real.norm_eq_abs] using iteratedFDeriv_apply_bound_of_difference_bound hf hM hb x v

lemma allenCahn_smooth {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hrange : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) (hpde : AllenCahn v) :
    ContDiff ℝ ∞ v :=
  contDiff_infty_of_difference_bounds (allenCahn_difference_bounds hv hrange hpde)

lemma allenCahn_uniform_derivatives {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ 2 v) (hrange : ∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) (hpde : AllenCahn v)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ C := by
  obtain ⟨M, hM, hb⟩ := allenCahn_difference_bounds hv hrange hpde (2 * k)
  exact ⟨M, hM, iteratedFDeriv_bound_of_difference_bound (allenCahn_smooth hv hrange hpde) hM hb⟩

lemma allenCahn_uniform_derivatives_dim (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Space n → ℝ, ContDiff ℝ 2 v →
      (∀ x, v x ∈ Set.Icc (-1 : ℝ) 1) → AllenCahn v →
      ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ C := by
  obtain ⟨M, hM, hb⟩ := allenCahn_difference_bounds_uniform n (2 * k)
  refine ⟨M, hM, ?_⟩
  intro v hv hrange hpde
  exact iteratedFDeriv_bound_of_difference_bound (allenCahn_smooth hv hrange hpde) hM (hb v hv hrange hpde)

end RegularitySupport.DeGiorgi
end

end OAI
