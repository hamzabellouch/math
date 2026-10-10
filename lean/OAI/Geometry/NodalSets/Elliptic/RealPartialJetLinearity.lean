import Mathlib.Analysis.Calculus.ContDiff.Operations
import OAI.Geometry.NodalSets.Elliptic.CoordinatePartialJets

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section

theorem partialJet_sub {I : Type*} [Fintype I] [DecidableEq I]
    (f g : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ds : List I) (x : I → ℝ) :
    partialJet (fun y ↦ f y-g y) ds x = partialJet f ds x-partialJet g ds x := by
  rw [partialJet_eq_iterated _ (hf.sub hg),partialJet_eq_iterated f hf,partialJet_eq_iterated g hg]
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast
    (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  rfl

theorem partialJet_const_mul {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (a : ℝ) (ds : List I) (x : I → ℝ) :
    partialJet (fun y ↦ a*f y) ds x = a*partialJet f ds x := by
  rw [partialJet_eq_iterated _ (contDiff_const.mul hf),partialJet_eq_iterated f hf]
  change iteratedFDeriv ℝ ds.length (a • f) x (partialDirs ds) = _
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast
    (show (ds.length:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  rfl

theorem partialJet_norm_le_iterated {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (ds : List I) (x : I → ℝ) :
    |partialJet f ds x| ≤ ‖iteratedFDeriv ℝ ds.length f x‖ := by
  rw [partialJet_eq_iterated f hf]
  have h := (iteratedFDeriv ℝ ds.length f x).le_opNorm (partialDirs ds)
  have hp : (∏ i : Fin ds.length, ‖partialDirs ds i‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦
      (norm_le_pi_norm (partialDirs ds) i).trans (partialDirs_norm_le_one ds))
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ ds.length f x)))

end
end Yau.Analysis

end OAI
