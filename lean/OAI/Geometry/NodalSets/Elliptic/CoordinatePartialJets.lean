import Mathlib.Analysis.Calculus.ContDiff.Comp
import OAI.Geometry.NodalSets.Elliptic.AnchoredCubeBound

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def partialDirs : (ds : List ι) → Fin ds.length → (ι → ℝ)
  | [] => Fin.elim0
  | i::ds => Fin.cons (Pi.single i 1) (partialDirs ds)

def partialJet (f : (ι → ℝ) → ℝ) : List ι → (ι → ℝ) → ℝ
  | [] => f
  | i::ds => fun x ↦ fderiv ℝ (partialJet f ds) x (Pi.single i 1)

lemma partialJet_smooth (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) : ContDiff ℝ ∞ (partialJet f ds) := by
  induction ds with
  | nil => exact hf
  | cons i ds ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma partialJet_eq_iterated (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) (x : ι → ℝ) :
    partialJet f ds x = iteratedFDeriv ℝ ds.length f x (partialDirs ds) := by
  induction ds generalizing x with
  | nil => simp [partialJet,partialDirs,iteratedFDeriv_zero_apply]
  | cons i ds ih =>
    have hh : partialJet f ds = fun x ↦ iteratedFDeriv ℝ ds.length f x (partialDirs ds) :=
      funext ih
    change fderiv ℝ (partialJet f ds) x (Pi.single i 1) = _
    rw [hh]
    symm
    have hdiff := hf.differentiable_iteratedFDeriv (m := ds.length)
      (by exact_mod_cast (show (ds.length:ℕ∞) < ⊤ from WithTop.coe_lt_top _))
    simpa only [List.length_cons,partialDirs,Fin.cons_zero,Fin.tail_cons] using
      (hdiff x).iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (partialDirs ds))

lemma partialDirs_norm_le_one (ds : List ι) : ‖partialDirs ds‖ ≤ 1 := by
  induction ds with
  | nil => exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun j ↦ Fin.elim0 j)
  | cons i ds ih =>
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at ih ⊢
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change ‖(Pi.single i (1:ℝ) : ι → ℝ)‖ ≤ 1
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro k
      by_cases h : k = i <;> simp [h]
    · simpa [partialDirs] using ih k

end
end Yau.Analysis

end OAI
