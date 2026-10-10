import OAI.Analysis.LipschitzHilbert.Estimates.RelativeExitIntervals
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Dyadic selection of the relative exit scale for each nonzero interval. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert

/-- Relative radii, starting below one half as required by the pathwise argument. -/
def relativeExitScale (m : ℕ) : ℝ := (1/4)*(1/2)^m

theorem relativeExitScale_pos (m : ℕ) : 0<relativeExitScale m := by
  unfold relativeExitScale
  positivity

theorem relativeExitScale_le (m : ℕ) : relativeExitScale m≤1/4 := by
  unfold relativeExitScale
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) (n:=m))
    (by norm_num)).trans_eq (mul_one _)

theorem relativeExitScale_succ (m : ℕ) : relativeExitScale m=2*relativeExitScale (m+1) := by
  unfold relativeExitScale
  rw [pow_succ]
  ring

theorem exists_relativeExitScale {d R : ℝ} (hd : 0<d) (hR : 0≤R) (hdR : d≤2*R) :
    ∃ m : ℕ, 2*relativeExitScale m*R<d ∧ d≤8*relativeExitScale m*R := by
  have hRpos : 0<R := by linarith
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (show 0<2*d/R by positivity) (show (1:ℝ)/2<1 by norm_num)
  have hex : ∃ m, 2*relativeExitScale m*R<d := by
    refine ⟨n,?_⟩
    have ht : (1/2:ℝ)^n*R<2*d := (lt_div_iff₀ hRpos).mp hn
    unfold relativeExitScale
    nlinarith
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  cases h : Nat.find hex with
  | zero => norm_num [relativeExitScale]; exact hdR
  | succ m =>
    have hn := Nat.find_min hex (show m<Nat.find hex by omega)
    have hs := relativeExitScale_succ m
    have hp := relativeExitScale_pos (m+1)
    nlinarith

variable {Ω : Type*}

theorem relative_interval_scale (F : ℕ → Ω → ℝ) (H l b : ℕ) (hb : b<H)
    (hlb : l≤b) (x : Ω) (hd : 0<‖F b x-F l x‖) :
    ∃ m j : ℕ, j<H ∧ l<relativeExitTimes F (relativeExitScale m) H (j+1) x ∧
      relativeExitTimes F (relativeExitScale m) H (j+1) x≤b ∧
      ‖F b x-F l x‖^3≤2048*relativeExitScale m*runningOscillation F b x*
        ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
  have hdiam : ‖F b x-F l x‖≤2*runningOscillation F b x := by
    have h1 := le_runningOscillation F (le_refl b) x
    have h2 := le_runningOscillation F hlb x
    have ht : ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F l x-F 0 x‖ := by
      simpa only [norm_sub_rev (F 0 x) (F l x)] using (show ‖F b x-F l x‖≤‖F b x-F 0 x‖+‖F 0 x-F l x‖ by
        simpa only [dist_eq_norm] using dist_triangle (F b x) (F 0 x) (F l x))
    linarith
  obtain ⟨m,hm1,hm2⟩ := exists_relativeExitScale hd (runningOscillation_nonneg F b x) hdiam
  obtain ⟨j,hj,hl,hb',hjump⟩ := relative_interval_crosses_exit F (relativeExitScale m)
    (relativeExitScale_pos m).le ((relativeExitScale_le m).trans (by norm_num)) H l b hb hlb x hm1 hm2
  refine ⟨m,j,hj,hl,hb',?_⟩
  have hsq : ‖F b x-F l x‖^2≤256*
      ‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
        F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2 := by
    have hp := norm_nonneg (F b x-F l x)
    have hq := norm_nonneg (F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
      F (relativeExitTimes F (relativeExitScale m) H j x) x)
    nlinarith
  calc
    _ = ‖F b x-F l x‖*‖F b x-F l x‖^2 := by ring
    _ ≤ (8*relativeExitScale m*runningOscillation F b x)*
        (256*‖F (relativeExitTimes F (relativeExitScale m) H (j+1) x) x-
          F (relativeExitTimes F (relativeExitScale m) H j x) x‖^2) :=
      mul_le_mul hm2 hsq (sq_nonneg _) (by
        have := relativeExitScale_pos m
        have := runningOscillation_nonneg F b x
        positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
