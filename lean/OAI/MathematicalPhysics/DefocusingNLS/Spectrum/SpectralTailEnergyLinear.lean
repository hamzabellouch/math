import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEnergyOperations

namespace OAI

/-! Finite linear combinations preserve the weighted top energy on a tail. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem spectralWeighted_top_smul_integrable (u : ℝ → V) (R : ℝ) (N : ℕ) (c : ℂ)
    (hu : IntegrableOn (fun r => r^11*‖iteratedDeriv N u r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (fun s => c • u s) r‖^2) (Ioi R) := by
  simpa only [iteratedDeriv_fun_const_smul_field] using
    spectralWeighted_square_smul_integrable (iteratedDeriv N u) R c hu

theorem spectralWeighted_top_add_integrable (u v : ℝ → V) (R : ℝ) (hR : 0≤R) (N : ℕ)
    (hcU : ContDiffOn ℝ ∞ u (Ioi R)) (hcV : ContDiffOn ℝ ∞ v (Ioi R))
    (hu : IntegrableOn (fun r => r^11*‖iteratedDeriv N u r‖^2) (Ioi R))
    (hv : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (fun s => u s+v s) r‖^2) (Ioi R) := by
  have hn := spectralWeighted_top_smul_integrable v R N (-1) hv
  have hh := spectralWeighted_top_sub_integrable u (fun s => (-1 : ℂ) • v s) R hR N
    hcU (hcV.const_smul (-1 : ℂ)) hu hn
  simpa only [neg_one_smul,sub_neg_eq_add] using hh

theorem spectralWeighted_top_combination_integrable (u v : ℝ → V)
    (R : ℝ) (hR : 0≤R) (N : ℕ) (a b : ℂ)
    (hcU : ContDiffOn ℝ ∞ u (Ioi R)) (hcV : ContDiffOn ℝ ∞ v (Ioi R))
    (hu : IntegrableOn (fun r => r^11*‖iteratedDeriv N u r‖^2) (Ioi R))
    (hv : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (fun s => a • u s+b • v s) r‖^2) (Ioi R) :=
  spectralWeighted_top_add_integrable _ _ R hR N (hcU.const_smul a) (hcV.const_smul b)
    (spectralWeighted_top_smul_integrable u R N a hu)
    (spectralWeighted_top_smul_integrable v R N b hv)

end DefocusingNLS

end OAI
