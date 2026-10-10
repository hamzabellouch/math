import OAI.Analysis.AncientFlat.Evolution.CompactDifference
import OAI.Analysis.AncientFlat.Evolution.ConstantPowers
import OAI.Analysis.AncientFlat.Spectral.QuasiSpectrum

namespace OAI
noncomputable section
open Set Filter
open scoped ZeroAtInfty
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem exists_nonspectral_circle (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (P : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ))
    (hP : TimeOneMap Af Bf P) :
    ∃ q : ℝ, Real.exp (-(1:ℝ)/2)<q ∧ q<1 ∧
      ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P := by
  obtain ⟨Pc,hPc⟩ := exists_constant_time_one (V := V) c h.1
  obtain ⟨C,hC⟩ := hPc.constant_power_bound h.1
  exact FlatSpectral.exists_circle_of_compact_difference_power_bound P Pc
    (compact_time_one_difference c Af Bf h P Pc hP hPc) _ C (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by norm_num)) hC
end FlatSimilarity

end

end OAI
