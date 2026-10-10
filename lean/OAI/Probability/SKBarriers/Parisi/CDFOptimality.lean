import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFMassVariation
import OAI.Probability.SKBarriers.Parisi.CDFMinimizer

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFParisi_minimizer_variation_nonneg {β : ℝ} (hβ : β≠0)
    (α γ : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hg : ∀ z, γ z∈Icc (0:ℝ) 1) (hγ1 : γ 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β) :
    0≤∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s) := by
  have H := scalarCDFParisi_mass_quotient_tendsto β α γ ha hα1 hg hγ1
  have Hθ : ∀ᶠ θ : ℝ in 𝓝[>] (0:ℝ), θ<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have Hn : 0≤(β^2/2)*∫ s in Icc (0:ℝ) 1, (γ s-α s)*(scalarCDFOverlap β α s-s) := by
    apply ge_of_tendsto H
    filter_upwards [Hθ,self_mem_nhdsWithin] with θ hθ1 hθ0
    have Hmin := finiteParisiInf_le_scalarCDFParisi β
      (cdfMassSegmentStieltjes α γ θ ⟨le_of_lt hθ0,hθ1.le⟩)
      (cdfMassSegment_bounds ha hg ⟨le_of_lt hθ0,hθ1.le⟩)
      (cdfMassSegment_one hα1 hγ1 θ)
    rw [← hmin] at Hmin
    exact div_nonneg (sub_nonneg.mpr Hmin) (le_of_lt hθ0)
  exact nonneg_of_mul_nonneg_right Hn (div_pos (sq_pos_of_ne_zero hβ) (by norm_num))

def pointCDF (q : ℝ) : StieltjesFunction ℝ := cdf (Measure.dirac q)

theorem pointCDF_apply (q s : ℝ) : pointCDF q s=unitCDF q s := by
  by_cases h : q ≤ s <;> simp [pointCDF,cdf_eq_real,Measure.real,unitCDF,h]

theorem pointCDF_bounds (q z : ℝ) : pointCDF q z∈Icc (0:ℝ) 1 :=
  ⟨cdf_nonneg _ _,cdf_le_one _ _⟩

theorem pointCDF_one {q : ℝ} (hq : q≤1) : pointCDF q 1=1 := by
  rw [pointCDF_apply,unitCDF,ite_eq_left hq]

end SK.Analytic

end
end

end OAI
