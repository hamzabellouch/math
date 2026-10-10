import OAI.Probability.InvariantIsing.Haar.HaarFrobeniusGeometry

namespace OAI

/-! Frobenius-Lipschitz observables are continuous in the matrix-group topology. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace InvariantIsing

lemma continuous_frobeniusDistance_right {N : ℕ} (U : SpecialOrthogonal N) :
    Continuous (fun V => frobeniusDistance V U) := by
  have he (i j : Fin N) : Continuous (fun V : SpecialOrthogonal N =>
      (V : Matrix (Fin N) (Fin N) ℝ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  unfold frobeniusDistance
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((he i j).sub continuous_const).pow 2

lemma frobeniusDistance_self {N : ℕ} (U : SpecialOrthogonal N) : frobeniusDistance U U = 0 := by
  simp [frobeniusDistance]

theorem continuous_of_frobenius_lipschitz {N : ℕ} (f : SpecialOrthogonal N → ℝ) (L : ℝ)
    (hf : ∀ U V, |f U-f V| ≤ L*frobeniusDistance U V) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun V => norm_nonneg _) (fun V => by simpa only [Real.norm_eq_abs] using hf V U)
  have hh := ((continuous_frobeniusDistance_right U).tendsto U).const_mul L
  simpa only [frobeniusDistance_self,mul_zero] using hh

end InvariantIsing

end

end OAI
