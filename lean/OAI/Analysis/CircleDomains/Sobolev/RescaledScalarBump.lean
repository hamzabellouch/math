import OAI.Analysis.CircleDomains.Modulus.FixedCapacityCutoffs

namespace OAI

/-! The fixed scalar cutoff translated to a level and rescaled to its
band width, with its exact derivative and support. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def rescaledScalarBump (t s : ℝ) (y : ℝ) : ℝ :=
  scalarCapacityBump ((y-t)/s)

lemma rescaledScalarBump_contDiff (t s : ℝ) :
    ContDiff ℝ 1 (rescaledScalarBump t s) :=
  scalarCapacityBump.contDiff.comp ((contDiff_id.sub contDiff_const).div_const s)

lemma rescaledScalarBump_deriv (t s y : ℝ) :
    deriv (rescaledScalarBump t s) y =
      deriv scalarCapacityBump ((y-t)/s) / s := by
  have hd := ((scalarCapacityBump.contDiff : ContDiff ℝ 1
    (scalarCapacityBump : ℝ → ℝ)).differentiable one_ne_zero ((y-t)/s)).hasDerivAt.comp y
      (((hasDerivAt_id y).sub_const t).div_const s)
  have he : (scalarCapacityBump : ℝ → ℝ) ∘ (fun x => (id x-t)/s) = rescaledScalarBump t s := rfl
  rw [he] at hd
  simpa only [one_div, div_eq_mul_inv, one_mul] using hd.deriv

lemma rescaledScalarBump_unit (t s y : ℝ) : rescaledScalarBump t s y ∈ Icc 0 1 :=
  ⟨scalarCapacityBump.nonneg,scalarCapacityBump.le_one⟩

lemma rescaledScalarBump_one (t : ℝ) {s y : ℝ} (hs : 0 < s) (hy : |y-t| ≤ s) :
    rescaledScalarBump t s y = 1 := by
  apply scalarCapacityBump_one
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact hy

lemma rescaledScalarBump_zero (t : ℝ) {s y : ℝ} (hs : 0 < s) (hy : 2*s < |y-t|) :
    rescaledScalarBump t s y = 0 ∧ deriv (rescaledScalarBump t s) y = 0 := by
  have h : 2 < |(y-t)/s| := by
    rw [abs_div, abs_of_pos hs]
    exact (lt_div_iff₀ hs).mpr hy
  obtain ⟨hz,hd⟩ := scalarCapacityBump_zero h
  exact ⟨hz,by rw [rescaledScalarBump_deriv,hd,zero_div]⟩

lemma rescaledScalarBump_deriv_bound {C : ℝ}
    (hC : ∀ t, ‖deriv scalarCapacityBump t‖ ≤ C)
    (t : ℝ) {s : ℝ} (hs : 0 < s) (y : ℝ) :
    ‖deriv (rescaledScalarBump t s) y‖ ≤ C/s := by
  rw [rescaledScalarBump_deriv,norm_div,Real.norm_eq_abs s,abs_of_pos hs]
  exact div_le_div_of_nonneg_right (hC _) hs.le

end CircleDomainRigidity

end

end OAI
