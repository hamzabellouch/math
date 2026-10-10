import OAI.MeasureTheory.Falconer.Angular.GnomonicInverse

namespace OAI

/-! # Gnomonic sectors as ordinary Euclidean cones -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

noncomputable def gnomonicCone {n : ℕ} (A : Set (Space n)) : Set (Space (n+1)) :=
  Ioo (0:ℝ) 1 • (Subtype.val '' (gnomonicChart '' A))

theorem gnomonicRatio_measurable (n : ℕ) : Measurable (@gnomonicRatio n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  exact (EuclideanSpace.proj i.succ).continuous.measurable.div
    (EuclideanSpace.proj 0).continuous.measurable

theorem gnomonicRatio_smul {n : ℕ} (r : ℝ) (hr : r ≠ 0) (z : Space (n+1)) :
    gnomonicRatio (r • z) = gnomonicRatio z := by
  apply PiLp.ext
  intro i
  simp only [gnomonicRatio_apply,PiLp.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ hr

theorem gnomonicCone_eq {n : ℕ} (A : Set (Space n)) :
    gnomonicCone A = {z | 0 < z 0 ∧ gnomonicRatio z ∈ A ∧ ‖z‖ < 1} := by
  ext z
  constructor
  · rintro ⟨r,hr,_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
    refine ⟨?_,?_,?_⟩
    · simp only [PiLp.smul_apply,smul_eq_mul,gnomonicChart_zero]
      exact mul_pos hr.1 (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x)))
    · rw [gnomonicRatio_smul r hr.1.ne',gnomonicRatio_chart]
      exact hx
    · simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,sphere_norm,mul_one] using hr.2
  · rintro ⟨hz,hA,hbound⟩
    have hpoint : gnomonicConePoint (z 0) (gnomonicRatio z) = z := by
      rw [gnomonicConePoint,northLift_gnomonicRatio z hz.ne',smul_smul,
        mul_inv_cancel₀ hz.ne',one_smul]
    have hn : z 0*‖northLift (gnomonicRatio z)‖ = ‖z‖ := by
      conv_rhs => rw [← hpoint]
      rw [gnomonicConePoint,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    refine ⟨z 0*‖northLift (gnomonicRatio z)‖,?_,
      (gnomonicChart (gnomonicRatio z) : Space (n+1)),?_,?_⟩
    · exact ⟨mul_pos hz (norm_pos_iff.mpr (northLift_ne_zero _)),hn.trans_lt hbound⟩
    · exact ⟨gnomonicChart (gnomonicRatio z),⟨gnomonicRatio z,hA,rfl⟩,rfl⟩
    · exact (gnomonicConePoint_radius (z 0) (gnomonicRatio z)).symm.trans hpoint

theorem gnomonicCone_measurable {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    MeasurableSet (gnomonicCone A) := by
  rw [gnomonicCone_eq]
  exact (measurableSet_lt measurable_const (EuclideanSpace.proj 0).continuous.measurable).inter
    ((hA.preimage (gnomonicRatio_measurable n)).inter (measurableSet_lt measurable_norm measurable_const))

theorem gnomonicConePoint_mem_iff {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r)
    (x : Space n) : gnomonicConePoint r x ∈ gnomonicCone A ↔
      x ∈ A ∧ r < ‖northLift x‖⁻¹ := by
  rw [gnomonicCone_eq]
  simp only [mem_ofPred_eq,gnomonicConePoint_zero,gnomonicRatio_conePoint r hr.ne',
    hr,true_and]
  rw [gnomonicConePoint,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hn := norm_pos_iff.mpr (northLift_ne_zero x)
  rw [← one_div,lt_div_iff₀ hn]

end Falconer

end OAI
