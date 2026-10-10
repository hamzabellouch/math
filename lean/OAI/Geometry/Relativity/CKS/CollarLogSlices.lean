import OAI.Geometry.Relativity.CKS.CollarThinInputs
import OAI.Geometry.Relativity.CKS.AngularCoefficientBounds

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev AMat := CKSAngularGeometry.Mat
abbrev MJ := CKSMixedGeometry.actualScalarJet
abbrev M3 := CKSMixedGeometry.actualThreeJet
abbrev AJ := CKSAngularGeometry.actualScalarJet
abbrev A3 := CKSAngularGeometry.actualThreeJet

structure LogCollarData where
  sigma : MP → AMat
  metricError : MP → AMat
  shift : MP → AP
  tError : MP → ℝ
  LError : MP → ℝ
  massError : MP → ℝ
  fstar : MP → ℝ
  etaDivR : MP → AP
  tauDivR2 : MP → AMat

def LogCollarData.angular (f : LogCollarData) (ρ : ℝ) : CKSAngularGeometry.CollarCoefficientFields where
  metric := ![fun y => f.sigma (slice ρ y),
    fun y => Real.exp ρ^3 • f.metricError (slice ρ y),
    fun y a b => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) (fun z => f.metricError z a b) (slice ρ y)]
  shift := fun y => Real.exp ρ^5 • f.shift (slice ρ y)
  scalar := ![fun y => Real.exp ρ^3*f.tError (slice ρ y),
    fun y => f.fstar (slice ρ y)+f.massError (slice ρ y),
    fun y => Real.exp ρ^3*f.LError (slice ρ y),
    fun y => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) f.tError (slice ρ y),
    fun y => f.fstar (slice ρ y)]
  eta := fun y => Real.exp ρ^3 • f.etaDivR (slice ρ y)
  tau := fun y => Real.exp ρ^3 • f.tauDivR2 (slice ρ y)
  etar := fun y a => Real.exp ρ^3*(f.etaDivR (slice ρ y) a+
    D (CKSMixedGeometry.basis 0) (fun z => f.etaDivR z a) (slice ρ y))
  massRadial := fun y => Real.exp ρ*D (CKSMixedGeometry.basis 0) f.massError (slice ρ y)
  massGap := fun y => Real.exp ρ*f.massError (slice ρ y)

structure LogCollarData.RegularAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  metricError : ContDiffAt ℝ 3 f.metricError x
  shift : ContDiffAt ℝ 3 f.shift x
  tError : ContDiffAt ℝ 2 f.tError x
  LError : ContDiffAt ℝ 2 f.LError x
  massError : ContDiffAt ℝ 2 f.massError x
  fstar : ContDiffAt ℝ 2 f.fstar x
  etaDivR : ContDiffAt ℝ 2 f.etaDivR x
  tauDivR2 : ContDiffAt ℝ 2 f.tauDivR2 x

structure LogCollarData.BoundedAt (f : LogCollarData) (B : ℝ) (x : MP) : Prop where
  sigma : ∀ a b, ‖M3 (fun y => f.sigma y a b) x‖ ≤ B
  metricError : ∀ a b, ‖M3 (fun y => f.metricError y a b) x‖ ≤ B/Real.exp (x 0)^3
  shift : ∀ a, ‖M3 (fun y => f.shift y a) x‖ ≤ B/Real.exp (x 0)^5
  tError : ‖MJ f.tError x‖ ≤ B/Real.exp (x 0)^3
  LError : ‖MJ f.LError x‖ ≤ B/Real.exp (x 0)^3
  massError : ‖MJ f.massError x‖ ≤ B/Real.exp (x 0)
  fstar : ‖MJ f.fstar x‖ ≤ B
  etaDivR : ∀ a, ‖MJ (fun y => f.etaDivR y a) x‖ ≤ B/Real.exp (x 0)^3
  tauDivR2 : ∀ a b, ‖MJ (fun y => f.tauDivR2 y a b) x‖ ≤ B/Real.exp (x 0)^3

theorem angular_thin_bounded {f : LogCollarData} {ρ B : ℝ} {x : AP}
    (hB : 0 ≤ B) (hr : 1 ≤ Real.exp ρ) (hf : f.RegularAt (slice ρ x))
    (hb : f.BoundedAt B (slice ρ x)) : (f.angular ρ).ThinBoundedAt (2*B) x := by
  have hB2 : B ≤ 2*B := by linarith
  have hc (n : ℕ) : ContDiffAt ℝ n (slice ρ) x :=
    (slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hmc (a b : A) := CKSMixedGeometry.component_diff hf.metricError a b
  have hsg (a b : A) := CKSMixedGeometry.component_diff hf.sigma a b
  have hme (a b : A) : ‖M3 (fun z => f.metricError z a b) (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by
    simpa only [slice_zero] using hb.metricError a b
  have htv : ‖MJ f.tError (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by simpa only [slice_zero] using hb.tError
  have hlv : ‖MJ f.LError (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by simpa only [slice_zero] using hb.LError
  have hmv : ‖MJ f.massError (slice ρ x)‖ ≤ B/Real.exp ρ := by simpa only [slice_zero] using hb.massError
  have hev (a : A) : ‖MJ (fun z => f.etaDivR z a) (slice ρ x)‖ ≤ B/Real.exp ρ^3 := by
    simpa only [slice_zero] using hb.etaDivR a
  unfold CKSAngularGeometry.CollarCoefficientFields.ThinBoundedAt
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    fin_cases i
    · exact ((angular_threejet_le_mixed ρ (hsg a b)).trans (hb.sigma a b)).trans hB2
    · exact (normalized_angular_three 3 (hmc a b) (hme a b)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    exact (normalized_angular_radial_two 3 (hmc a b) (hme a b)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (normalized_angular_three 5 (contDiffAt_pi.mp hf.shift a) ?_).trans hB2
    simpa only [slice_zero] using hb.shift a
  · intro i hi
    fin_cases i
    · exact (normalized_angular_two 3 hf.tError htv).trans hB2
    · change ‖AJ (fun y => f.fstar (slice ρ y)+f.massError (slice ρ y)) x‖ ≤ _
      have hfs : ContDiffAt ℝ 2 (fun y => f.fstar (slice ρ y)) x := hf.fstar.comp x (hc 2)
      have hfm : ContDiffAt ℝ 2 (fun y => f.massError (slice ρ y)) x := hf.massError.comp x (hc 2)
      change ‖CKSAngularGeometry.actualScalarJet (fun y => f.fstar (slice ρ y)+f.massError (slice ρ y)) x‖ ≤ _
      rw [CKSAngularGeometry.actualScalarJet_add hfs hfm]
      have hm : ‖AJ (fun y => f.massError (slice ρ y)) x‖ ≤ B :=
        ((angular_twojet_le_mixed ρ hf.massError).trans hmv).trans (div_le_self hB hr)
      exact (norm_add_le _ _).trans (add_le_add ((angular_twojet_le_mixed ρ hf.fstar).trans hb.fstar) hm) |>.trans_eq (by ring)
    · exact (normalized_angular_two 3 hf.LError hlv).trans hB2
    · exact (hi rfl).elim
    · exact ((angular_twojet_le_mixed ρ hf.fstar).trans hb.fstar).trans hB2
  · exact (normalized_radial_value 3 htv).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    exact (normalized_angular_two 3 (contDiffAt_pi.mp hf.etaDivR a) (hev a)).trans hB2
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro b
    apply (normalized_angular_two 3 (CKSMixedGeometry.component_diff hf.tauDivR2 a b) ?_).trans hB2
    simpa only [slice_zero] using hb.tauDivR2 a b
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro a
    change |Real.exp ρ^3*(_+_)| ≤ _
    rw [mul_add]
    exact (abs_add_le _ _).trans ((add_le_add (normalized_value 3 (hev a))
      (normalized_radial_value 3 (hev a))).trans_eq (by ring))
  · simpa only [LogCollarData.angular,pow_one] using (normalized_radial_value 1 (by simpa only [pow_one] using hmv)).trans hB2
  · simpa only [LogCollarData.angular,pow_one] using (normalized_value 1 (by simpa only [pow_one] using hmv)).trans hB2

end
end CKSAngularSlice

end

end OAI
