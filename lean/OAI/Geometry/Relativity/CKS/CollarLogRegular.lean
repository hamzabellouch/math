import OAI.Geometry.Relativity.CKS.CollarLogSlices

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angular_regular {f : LogCollarData} {ρ : ℝ} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (ht : ContDiffAt ℝ 3 f.tError (slice ρ x)) : (f.angular ρ).RegularAt x := by
  have hc (n : ℕ) : ContDiffAt ℝ n (slice ρ) x :=
    (slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
  have hs : ContDiffAt ℝ 3 (fun y => f.sigma (slice ρ y)) x := hf.sigma.comp x (hc 3)
  have hq : ContDiffAt ℝ 3 (fun y => Real.exp ρ^3 • f.metricError (slice ρ y)) x :=
    (hf.metricError.comp x (hc 3)).const_smul (Real.exp ρ^3)
  have hqr : ContDiffAt ℝ 2 (fun y a b => Real.exp ρ^3*
      D (CKSMixedGeometry.basis 0) (fun z => f.metricError z a b) (slice ρ y)) x := by
    apply contDiffAt_pi.mpr; intro a
    apply contDiffAt_pi.mpr; intro b
    simpa only [smul_eq_mul, Function.comp_apply] using
      ((contDiffAt_D (CKSMixedGeometry.component_diff hf.metricError a b)
      (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2)).const_smul (Real.exp ρ^3)
  refine ⟨⟨hs,hq,hqr⟩,?_,?_,?_,?_⟩
  · exact (hf.shift.comp x (hc 3)).const_smul (Real.exp ρ^5)
  · intro i
    fin_cases i
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.tError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.tError.comp x (hc 2))
    · exact (hf.fstar.comp x (hc 2)).add (hf.massError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*f.LError (slice ρ y)) x
      exact contDiffAt_const.mul (hf.LError.comp x (hc 2))
    · change ContDiffAt ℝ 2 (fun y => Real.exp ρ^3*D (CKSMixedGeometry.basis 0) f.tError (slice ρ y)) x
      exact contDiffAt_const.mul ((contDiffAt_D ht (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)).comp x (hc 2))
    · exact hf.fstar.comp x (hc 2)
  · exact (hf.etaDivR.comp x (hc 2)).const_smul (Real.exp ρ^3)
  · exact (hf.tauDivR2.comp x (hc 2)).const_smul (Real.exp ρ^3)

end
end CKSAngularSlice

end

end OAI
