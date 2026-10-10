import OAI.Geometry.Relativity.CKS.AngularSlice

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalized_angular_two {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 2 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualScalarJet (fun y => Real.exp ρ^n*f (slice ρ y)) x‖ ≤ B := by
  have hd : ContDiffAt ℝ 2 (fun y => f (slice ρ y)) x :=
    hf.comp x ((slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [CKSAngularGeometry.actualScalarJet_smul _ hd,norm_smul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  calc
    _ ≤ Real.exp ρ^n*(B/Real.exp ρ^n) := mul_le_mul_of_nonneg_left
      ((angular_twojet_le_mixed ρ hf).trans hb) (by positivity)
    _ = B := by field_simp

lemma normalized_angular_three {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 3 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualThreeJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualThreeJet (fun y => Real.exp ρ^n*f (slice ρ y)) x‖ ≤ B := by
  have hd : ContDiffAt ℝ 3 (fun y => f (slice ρ y)) x :=
    hf.comp x ((slice_smooth ρ).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤)))
  rw [CKSAngularGeometry.actualThreeJet_smul _ hd,norm_smul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  calc
    _ ≤ Real.exp ρ^n*(B/Real.exp ρ^n) := mul_le_mul_of_nonneg_left
      ((angular_threejet_le_mixed ρ hf).trans hb) (by positivity)
    _ = B := by field_simp

lemma radial_value_le_jet (f : MP → ℝ) (x : MP) :
    |D (CKSMixedGeometry.basis 0) f x| ≤ ‖CKSMixedGeometry.actualScalarJet f x‖ := by
  change ‖(CKSMixedGeometry.actualScalarJet f x).2.1 0‖ ≤ _
  exact (norm_le_pi_norm _ 0).trans ((norm_fst_le _).trans (norm_snd_le _))

lemma normalized_radial_value {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    |Real.exp ρ^n*D (CKSMixedGeometry.basis 0) f (slice ρ x)| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  exact (mul_le_mul_of_nonneg_left ((radial_value_le_jet f _).trans hb) (by positivity)).trans_eq (by field_simp)

lemma normalized_value {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hb : ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    |Real.exp ρ^n*f (slice ρ x)| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos (Real.exp_pos ρ) n)]
  have hv : |f (slice ρ x)| ≤ ‖CKSMixedGeometry.actualScalarJet f (slice ρ x)‖ := by
    simpa only [CKSMixedGeometry.actualScalarJet,Prod.fst,Real.norm_eq_abs] using (norm_fst_le (CKSMixedGeometry.actualScalarJet f (slice ρ x)))
  exact (mul_le_mul_of_nonneg_left (hv.trans hb) (by positivity)).trans_eq (by field_simp)

lemma angular_radial_two_le_three {f : MP → ℝ} {ρ : ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice ρ x)) :
    ‖CKSAngularGeometry.actualScalarJet (fun y => D (CKSMixedGeometry.basis 0) f (slice ρ y)) x‖ ≤
      ‖CKSMixedGeometry.actualThreeJet f (slice ρ x)‖ := by
  have hd := contDiffAt_D hf (m:=2) (by norm_num) (CKSMixedGeometry.basis 0)
  exact (angular_twojet_le_mixed ρ hd).trans
    ((norm_le_pi_norm (CKSMixedGeometry.actualThreeJet f (slice ρ x)).2 0).trans (norm_snd_le _))

lemma normalized_angular_radial_two {f : MP → ℝ} {ρ B : ℝ} {x : AP} (n : ℕ)
    (hf : ContDiffAt ℝ 3 f (slice ρ x))
    (hb : ‖CKSMixedGeometry.actualThreeJet f (slice ρ x)‖ ≤ B/Real.exp ρ^n) :
    ‖CKSAngularGeometry.actualScalarJet
      (fun y => Real.exp ρ^n*D (CKSMixedGeometry.basis 0) f (slice ρ y)) x‖ ≤ B := by
  apply normalized_angular_two n (contDiffAt_D hf (m:=2) (by norm_num) _)
  exact ((norm_le_pi_norm (CKSMixedGeometry.actualThreeJet f (slice ρ x)).2 0).trans (norm_snd_le _)).trans hb

end
end CKSAngularSlice

end

end OAI
