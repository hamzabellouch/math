import OAI.Geometry.Relativity.CKS.AngularCurvature

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma actualJet_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    actualJet (fun y => q y+p y) x = actualJet q x+actualJet p x := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a i k
    exact D_add _ ((component_diff hq i k).differentiableAt (by norm_num))
      ((component_diff hp i k).differentiableAt (by norm_num))
  · ext a b i k
    have he : (fun y => D (basis b) (fun z => q z i k+p z i k) y) =ᶠ[𝓝 x]
        (fun y => D (basis b) (fun z => q z i k) y+D (basis b) (fun z => p z i k) y) := by
      filter_upwards [hq.eventually (by norm_num),hp.eventually (by norm_num)] with y hqy hpy
      exact D_add _ ((component_diff hqy i k).differentiableAt (by norm_num))
        ((component_diff hpy i k).differentiableAt (by norm_num))
    change D (basis a) (fun y => D (basis b) (fun z => q z i k+p z i k) y) x = _
    unfold D at he ⊢
    rw [he.fderiv_eq]
    change D (basis a) (fun y => D (basis b) (fun z => q z i k) y+
      D (basis b) (fun z => p z i k) y) x = _
    exact D_add _ (first_diff hq b i k) (first_diff hp b i k)

lemma actualJet_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    actualJet (fun y => c • q y) x = c • actualJet q x := by
  have hm (e : Point) {f : Point → ℝ} {y : Point} (hf : DifferentiableAt ℝ f y) :
      D e (fun z => c*f z) y = c*D e f y := by
    rw [D_mul _ (differentiableAt_const _) hf,D_const]
    ring
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a i k
    exact hm _ ((component_diff hq i k).differentiableAt (by norm_num))
  · ext a b i k
    have he : (fun y => D (basis b) (fun z => c*q z i k) y) =ᶠ[𝓝 x]
        (fun y => c*D (basis b) (fun z => q z i k) y) := by
      filter_upwards [hq.eventually (by norm_num)] with y hqy
      exact hm _ ((component_diff hqy i k).differentiableAt (by norm_num))
    change D (basis a) (fun y => D (basis b) (fun z => c*q z i k) y) x = _
    unfold D at he ⊢
    rw [he.fderiv_eq]
    exact hm _ (first_diff hq b i k)

def interpolate (e : ℝ) (q σ : Point → Mat) : Point → Mat := fun x => (1-e) • q x+e • σ x

lemma actualJet_interpolate (e : ℝ) {q σ : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hσ : ContDiffAt ℝ 2 σ x) :
    actualJet (interpolate e q σ) x = (1-e) • actualJet q x+e • actualJet σ x := by
  unfold interpolate
  rw [actualJet_add (hq.const_smul (1-e)) (hσ.const_smul e),
    actualJet_smul _ hq,actualJet_smul _ hσ]

lemma interpolation_weight {e w A r : ℝ} (he : 0 ≤ e) (hew : e ≤ w)
    (hA : 0 ≤ A) (hr : 0 < r) {q σ : Jet} (hq : ‖q-σ‖ ≤ A/r^3) :
    ‖((1-e) • q+e • σ)-q‖ ≤ A*w/r^3 := by
  have hid : ((1-e) • q+e • σ)-q = -e • (q-σ) := by module
  rw [hid,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg he]
  calc
    e*‖q-σ‖ ≤ e*(A/r^3) := mul_le_mul_of_nonneg_left hq he
    _ ≤ w*(A/r^3) := mul_le_mul_of_nonneg_right hew (div_nonneg hA (pow_nonneg hr.le _))
    _ = _ := by ring

lemma interpolation_reference {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) {q σ : Jet} :
    ‖((1-e) • q+e • σ)-σ‖ ≤ ‖q-σ‖ := by
  have hid : ((1-e) • q+e • σ)-σ = (1-e) • (q-σ) := by module
  rw [hid,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

def cksLeaf (r : ℝ) (σ m remainder : Point → Mat) : Point → Mat :=
  fun x => r^2 • σ x+(1/r) • m x+remainder x

lemma normalized_cksLeaf (r : ℝ) (hr : r ≠ 0) (σ m remainder : Point → Mat) :
    (fun x => (1/r^2) • cksLeaf r σ m remainder x) =
      (fun x => σ x+(1/r^3) • m x+(1/r^2) • remainder x) := by
  ext x i k
  simp only [cksLeaf,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp

lemma cks_normalized_jet_bound {r A B : ℝ} (hr : 1 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {σ m remainder : Point → Mat} {x : Point}
    (hσ : ContDiffAt ℝ 2 σ x) (hm : ContDiffAt ℝ 2 m x) (hrem : ContDiffAt ℝ 2 remainder x)
    (hmB : ‖actualJet m x‖ ≤ B) (hremB : ‖actualJet remainder x‖ ≤ A/r^2) :
    ‖actualJet (fun y => (1/r^2) • cksLeaf r σ m remainder y) x-actualJet σ x‖ ≤ (A+B)/r^3 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [normalized_cksLeaf r hr0.ne',actualJet_add (hσ.add (hm.const_smul (1/r^3))) (hrem.const_smul (1/r^2)),
    actualJet_add hσ (hm.const_smul (1/r^3)),actualJet_smul _ hm,actualJet_smul _ hrem]
  have hid : actualJet σ x+(1/r^3) • actualJet m x+(1/r^2) • actualJet remainder x-actualJet σ x =
      (1/r^3) • actualJet m x+(1/r^2) • actualJet remainder x := by abel
  rw [hid]
  calc
    _ ≤ ‖(1/r^3) • actualJet m x‖+‖(1/r^2) • actualJet remainder x‖ := norm_add_le _ _
    _ = (1/r^3)*‖actualJet m x‖+(1/r^2)*‖actualJet remainder x‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (pow_pos hr0 _)),abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hr0))]
    _ ≤ (1/r^3)*B+(1/r^2)*(A/r^2) := add_le_add
      (by simpa only [mul_comm] using mul_le_mul hmB (le_refl (1/r^3)) (by positivity) hB)
      (mul_le_mul_of_nonneg_left hremB (by positivity))
    _ ≤ (A+B)/r^3 := by
      have hi : 1/r ≤ 1 := (div_le_one hr0).mpr hr
      have hh := mul_le_mul_of_nonneg_left hi hA
      field_simp at hh ⊢
      nlinarith [sq_nonneg r, mul_nonneg hA (sub_nonneg.mpr hr)]

end
end CKSAngularGeometry

end

end OAI
