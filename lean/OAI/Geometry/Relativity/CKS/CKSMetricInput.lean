import OAI.Geometry.Relativity.CKS.MatrixThreeJets
import OAI.Geometry.Relativity.CKS.CollarAngularMetric

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixThreeJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) :
    matrixThreeJets (fun y => c • q y) x = c • matrixThreeJets q x := by
  funext i k
  exact actualThreeJet_smul c (component_three hq i k)

lemma matrixThreeJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hp : ContDiffAt ℝ 3 p x) :
    matrixThreeJets (fun y => q y+p y) x = matrixThreeJets q x+matrixThreeJets p x := by
  funext i k
  exact actualThreeJet_add (component_three hq i k) (component_three hp i k)

lemma cks_normalized_three_bound {r A B : ℝ} (hr : 1 ≤ r) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    {σ m remainder : Point → Mat} {x : Point}
    (hσ : ContDiffAt ℝ 3 σ x) (hm : ContDiffAt ℝ 3 m x) (hrem : ContDiffAt ℝ 3 remainder x)
    (hmB : ‖matrixThreeJets m x‖ ≤ B) (hremB : ‖matrixThreeJets remainder x‖ ≤ A/r^2) :
    ‖matrixThreeJets (fun y => (1/r^2) • cksLeaf r σ m remainder y) x-matrixThreeJets σ x‖ ≤ (A+B)/r^3 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [normalized_cksLeaf r hr0.ne',matrixThreeJets_add (hσ.add (hm.const_smul (1/r^3))) (hrem.const_smul (1/r^2)),
    matrixThreeJets_add hσ (hm.const_smul (1/r^3)),matrixThreeJets_smul _ hm,matrixThreeJets_smul _ hrem]
  have hid : matrixThreeJets σ x+(1/r^3) • matrixThreeJets m x+(1/r^2) • matrixThreeJets remainder x-matrixThreeJets σ x =
      (1/r^3) • matrixThreeJets m x+(1/r^2) • matrixThreeJets remainder x := by abel
  rw [hid]
  calc
    _ ≤ ‖(1/r^3) • matrixThreeJets m x‖+‖(1/r^2) • matrixThreeJets remainder x‖ := norm_add_le _ _
    _ = (1/r^3)*‖matrixThreeJets m x‖+(1/r^2)*‖matrixThreeJets remainder x‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (pow_pos hr0 _)),abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hr0))]
    _ ≤ (1/r^3)*B+(1/r^2)*(A/r^2) := add_le_add
      (mul_le_mul_of_nonneg_left hmB (by positivity)) (mul_le_mul_of_nonneg_left hremB (by positivity))
    _ ≤ (A+B)/r^3 := by
      have hi : 1/r ≤ 1 := (div_le_one hr0).mpr hr
      have hh := mul_le_mul_of_nonneg_left hi hA
      field_simp at hh ⊢
      nlinarith [sq_nonneg r, mul_nonneg hA (sub_nonneg.mpr hr)]

lemma normalized_cks_radial_deriv {E : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (σ m : ℝ) (hE : DifferentiableAt ℝ E r) :
    r*deriv (fun ρ => σ+(1/ρ^3)*m+(1/ρ^2)*E ρ) r =
      (-3/r^3)*m+(-2/r^2)*E r+(1/r)*deriv E r := by
  have h3 := (hasDerivAt_const r (1:ℝ)).div ((hasDerivAt_id r).pow 3) (pow_ne_zero _ hr)
  have h2 := (hasDerivAt_const r (1:ℝ)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero _ hr)
  have hd := ((hasDerivAt_const r σ).add (h3.mul_const m)).add (h2.mul hE.hasDerivAt)
  have hid : HasDerivAt (fun ρ => σ+(1/ρ^3)*m+(1/ρ^2)*E ρ)
      ((-3/r^4)*m+(-2/r^3)*E r+(1/r^2)*deriv E r) r := by
    convert! hd using 1
    dsimp
    field_simp
    ring
  rw [hid.deriv]
  field_simp

def cksRadialField (r : ℝ) (m E dE : Point → Mat) : Point → Mat :=
  fun x => (-3/r^3) • m x+(-2/r^2) • E x+(1/r) • dE x

lemma matrixScalarJets_add {q p : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (hp : ContDiffAt ℝ 2 p x) :
    matrixScalarJets (fun y => q y+p y) x = matrixScalarJets q x+matrixScalarJets p x := by
  simpa using matrixScalarJets_linear 1 1 hq hp

lemma matrixScalarJets_smul (c : ℝ) {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) :
    matrixScalarJets (fun y => c • q y) x = c • matrixScalarJets q x := by
  funext i k
  exact actualScalarJet_smul c (component_diff hq i k)

lemma cks_radial_jet_bound {r A B : ℝ} (hr : 1 ≤ r) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    {m E dE : Point → Mat} {x : Point}
    (hm : ContDiffAt ℝ 2 m x) (hE : ContDiffAt ℝ 2 E x) (hdE : ContDiffAt ℝ 2 dE x)
    (hmB : ‖matrixScalarJets m x‖ ≤ B) (hEB : ‖matrixScalarJets E x‖ ≤ A/r^2)
    (hdEB : ‖matrixScalarJets dE x‖ ≤ A/r^3) :
    ‖matrixScalarJets (cksRadialField r m E dE) x‖ ≤ (3*A+3*B)/r^3 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  unfold cksRadialField
  rw [matrixScalarJets_add ((hm.const_smul (-3/r^3)).add (hE.const_smul (-2/r^2))) (hdE.const_smul (1/r)),
    matrixScalarJets_add (hm.const_smul (-3/r^3)) (hE.const_smul (-2/r^2)),
    matrixScalarJets_smul _ hm,matrixScalarJets_smul _ hE,matrixScalarJets_smul _ hdE]
  calc
    _ ≤ ‖(-3/r^3) • matrixScalarJets m x‖+‖(-2/r^2) • matrixScalarJets E x‖+
        ‖(1/r) • matrixScalarJets dE x‖ := norm_add₃_le
    _ = (3/r^3)*‖matrixScalarJets m x‖+(2/r^2)*‖matrixScalarJets E x‖+
        (1/r)*‖matrixScalarJets dE x‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hr0,
        abs_of_pos (pow_pos hr0 3),abs_of_pos (sq_pos_of_pos hr0)]
      norm_num
    _ ≤ (3/r^3)*B+(2/r^2)*(A/r^2)+(1/r)*(A/r^3) := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hmB (by positivity))
        (mul_le_mul_of_nonneg_left hEB (by positivity)))
      (mul_le_mul_of_nonneg_left hdEB (by positivity))
    _ ≤ (3*A+3*B)/r^3 := by
      have hh := mul_le_mul_of_nonneg_left hr hA
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg r)]

end
end CKSAngularGeometry

end

end OAI
