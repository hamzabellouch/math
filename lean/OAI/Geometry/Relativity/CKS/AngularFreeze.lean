import OAI.Geometry.Relativity.CKS.InducedSphereCalculus

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix)
open scoped Topology ContDiff

lemma D_line {F : Point → ℝ} {x : Point} (hF : DifferentiableAt ℝ F x) (v : Point) :
    D v F x = deriv (fun s : ℝ => F (x + s • v)) 0 := by
  have hd : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x using 1
    simp
  have hf : HasFDerivAt F (fderiv ℝ F x) (x + (0:ℝ) • v) := by simpa using hF.hasFDerivAt
  have hh := hf.comp_hasDerivAt 0 hd
  simpa only [zero_smul,add_zero,D,Function.comp_def] using hh.deriv.symm

lemma D_line_congr {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (v : Point)
    (he : ∀ s : ℝ, F (x+s•v) = G (x+s•v)) : D v F x = D v G x := by
  rw [D_line hF,D_line hG]
  congr 1
  funext s
  exact he s

lemma angular_line_radial (x : Point) (k : Ix) (hk : k ≠ 0) (s : ℝ) :
    (x+s•basis k) 0 = x 0 := by
  simp [basis,Ne.symm hk]

lemma angular_first_congr_leaf {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (he : ∀ y : Point, y 0 = x 0 → F y = G y) (k : Ix) (hk : k ≠ 0) :
    D (basis k) F x = D (basis k) G x := by
  apply D_line_congr hF hG
  intro s
  exact he _ (angular_line_radial x k hk s)

lemma angular_second_congr_leaf {F G : Point → ℝ} {x : Point}
    (hF : ∀ y : Point, y 0 = x 0 → ContDiffAt ℝ 2 F y)
    (hG : ∀ y : Point, y 0 = x 0 → ContDiffAt ℝ 2 G y)
    (he : ∀ y : Point, y 0 = x 0 → F y = G y)
    (i j : Ix) (hi : i ≠ 0) (hj : j ≠ 0) :
    D (basis j) (D (basis i) F) x = D (basis j) (D (basis i) G) x := by
  have hFd := (CKSCalculus.contDiffAt_D (hF x rfl) (m := 1) (by norm_num) (basis i)).differentiableAt (by norm_num)
  have hGd := (CKSCalculus.contDiffAt_D (hG x rfl) (m := 1) (by norm_num) (basis i)).differentiableAt (by norm_num)
  apply D_line_congr hFd hGd
  intro s
  have hy := angular_line_radial x j hj s
  apply angular_first_congr_leaf ((hF _ hy).differentiableAt (by norm_num))
    ((hG _ hy).differentiableAt (by norm_num)) _ i hi
  intro z hz
  exact he z (hz.trans hy)

end
end CKSSphericalChart

end

end OAI
