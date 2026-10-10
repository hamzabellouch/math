import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.MatrixWirtinger

namespace OAI

/-! Holomorphic Direction. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma wderiv_direction_sum {α : Type*} (s : Finset α) (a : ℂ) (v : α → V n)
    (f : V n → ℂ) (z : V n) :
    wderiv a (∑ i ∈ s, v i) f z = ∑ i ∈ s, wderiv a (v i) f z := by
  simp only [wderiv,Finset.smul_sum,map_sum,Finset.mul_sum]
  rw [← Finset.sum_div,Finset.sum_add_distrib]

lemma dz_direction_smul (c : ℂ) (v : V n) (f : V n → ℂ) (z : V n) :
    dz (c • v) f z = c*dz v f z := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    ext j
    change c*v j = (c.re:ℂ)*v j+(c.im:ℂ)*(Complex.I*v j)
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hi : Complex.I • (c • v) = -c.im • v + c.re • (Complex.I • v) := by
    ext j
    change Complex.I*(c*v j) = ((-c.im:ℝ):ℂ)*v j+(c.re:ℂ)*(Complex.I*v j)
    conv_lhs => rw [← Complex.re_add_im c]
    simp only [Complex.ofReal_neg]
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold dz wderiv
  rw [hi,he]
  simp only [map_add,map_smul,Complex.real_smul,Complex.ofReal_neg]
  conv_rhs => arg 1; rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma dz_direction_coordinates (v : V n) (f : V n → ℂ) (z : V n) :
    dz v f z = ∑ i, v i*dz (e i) f z := by
  have he : v = ∑ i, v i • e i := by ext j; simp [e,Pi.single_apply]
  calc
    _ = dz (∑ i, v i • e i) f z := congrArg (fun u => dz u f z) he
    _ = _ := by
      unfold dz
      rw [wderiv_direction_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact dz_direction_smul (v i) (e i) f z

lemma mderiv_hol_coordinates (v : V n) (M : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) :
    mderiv (-Complex.I) v M z = ∑ i, v i • mderiv (-Complex.I) (e i) M z := by
  ext a b
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mderiv,dz] using dz_direction_coordinates v (fun y => M y a b) z
end KaehlerCalculus

end
end

end OAI
