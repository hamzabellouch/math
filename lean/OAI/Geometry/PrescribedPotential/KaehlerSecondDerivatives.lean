import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixLogDet
import OAI.Geometry.PrescribedPotential.WirtingerConjugate

namespace OAI

/-! Kaehler Second Derivatives. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma closed_mixed_symmetry {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hh : ∀ y ∈ U, (M y).IsHermitian)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    {z : V n} (hz : z ∈ U) (i j k l : Fin n) :
    dzbar (e k) (dz (e l) (fun y => M y i j)) z =
      dzbar (e i) (dz (e j) (fun y => M y k l)) z := by
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have he1 : dz (e l) (fun y => M y i j) =ᶠ[𝓝 z] dz (e j) (fun y => M y i l) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact closed_dz_symmetry hU hM hh hclosed hy i j l
  rw [show dzbar (e k) (dz (e l) (fun y => M y i j)) z =
    dzbar (e k) (dz (e j) (fun y => M y i l)) z from wderiv_congr he1 _ _]
  rw [show dzbar (e k) (dz (e j) (fun y => M y i l)) z =
    dz (e j) (dzbar (e k) (fun y => M y i l)) z from wderiv_comm (entry_smooth hs i l) _ _ _ _]
  have he2 : dzbar (e k) (fun y => M y i l) =ᶠ[𝓝 z] dzbar (e i) (fun y => M y k l) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact closed_dzbar_symmetry hU hM hh hclosed hy i l k
  rw [show dz (e j) (dzbar (e k) (fun y => M y i l)) z =
    dz (e j) (dzbar (e i) (fun y => M y k l)) z from wderiv_congr he2 _ _]
  exact wderiv_comm (entry_smooth hs k l) _ _ _ _

lemma closed_derivative_quadratic {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hh : ∀ y ∈ U, (M y).IsHermitian)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    {z : V n} (hz : z ∈ U) (i j : Fin n) :
    ∑ k, (mderiv Complex.I (e k) M z*mderiv (-Complex.I) (e k) M z) i j =
      (mderiv Complex.I (e i) M z*mderiv (-Complex.I) (e j) M z).trace := by
  classical
  simp only [Matrix.mul_apply,Matrix.trace,Matrix.diag_apply,mderiv]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change dzbar (e k) (fun y => M y i l) z * dz (e k) (fun y => M y l j) z =
    dzbar (e i) (fun y => M y k l) z * dz (e j) (fun y => M y l k) z
  rw [closed_dzbar_symmetry hU hM hh hclosed hz i l k,
    closed_dz_symmetry hU hM hh hclosed hz l j k]

lemma ricci_cancellation_at_one {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    {z : V n} (hz : z ∈ U) (hMz : M z = 1) :
    (∑ k, mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) M) z) =
      PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z +
        ∑ k, mderiv Complex.I (e k) M z*mderiv (-Complex.I) (e k) M z := by
  have hh : ∀ y ∈ U, (M y).IsHermitian := fun y hy => (hp y hy).isHermitian
  ext i j
  simp only [Matrix.sum_apply,Matrix.add_apply]
  rw [closed_derivative_quadratic hU hM hh hclosed hz i j]
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have hl : ContDiffAt ℝ ∞ (fun y => Real.log (M y).det.re) z :=
    (Complex.reCLM.contDiff.contDiffAt.comp z (determinant_smooth.contDiffAt.comp z hs)).log
      (ne_of_gt (Complex.pos_iff.mp (hp z hz).det_pos).1)
  rw [potentialMatrix_eq_dzbar_dz hl]
  have he := second_wderiv_logdet_at_one hU hM hp hz hMz (-Complex.I) Complex.I (e i) (e j)
  change dzbar (e i) (dz (e j) (fun y => (Real.log (M y).det.re : ℂ))) z = _ at he
  change ∑ k, dzbar (e k) (dz (e k) (fun y => M y i j)) z =
    dzbar (e i) (dz (e j) (fun y => (Real.log (M y).det.re : ℂ))) z + _
  rw [he,sub_add_cancel]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro k _
  exact closed_mixed_symmetry hU hM hh hclosed hz i j k k
end KaehlerCalculus

end
end

end OAI
