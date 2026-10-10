import Mathlib

namespace OAI

noncomputable section
namespace CKSArea
noncomputable section
open Matrix
open scoped Matrix
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def density (g : Mat2) : ℝ := Real.sqrt g.det

lemma real_symmetric {n : Type*} {g : Matrix n n ℝ} (h : g.IsHermitian) (i j : n) :
    g j i = g i j := by
  simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun h i) j

lemma mixed_det_nonneg {g h : Mat2} (hg : g.PosDef) (hh : h.PosSemidef) :
    0 ≤ g 0 0*h 1 1+g 1 1*h 0 0-2*g 0 1*h 0 1 := by
  have ha : 0 < g 0 0 := hg.diag_pos
  have he : 0 ≤ h 0 0 := hh.diag_nonneg
  have hd : 0 < g 0 0*g 1 1-(g 0 1)^2 := by
    have hh' := hg.det_pos
    rw [Matrix.det_fin_two,real_symmetric hg.isHermitian 0 1] at hh'
    nlinarith
  have hp := hh.dotProduct_mulVec_nonneg ![-g 0 1,g 0 0]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, star_trivial,
    Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hp
  rw [real_symmetric hh.isHermitian 0 1] at hp
  have hn : 0 ≤ g 0 0*(g 0 0*h 1 1+g 1 1*h 0 0-2*g 0 1*h 0 1) := by
    nlinarith [mul_nonneg hd.le he]
  exact nonneg_of_mul_nonneg_right hn ha

lemma det_lower_bound {g p : Mat2} {c : ℝ} (hg : g.PosDef) (hc : 0 ≤ c)
    (h : (p-c • g).PosSemidef) : c^2*g.det ≤ p.det := by
  let e := p-c • g
  have he : e.PosSemidef := h
  have hp : p = c • g+e := by dsimp [e]; abel
  have hmix := mixed_det_nonneg hg he
  have hedet : 0 ≤ e.det := he.det_nonneg
  have hg10 := real_symmetric hg.isHermitian 0 1
  have he10 := real_symmetric he.isHermitian 0 1
  rw [hp,Matrix.det_fin_two,Matrix.det_fin_two]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  rw [hg10,he10]
  rw [Matrix.det_fin_two,he10] at hedet
  nlinarith [mul_nonneg hc hmix]

theorem density_lower_bound {g p : Mat2} {c : ℝ} (hg : g.PosDef) (hc : 0 ≤ c)
    (h : (p-c • g).PosSemidef) : c*density g ≤ density p := by
  have hh := Real.sqrt_le_sqrt (det_lower_bound hg hc h)
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs,abs_of_nonneg hc] at hh
  exact hh

end
end CKSArea

end

end OAI
