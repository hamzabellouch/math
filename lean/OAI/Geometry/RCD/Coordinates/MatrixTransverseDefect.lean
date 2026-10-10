import OAI.Geometry.RCD.Harmonic.GramQuadraticDefect

namespace OAI

/-! # The same finite Gram defect controls the transverse derivative -/

open Finset
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem matrix_gram_row_defect {n : ℕ} (G : Fin n → Fin n → ℝ)
    (a : Euclidean n) (ha : ‖a‖=1) (i : Fin n) :
    |(∑ j, a j*G i j)-a i| ≤ matrixGramDefect G := by
  classical
  have hai (j : Fin n) : |a j| ≤ 1 := by
    simpa only [Real.norm_eq_abs,ha] using PiLp.norm_apply_le a j
  have hid : (∑ j, a j*(if i=j then (1:ℝ) else 0))=a i := by simp [mul_ite]
  have he : (∑ j, a j*G i j)-a i=
      ∑ j, a j*(G i j-(if i=j then 1 else 0)) := by
    simp only [mul_sub,sum_sub_distrib,hid]
  rw [he]
  calc
    _ ≤ ∑ j, |a j*(G i j-(if i=j then 1 else 0))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |G i j-(if i=j then 1 else 0)| := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hai j) (abs_nonneg _)).trans_eq (one_mul _)
    _ ≤ matrixGramDefect G := by
      exact single_le_sum (s := univ)
        (f := fun l => ∑ j, |G l j-(if l=j then 1 else 0)|)
        (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _)) (mem_univ i)

theorem matrix_transverse_defect {n : ℕ} (G : Fin n → Fin n → ℝ)
    (a z : Euclidean n) (ha : ‖a‖=1) {M : ℝ} (hz : ‖z‖ ≤ M) :
    |2*(∑ i, z i*(∑ j, a j*G i j))-
      2*⟪z,a⟫_ℝ * (∑ i, ∑ j, a i*a j*G i j)| ≤
        2*((n:ℝ)+1)*M*matrixGramDefect G := by
  classical
  let E := matrixGramDefect G
  let q := ∑ i, ∑ j, a i*a j*G i j
  have hE : 0 ≤ E := matrixGramDefect_nonneg G
  have hq : |q-1| ≤ E := by
    simpa only [q,ha,one_pow,mul_one] using matrix_gram_quadratic_defect G a
  have hw : |⟪z,a⟫_ℝ| ≤ M := by
    exact ((abs_real_inner_le_norm z a).trans_eq (by rw [ha,mul_one])).trans hz
  have hzi (i : Fin n) : |z i| ≤ M := by
    have hh : |z i|≤‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    exact hh.trans hz
  have hs : |∑ i, z i*((∑ j, a j*G i j)-a i)| ≤ (n:ℝ)*M*E := by
    calc
      _ ≤ ∑ i, |z i*((∑ j, a j*G i j)-a i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, M*E := by
        apply sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hzi i) (matrix_gram_row_defect G a ha i)
          (abs_nonneg _) ((norm_nonneg z).trans hz)
      _=_ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  have hid : (∑ i, z i*a i)=⟪z,a⟫_ℝ := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    apply sum_congr rfl
    intro i _
    ring
  have he : 2*(∑ i, z i*(∑ j, a j*G i j))-2*⟪z,a⟫_ℝ * q =
      2*((∑ i, z i*((∑ j, a j*G i j)-a i))-⟪z,a⟫_ℝ * (q-1)) := by
    simp only [mul_sub,sum_sub_distrib,hid]
    ring
  change |2*(∑ i, z i*(∑ j, a j*G i j))-2*⟪z,a⟫_ℝ * q| ≤ _
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*(|∑ i, z i*((∑ j, a j*G i j)-a i)|+|⟪z,a⟫_ℝ * (q-1)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2*((n:ℝ)*M*E+M*E) := by
      apply mul_le_mul_of_nonneg_left (add_le_add hs ?_) (by norm_num)
      rw [abs_mul]
      exact mul_le_mul hw hq (abs_nonneg _) ((norm_nonneg z).trans hz)
    _=_ := by ring

end RegularPointCoordinates

end

end OAI
