import OAI.NumberTheory.DukePrimeDegree.Geometry.MatrixLogLength
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootUniformContraction
import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationMatrixCoordinates

namespace OAI

/-! # Exponential root contraction in logarithmic matrix length -/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.Operator Topology BigOperators NNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma inverse_displacement_le_twice {d : ℕ} (g : G (d+1))
    (hg : ‖g.val-1‖ ≤ 1/2) : ‖(g⁻¹).val-1‖ ≤ 2*‖g.val-1‖ := by
  have he : (g⁻¹).val*g.val=1 := congrArg Subtype.val (inv_mul_cancel g)
  have hid : (g⁻¹).val-1 = -((g⁻¹).val*(g.val-1)) := by
    rw [mul_sub,he,mul_one]
    abel
  have hnorm : ‖(g⁻¹).val-1‖ ≤ ‖(g⁻¹).val‖*‖g.val-1‖ := by
    rw [hid,norm_neg]
    exact norm_mul_le _ _
  have hi : ‖(g⁻¹).val‖ ≤ ‖(g⁻¹).val-1‖+1 := by
    simpa only [sub_add_cancel,norm_one] using norm_add_le ((g⁻¹).val-1) 1
  have hb := mul_le_mul_of_nonneg_right hi (norm_nonneg (g.val-1))
  nlinarith [norm_nonneg ((g⁻¹).val-1)]

lemma matrixLogLength_le_three_displacement {d : ℕ} (g : G (d+1))
    (hg : ‖g.val-1‖ ≤ 1/2) : matrixLogLength g ≤ 3*‖g.val-1‖ := by
  have h₁ := matrixLogLength_le_displacements g
  have h₂ := inverse_displacement_le_twice g hg
  linarith

lemma matrix_opNorm_le_card_mul_entryBound {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i j, |M i j| ≤ C) : ‖M‖ ≤ (n:ℝ)*C := by
  let c : ℝ≥0 := ⟨C,hC⟩
  have H : ‖M‖₊ ≤ (n:ℝ≥0)*c := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc
      ∑ j, ‖M i j‖₊ ≤ ∑ _j : Fin n, c := by
        apply Finset.sum_le_sum
        intro j _
        exact_mod_cast hM i j
      _ = (n:ℝ≥0)*c := by simp
  exact_mod_cast H

lemma upperRoot_displacement_le_size (n : ℕ) (t : UpperRootTime n) :
    ‖((completeRootChain n).word t).val-1‖ ≤ (n:ℝ)*upperRootSize n t := by
  apply matrix_opNorm_le_card_mul_entryBound _ (norm_nonneg _)
  intro i j
  by_cases hij : i < j
  · let p : allPositiveRoots n := ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
    have H := norm_le_pi_norm (upperRootEuclideanCoordinates n t) p
    rw [Matrix.sub_apply,Matrix.one_apply,ite_eq_right (ne_of_lt hij),sub_zero]
    have he := upperRootEuclideanCoordinates_entry n t p
    change ((completeRootChain n).word t).val i j = upperRootEuclideanCoordinates n t p at he
    rw [he]
    simpa only [Real.norm_eq_abs,upperRootSize] using H
  · have H := positiveRootGeneratedGroup_pattern (allPositiveRoots n) (allPositiveRoots_closed n)
      (upperRootWord_mem n t) i j (by simpa only [allPositiveRoots,Finset.mem_filter,Finset.mem_univ,true_and] using hij)
    rw [Matrix.sub_apply,H,sub_self,abs_zero]
    exact norm_nonneg _

theorem upperRoot_logLength_contraction {d : ℕ}
    (ell : Fin (d+1) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    {R : ℝ} (hR : 0 < R) (hsmall : 3*(d+1:ℝ)*R ≤ 1)
    {r : ℝ} (hr : 0 ≤ r) {t : UpperRootTime (d+1)}
    (ht : t ∈ (completeRootChain (d+1)).cube R) :
    matrixLogLength ((completeRootChain (d+1)).word
      ((completeRootChain (d+1)).rootDilation ell r t)) ≤ Real.exp (-ε*r) := by
  let w := (completeRootChain (d+1)).word ((completeRootChain (d+1)).rootDilation ell r t)
  have hs : upperRootSize (d+1) t ≤ R := ((mem_upperRootCube_iff_size_lt (d+1) hR t).mp ht).le
  have hscale := upperRootSize_dilation_le (d+1) ell ε r hgap hr t
  have hnorm : ‖w.val-1‖ ≤ (d+1:ℝ)*Real.exp (-ε*r)*R := by
    have H := upperRoot_displacement_le_size (d+1)
      ((completeRootChain (d+1)).rootDilation ell r t)
    dsimp only [w]
    calc
      _ ≤ (d+1:ℝ)*upperRootSize (d+1) ((completeRootChain (d+1)).rootDilation ell r t) := by
        simpa only [Nat.cast_add,Nat.cast_one] using H
      _ ≤ (d+1:ℝ)*(Real.exp (-ε*r)*R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hscale.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
      _ = _ := by ring
  have he : Real.exp (-ε*r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hhalf : ‖w.val-1‖ ≤ 1/2 := by
    have hbound : (d+1:ℝ)*Real.exp (-ε*r)*R ≤ (d+1:ℝ)*R := by
      nlinarith [mul_nonneg (show 0 ≤ (d+1:ℝ) by positivity) hR.le]
    linarith
  have H := matrixLogLength_le_three_displacement w hhalf
  have hlast : 3*((d+1:ℝ)*Real.exp (-ε*r)*R) ≤ Real.exp (-ε*r) := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (-ε*r)).le]
  exact H.trans ((mul_le_mul_of_nonneg_left hnorm (by norm_num)).trans hlast)

end DukePrimeDegree

end

end OAI
