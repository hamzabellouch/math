import OAI.Analysis.Laughlin.Spin.Basis
import OAI.Analysis.Laughlin.Spin.GenericOrthogonality
import OAI.Analysis.Laughlin.Spin.Intertwining

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev GenericCoupledIndex (A B : ℕ) :=
  Σ z : Fin (min A B+1), Fin (genericCoupledWeight A B z.val+1)

noncomputable def genericCoupledBasis (A B : ℕ) :
    Matrix (SpinIndex A B) (GenericCoupledIndex A B) ℝ :=
  fun i s => genericUnitDescendant A B s.1.val (by have := s.1.isLt; omega)
    (by have := s.1.isLt; omega) s.2.val i

theorem genericCoupledIndex_card (A B : ℕ) :
    Fintype.card (GenericCoupledIndex A B) = Fintype.card (SpinIndex A B) := by
  have hr : (Fintype.card (GenericCoupledIndex A B) : ℝ) =
      (Fintype.card (SpinIndex A B) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (min A B+1)) :
        ((genericCoupledWeight A B z.val+1 : ℕ) : ℝ) = A+B+1-2*(z.val : ℝ) := by
      have hz := z.isLt
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z.val ≤ A+B)]
      push_cast
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rcases le_total A B with h | h
    · rw [Nat.min_eq_left h]; ring
    · rw [Nat.min_eq_right h]; ring
  exact_mod_cast hr

theorem genericCoupledBasis_isometry (A B : ℕ) :
    (genericCoupledBasis A B)ᵀ * genericCoupledBasis A B = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,genericCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      genericUnitDescendant_norm A B s.1.val s.2.val _ _ (by have := s.2.isLt; omega)
  · rw [ite_eq_right h]
    apply genericUnitDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      exact h (by have he : n=m := Fin.ext hnm; subst m; rfl)
    · left
      intro he
      exact hzw (Fin.ext he)

theorem genericCoupledBasis_complete (A B : ℕ) :
    genericCoupledBasis A B * (genericCoupledBasis A B)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := GenericCoupledIndex A B) (n := SpinIndex A B) (R := ℝ) (genericCoupledIndex_card A B)).mp
    (genericCoupledBasis_isometry A B)

theorem genericCoupledInclusion_isometry (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (genericCoupledInclusion A B z hA hB)ᵀ * genericCoupledInclusion A B z hA hB = 1 := by
  ext n m
  simp only [Matrix.mul_apply,Matrix.transpose_apply,genericCoupledInclusion,Matrix.one_apply]
  by_cases h : n=m
  · subst m
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using genericUnitDescendant_norm A B z n.val hA hB (by omega)
  · rw [ite_eq_right h]
    exact genericUnitDescendant_orthogonal A B z z n.val m.val hA hB hA hB
      (Or.inr (fun he => h (Fin.ext he)))

theorem physicalCoupledInclusion_isometry (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    (physicalCoupledInclusion A B z hA hB)ᴴ * physicalCoupledInclusion A B z hA hB = 1 := by
  have hs : star ((-1 : ℂ)^z) * (-1 : ℂ)^z = 1 := by
    simp only [star_pow,star_neg,star_one,← mul_pow]
    norm_num
  have hg : ((genericCoupledInclusion A B z hA hB).map Complex.ofReal)ᴴ *
      (genericCoupledInclusion A B z hA hB).map Complex.ofReal = 1 := by
    ext n m
    have h := congrArg Complex.ofReal
      (congrFun (congrFun (genericCoupledInclusion_isometry A B z hA hB) n) m)
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.conjTranspose_apply,
      Matrix.map_apply,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,
      Complex.ofReal_mul,Matrix.one_apply,apply_ite,Complex.ofReal_one,
      Complex.ofReal_zero] using h
  simp only [physicalCoupledInclusion,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,hg]
  simp only [star_pow,star_neg,star_one] at hs ⊢
  rw [hs,one_smul]

end Laughlin.Spin

end OAI
