import OAI.Geometry.NodalSets.Coefficients.RealFiniteCoefficientL2Bound

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_compact_fintype_coefficient_L2_bound {n : ℕ} {I : Type*} [Fintype I] {K : Set (Coord n)}
    (hK : IsCompact K) (A : Coord n → I → ℝ) (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : I → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
      (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*(∑ j, ∫ x in K, (U j x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image (continuous_pi hA)).isBounded.exists_pos_norm_le
  refine ⟨((Fintype.card I:ℝ)+1)*B^2,by positivity,fun U hU ↦ ?_⟩
  have hprod (j : I) : MemLp (fun x ↦ A x j*U j x) 2 (volume.restrict K) := by
    obtain ⟨_,_,hbound⟩ := real_compact_multiplier_bound hK (fun x ↦ A x j) (hA j)
    exact (hbound (U j) (hU j)).1
  have hsum : MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) :=
    memLp_finsetSum Finset.univ (fun j _ ↦ hprod j)
  refine ⟨hsum,?_⟩
  have hisum := integrable_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq)
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq),← integral_const_mul]
  apply setIntegral_mono_on hsum.integrable_sq (hisum.const_mul _) hK.measurableSet
  intro x hx
  have hcoef (j : I) : (A x j)^2 ≤ B^2 := by
    have ht := (norm_le_pi_norm (A x) j).trans (hb _ ⟨x,hx,rfl⟩)
    rw [Real.norm_eq_abs] at ht
    nlinarith [sq_abs (A x j),abs_nonneg (A x j)]
  have hcoefsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcoef j)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hcoefsum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A x j) (fun j ↦ U j x)
  have hn : 0 ≤ ∑ j, (U j x)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcoefsum hn
  have hextra := mul_nonneg (sq_nonneg B) hn
  nlinarith only [hCS,hmul,hextra]

theorem real_compact_fintype_coefficient_common_bound {n : ℕ} {I : Type*} [Fintype I]
    {K : Set (Coord n)} (hK : IsCompact K) (A : Coord n → I → ℝ)
    (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : I → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      ∀ E : ℝ, 0 ≤ E → (∀ j, (∫ x in K, (U j x)^2) ≤ E) →
        MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
        (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*E := by
  obtain ⟨C,hC,hb⟩ := real_compact_fintype_coefficient_L2_bound hK A hA
  refine ⟨C*((Fintype.card I:ℝ)+1),by positivity,fun U hU E hE hbound ↦ ?_⟩
  have h := hb U hU
  refine ⟨h.1,h.2.trans ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hbound j)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hs' : (∑ j, ∫ x in K, (U j x)^2) ≤ ((Fintype.card I:ℝ)+1)*E := by nlinarith only [hs,hE]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs' hC.le

end
end Yau

end OAI
