import OAI.Analysis.BoundedHochschild.RepresentedAveragingAlgebra
import OAI.Analysis.BoundedHochschild.SubnormalizedOperatorRows

namespace OAI

/-! A finite subrow of an infinite normalized row is completed by the square
root of its positive defect. This completion does not assume a trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def rowDefect (m : I → M) (s : Finset I) : M :=
  CFC.sqrt (1 - ∑ i ∈ s, m i * star (m i))

lemma rowDefect_nonneg (m : I → M) (s : Finset I) : 0 ≤ rowDefect m s :=
  CFC.sqrt_nonneg _

lemma rowDefect_mul_star (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) :
    rowDefect m s * star (rowDefect m s) = 1 - ∑ i ∈ s, m i * star (m i) := by
  rw [(rowDefect_nonneg m s).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hs)

lemma rowDefect_norm_le (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) : ‖rowDefect m s‖ ≤ 1 := by
  have hd : ‖1 - ∑ i ∈ s, m i * star (m i)‖ ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hs)).mpr
    exact sub_le_self _ (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (m i))
  rw [← rowDefect_mul_star m s hs, CStarRing.norm_self_mul_star] at hd
  nlinarith [norm_nonneg (rowDefect m s)]

def completedRow (m : I → M) (s : Finset I) : Option s → M
  | none => rowDefect m s
  | some i => m i

lemma completedRow_normalized (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) :
    ∑ i, completedRow m s i * star (completedRow m s i) = 1 := by
  classical
  rw [Fintype.sum_option]
  change rowDefect m s * star (rowDefect m s) + ∑ i : s, m i * star (m i) = 1
  rw [rowDefect_mul_star m s hs, Finset.sum_coe_sort s (fun i => m i * star (m i))]
  exact sub_add_cancel _ _

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma completedRow_average (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (s : Finset I) (W : H →L[ℂ] K) :
    representedRightAverage π σ (completedRow m s) W =
      (π (rowDefect m s)).comp (W.comp (σ (rowDefect m s)).adjoint) +
      ∑ i ∈ s, (π (m i)).comp (W.comp (σ (m i)).adjoint) := by
  classical
  unfold representedRightAverage operatorRowAverage
  rw [Fintype.sum_option]
  change _ + (∑ i : s, (π (m i)).comp (W.comp (σ (m i)).adjoint)) = _
  rw [Finset.sum_coe_sort s (fun i => (π (m i)).comp (W.comp (σ (m i)).adjoint))]
  rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
