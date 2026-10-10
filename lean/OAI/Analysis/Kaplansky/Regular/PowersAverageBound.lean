import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.PowersAverages

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

lemma averageConjugate_norm_eq {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    ‖averageConjugate h x‖ = (N:ℝ)⁻¹ * ‖∑ i, left (h i)*x.val*left (h i)⁻¹‖ := by
  change ‖(averageConjugate h x).val‖ = _
  rw [averageConjugate_val,norm_smul,norm_inv,Complex.norm_natCast]

lemma averageConjugate_mul {N : ℕ} (h : Fin N → G) (u : G) (x : Algebra G) :
    averageConjugate (fun i => h i*u) x = averageConjugate h (conjugateMap u x) := by
  rw [averageConjugate_apply,averageConjugate_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => conjugateMap_mul _ _ _)

lemma average_partition_bound {N : ℕ} (D : G → Prop) (h : Fin N → G)
    (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
    (x : Algebra G) (hT : mask D*x.val*mask D=0) :
    ‖averageConjugate h x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖) := by
  rw [averageConjugate_norm_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have he := powers_operator_estimate D h hd x.val hT
  rw [Fintype.card_fin] at he
  exact he

lemma average_conjugated_partition_bound {N : ℕ} (D : G → Prop) (h : Fin N → G)
    (hd : ∀ i j w, ¬D ((h i)⁻¹*w) → ¬D ((h j)⁻¹*w) → i=j)
    (u : G) (x : Algebra G) (hT : mask D*(conjugateMap u x).val*mask D=0) :
    ‖averageConjugate (fun i => h i*u) x‖ ≤ (N:ℝ)⁻¹*(2*Real.sqrt N*‖x‖) := by
  rw [averageConjugate_mul]
  apply (average_partition_bound D h hd (conjugateMap u x) hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_left (conjugateMap_norm_le _ _) (by positivity)

lemma average_approximation_bound {N : ℕ} (hN : 0<N) (h : Fin N → G)
    (x y : Algebra G) : ‖averageConjugate h x‖ ≤ ‖x-y‖+‖averageConjugate h y‖ := by
  have hax := averageConjugate_norm_le hN h (x-y)
  have hab := norm_add_le (averageConjugate h (x-y)) (averageConjugate h y)
  rw [map_sub,sub_add_cancel] at hab
  rw [map_sub] at hax
  linarith


end KaplanskyConsequences.Regular

end

end OAI
