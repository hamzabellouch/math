import OAI.Analysis.Laughlin.Asymptotics.LocalMetricLimit
import OAI.Analysis.Laughlin.Pair.EnergyReturn

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def truncatedModeFactor (L Q : ℕ) (i : Fin (Q+1)) : ℝ :=
  if i.val ≤ L then modeFactor Q i.val else 1

noncomputable def truncatedScaling (L Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (truncatedModeFactor L Q i : ℂ))

noncomputable def truncatedScalingInv (L Q : ℕ) : Space Q →ₐ[ℂ] Space Q :=
  exteriorScaling Q (fun i => (truncatedModeFactor L Q i : ℂ)⁻¹)

noncomputable def truncatedDiagonals (L Q : ℕ) (A : Finset (Fin (Q+1))) : ℝ :=
  ∏ i ∈ A, truncatedModeFactor L Q i

theorem truncatedModeFactor_pos (L Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) :
    0 < truncatedModeFactor L Q i := by
  unfold truncatedModeFactor
  split_ifs
  · exact modeFactor_pos Q hQ i
  · norm_num

theorem truncatedScaling_left_inverse (L Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    truncatedScalingInv L Q (truncatedScaling L Q x) = x := by
  apply exteriorScaling_inverse
  intro i
  exact_mod_cast ne_of_gt (truncatedModeFactor_pos L Q hQ i)

noncomputable def localOccupation (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) : Finset (Fin (L+1)) :=
  Finset.univ.filter (fun i => (⟨i.val,by omega⟩ : Fin (Q+1)) ∈ A)

theorem truncatedDiagonals_local (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    truncatedDiagonals L Q A = localDiagonals L Q (localOccupation L Q hL A) := by
  classical
  unfold truncatedDiagonals truncatedModeFactor localDiagonals
  rw [← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i hi => (⟨i.val,by have := i.isLt; omega⟩ : Fin (Q+1)))
  · intro i hi
    simp only [localOccupation,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact Finset.mem_filter.mpr ⟨hi,by change i.val ≤ L; have := i.isLt; omega⟩
  · intro i hi j hj he
    exact Fin.ext (congrArg (@Fin.val (Q+1)) he)
  · intro i hi
    obtain ⟨hiA,hiL⟩ := Finset.mem_filter.mp hi
    refine ⟨⟨i.val,by omega⟩,?_,?_⟩
    · simpa [localOccupation] using hiA
    · rfl
  · intro i hi
    rfl

theorem truncatedScalingInv_coordinate (L Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (truncatedScalingInv L Q x) A =
      ((truncatedDiagonals L Q A)⁻¹ : ℝ) * (occupationBasis Q).repr x A := by
  rw [truncatedScalingInv,exteriorScaling_coordinate]
  simp [truncatedDiagonals,Finset.prod_inv_distrib,Complex.ofReal_prod]

theorem truncatedMetricError_bound (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    |((truncatedDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  rw [truncatedDiagonals_local L Q hL]
  exact localMetricError_bound L Q _

end Laughlin.Fock

end OAI
