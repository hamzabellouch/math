import Mathlib
import OAI.RepresentationTheory.PartialPermutation.SymmetricTransfer
import OAI.RepresentationTheory.PartialPermutation.TableauLimits
import OAI.RepresentationTheory.PartialPermutation.SpechtClassification

namespace OAI

namespace PartialPermutation
noncomputable section
open scoped Classical

lemma symmetricInverseDegreeSum_le_tableaux (n : ℕ) (u : ℝ) (hu : 0 < u) :
    symmetricInverseDegreeSum n u ≤ TableauZeta.fullSum n u := by
  have he : symmetricInverseDegreeSum n u =
      ∑ μ : DiagramCounting.Shape n, (irreducibleDegree (SpechtActual.index μ):ℝ)^(-u) := by
    exact (Fintype.sum_equiv (SpechtActual.indexEquiv n) _ _ (fun _ => rfl)).symm
  rw [he]
  apply Finset.sum_le_sum
  intro μ _
  exact Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast Tableau.standardCount_pos μ.1)
    (by exact_mod_cast SpechtActual.standardCount_le_degree μ) (neg_nonpos.mpr hu.le)

theorem symmetricReciprocalDegreeBounded : SymmetricReciprocalDegreeBoundedStatement := by
  intro u hu
  obtain ⟨a,ha⟩ := TableauZeta.fullSum_bddAbove u hu
  refine ⟨a,?_⟩
  rintro x ⟨n,_,rfl⟩
  exact (symmetricInverseDegreeSum_le_tableaux n u hu).trans (ha (Set.mem_range_self n))

lemma symmetricInverseDegreeSum_le_constant {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    symmetricInverseDegreeSum n u ≤ symmetricDegreeConstant u := by
  exact le_csSup (symmetricReciprocalDegreeBounded u hu) ⟨n,hn,rfl⟩

lemma symmetricDegreeConstant_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ symmetricDegreeConstant u :=
  (inverseDegreeSum_nonneg (Equiv.Perm (Fin 1)) u).trans
    (symmetricInverseDegreeSum_le_constant (n := 1) le_rfl hu)

end
end PartialPermutation

end OAI
