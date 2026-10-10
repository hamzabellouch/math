import OAI.Analysis.GroupDeterminants.LampDenominators

namespace OAI

universe uH

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
variable {H : Type uH} [Group H]

lemma zmodTwo_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  exact (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) z hz

lemma binary_support_expansion (a : MonoidAlgebra (ZMod 2) H) (ha : a.coeff 1 = 1) :
    ∃ S : Finset H, 1 ∉ S ∧ a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1 := by
  classical
  have hm : 1 ∈ a.coeff.support := Finsupp.mem_support_iff.mpr (ha ▸ one_ne_zero)
  refine ⟨a.coeff.support.erase 1, Finset.notMem_erase _ _, ?_⟩
  calc
    a = ∑ s ∈ a.coeff.support, MonoidAlgebra.single s (a.coeff s) :=
      (MonoidAlgebra.sum_coeff_single a).symm
    _ = MonoidAlgebra.single 1 (a.coeff 1) +
        ∑ s ∈ a.coeff.support.erase 1, MonoidAlgebra.single s (a.coeff s) :=
      (Finset.add_sum_erase _ _ hm).symm
    _ = _ := by
      rw [ha, ← MonoidAlgebra.one_def]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      rw [zmodTwo_eq_one_of_ne_zero (a.coeff s)
        (Finsupp.mem_support_iff.mp (Finset.mem_of_mem_erase hs))]

lemma binary_coefficient_normalize (a : MonoidAlgebra (ZMod 2) H) (ha : a ≠ 0) :
    ∃ h : H, ∃ S : Finset H, 1 ∉ S ∧
      MonoidAlgebra.single h⁻¹ 1 * a = 1 + ∑ s ∈ S, MonoidAlgebra.single s 1 := by
  classical
  obtain ⟨h, hh⟩ : ∃ h, a.coeff h ≠ 0 := by
    by_contra! hn
    apply ha
    ext h
    exact hn h
  have he : (MonoidAlgebra.single h⁻¹ 1 * a).coeff 1 = 1 := by
    rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff h (by simp [inv_mul_eq_one, eq_comm])]
    exact one_mul _ |>.trans (zmodTwo_eq_one_of_ne_zero _ hh)
  obtain ⟨S, hS, he⟩ := binary_support_expansion _ he
  exact ⟨h, S, hS, he⟩
end GroupRingDeterminant

end

end OAI
