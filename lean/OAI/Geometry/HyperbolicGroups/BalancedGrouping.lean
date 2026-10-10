import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Group blocks of size at most half into two groups of size at most two
thirds. The total may be less than n because removed vertices are absent. -/
theorem balanced_grouping (w : I → ℕ) (n : ℕ) (htotal : ∑ i, w i ≤ n)
    (hblock : ∀ i, 2*w i ≤ n) :
    ∃ A : Finset I, 3*(∑ i ∈ A, w i) ≤ 2*n ∧ 3*(∑ i ∈ Aᶜ, w i) ≤ 2*n := by
  classical
  by_cases hsmall : 3*(∑ i, w i) ≤ 2*n
  · exact ⟨∅,by simp,by simpa using hsmall⟩
  by_cases hlarge : ∃ i, n ≤ 3*w i
  · obtain ⟨i,hi⟩ := hlarge
    refine ⟨{i},?_,?_⟩
    · simp only [Finset.sum_singleton]
      have hh := hblock i
      omega
    · have hs := Finset.sum_add_sum_compl ({i} : Finset I) w
      simp only [Finset.sum_singleton] at hs
      omega
  push Not at hlarge
  let P := (Finset.univ : Finset I).powerset.filter (fun A => n ≤ 3*(∑ i ∈ A, w i))
  have hP : P.Nonempty := ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),by omega⟩⟩
  obtain ⟨A,hAP,hmin⟩ := Finset.exists_min_image P Finset.card hP
  have hAn := (Finset.mem_filter.mp hAP).2
  have hAne : A.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,Finset.sum_empty,mul_zero] at hAn
    omega
  obtain ⟨a,ha⟩ := hAne
  have hremove : 3*(∑ i ∈ A.erase a, w i) < n := by
    by_contra h
    have hm := hmin (A.erase a) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),by omega⟩)
    have hcard := Finset.card_erase_lt_of_mem ha
    omega
  have hs : w a + ∑ i ∈ A.erase a, w i = ∑ i ∈ A, w i := Finset.add_sum_erase A w ha
  have ha' := hlarge a
  have hcompl := Finset.sum_add_sum_compl A w
  exact ⟨A,by omega,by omega⟩

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
