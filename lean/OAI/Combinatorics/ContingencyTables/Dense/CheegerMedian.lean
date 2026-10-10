import OAI.Combinatorics.ContingencyTables.Dense.CheegerCoarea

namespace OAI

/-! # A stationary weighted median on a finite chain -/
namespace ContingencyTables.CheegerProof
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section
variable {X : Type*} [Fintype X] (C : FiniteChain X)

theorem exists_median (f : X → ℝ) : ∃ a : ℝ,
    mass C (Finset.univ.filter fun x => f x < a) ≤ 1/2 ∧
    mass C (Finset.univ.filter fun x => a < f x) ≤ 1/2 := by
  have hne : (Finset.univ : Finset X).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := C.normalized
    rw [hz,Finset.sum_empty] at h
    norm_num at h
  let M := Finset.univ.filter fun x =>
    1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x)
  have hM : M.Nonempty := by
    obtain ⟨x,hx,hm⟩ := Finset.exists_max_image Finset.univ f hne
    have he : (Finset.univ.filter fun y => f y ≤ f x) = Finset.univ := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact iff_true_intro (hm y (Finset.mem_univ _))
    refine ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩⟩
    rw [he]
    simp only [mass,C.normalized]
    norm_num
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image M f hM
  have hxM : 1/2 ≤ mass C (Finset.univ.filter fun y => f y ≤ f x) :=
    (Finset.mem_filter.mp hx).2
  refine ⟨f x,?_,?_⟩
  · let L := Finset.univ.filter fun y => f y < f x
    change mass C L ≤ 1/2
    by_contra hn
    have hL : 1/2 < mass C L := lt_of_not_ge hn
    have hLn : L.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he] at hL
      norm_num [mass] at hL
    obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image L f hLn
    have hyx : f y < f x := (Finset.mem_filter.mp hy).2
    have he : (Finset.univ.filter fun z => f z ≤ f y) = L := by
      ext z
      simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun hz => hz.trans_lt hyx,fun hz => hymax z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)⟩
    have hyM : y ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [he]
      exact hL.le
    exact (not_lt_of_ge (hmin y hyM)) hyx
  · have he : (Finset.univ.filter fun y => f y ≤ f x)ᶜ =
        Finset.univ.filter (fun y => f x < f y) := by
      ext y
      simp
    have h := mass_compl C (Finset.univ.filter fun y => f y ≤ f x)
    rw [he] at h
    linarith

theorem variance_le_centered (f : X → ℝ) (a : ℝ) :
    C.variance f ≤ ∑ x, C.π x*(f x-a)^2 := by
  have he : (∑ x, C.π x*(f x-a)^2) = C.inner f f-2*a*C.mean f+a^2 := by
    calc
      _ = (∑ x, C.π x*f x*f x)-2*a*(∑ x,C.π x*f x)+a^2*(∑ x,C.π x) := by
        simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [C.normalized,mul_one]; rfl
  rw [C.variance_formula,he]
  nlinarith [sq_nonneg (C.mean f-a)]

end
end ContingencyTables.CheegerProof

end OAI
