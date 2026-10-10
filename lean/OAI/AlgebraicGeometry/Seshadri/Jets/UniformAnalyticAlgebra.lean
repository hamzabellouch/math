import Mathlib

namespace OAI


                                                
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem exists_uniform_analytic_neighborhood
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ))
    (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ p ∈ U, ∀ a, AnalyticAt ℂ (fun z => q (p+z) a) 0 := by
  classical
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := ℂ) (A := A)
  let U : Set (ℂ × ℂ) := ⋂ a ∈ s, {p | AnalyticAt ℂ (fun z => q z a) p}
  have hU : IsOpen U := isOpen_biInter_finset fun a ha => isOpen_analyticAt ℂ _
  have h0 : (0 : ℂ × ℂ) ∈ U := by simp only [U, Set.mem_iInter]; exact fun a ha => hq a
  refine ⟨U,hU,h0,?_⟩
  intro p hp a
  have hall : AnalyticAt ℂ (fun z => q z a) p := by
    have ha : a ∈ Algebra.adjoin ℂ (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp a) ha)
    | algebraMap c =>
      convert (analyticAt_const (𝕜 := ℂ) (v := c) (x := p)) using 1
      funext z
      exact (q z).commutes c
    | add a b ha hb ia ib =>
      convert ia.add ib using 1
      funext z
      exact map_add (q z) a b
    | mul a b ha hb ia ib =>
      have he : (fun z => q z (a*b)) = (fun z => q z a * q z b) :=
        funext fun z => map_mul (q z) a b
      rw [he]
      exact ia.mul ib
  have hh : AnalyticAt ℂ (fun z : ℂ × ℂ => p+z) 0 := analyticAt_const.add analyticAt_id
  have hall' : AnalyticAt ℂ (fun z => q z a) (p+0) := by simpa using hall
  exact hall'.comp hh
end
end MaximalSeshadri.AnalyticCoordinates

end



end OAI
