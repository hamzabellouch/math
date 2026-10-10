import OAI.NumberTheory.Ostmann.Construction.RepeatedLocal

namespace OAI

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

theorem repeated_family_mean_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (F : ι → κ → ℂ) (hcard : 2≤Fintype.card ι)
    (hF : ∀i,(∑x,‖F i x‖^2)≤Fintype.card κ) :
    ‖(∑x,∏i,F i x)/(Fintype.card κ:ℂ)‖≤
      (Real.sqrt (Fintype.card κ))^(Fintype.card ι-2) := by
  classical
  let e := Fintype.card ι-2
  have he : Fintype.card ι=e+2 := by dsimp [e]; omega
  let E : Fin (e+2) ≃ ι := (Fintype.equivFinOfCardEq he).symm
  let f : κ → ℂ := fun x => F (E 0) x
  let g : κ → ℂ := fun x => F (E (Fin.succ 0)) x
  let rest : Fin e → κ → ℂ := fun j x => F (E j.succ.succ) x
  have hpoint (x : κ) : (∏i,F i x)=f x*g x*∏j,rest j x := by
    rw [← E.prod_comp (fun i => F i x)]
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    dsimp [f,g,rest]
    ring
  simp_rw [hpoint]
  exact repeated_local_mean_bound e f g rest (hF _) (hF _) (fun j => hF _)

theorem repeated_family_mean_mul_card {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (F : ι → κ → ℂ) (hcard : 2≤Fintype.card ι)
    (hF : ∀i,(∑x,‖F i x‖^2)≤Fintype.card κ) :
    (Fintype.card κ:ℝ)*‖(∑x,∏i,F i x)/(Fintype.card κ:ℂ)‖≤
      (Real.sqrt (Fintype.card κ))^(Fintype.card ι) := by
  have h := mul_le_mul_of_nonneg_left (repeated_family_mean_bound F hcard hF)
    (Nat.cast_nonneg (α := ℝ) (Fintype.card κ))
  have he : Fintype.card ι=2+(Fintype.card ι-2) := by omega
  rw [he,pow_add,Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h

end Ostmann.Construction

end

end OAI
