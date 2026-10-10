import Mathlib

namespace OAI

noncomputable section

namespace KKVariableUltra

noncomputable section

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Fintype ι] [DecidableEq ι]

theorem matrix_range_center (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (hρ : Function.Injective ρ)
    (a : ρ.range) (ha : ∀ b : ρ.range, Commute a b) : ∃ c : ℂ, a=c•1 := by
  obtain ⟨x,hx⟩ := a.property
  change ρ x=a.val at hx
  have hc : ∀ y : Matrix ι ι ℂ, Commute x y := by
    intro y
    apply hρ
    rw [map_mul,map_mul]
    have hh := congrArg Subtype.val (ha ⟨ρ y,⟨y,rfl⟩⟩).eq
    change a.val*ρ y=ρ y*a.val at hh
    simpa only [hx] using hh
  obtain ⟨c,hc⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j _ => (hc (Matrix.single i j 1)).symm)
  refine ⟨c,Subtype.ext ?_⟩
  change a.val=c•(1:A)
  rw [← hx,← hc]
  change ρ (algebraMap ℂ (Matrix ι ι ℂ) c)=c•(1:A)
  simp only [Algebra.algebraMap_eq_smul_one,map_smul,map_one]

end

end KKVariableUltra
end

end OAI
