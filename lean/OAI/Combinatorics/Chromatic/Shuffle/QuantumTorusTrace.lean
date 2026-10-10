import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.QuantumTorus

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
lemma alternating_skew (hΩ : ∀m,Ω m m=0) (a b : M) : Ω a b= -(Ω b a) := by
  have hh:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ] at hh
  omega

lemma coefficient_trace (hΩ : ∀m,Ω m m=0) (r : M) (f g : Torus v Ω)
    (hf : ∀m,Ω m r≠0 → f m=0) : (f*g) r=(g*f) r := by
  classical
  change (Torus.multiply v Ω f g) r=(Torus.multiply v Ω g f) r
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases he : a+b=r
  · have har : Ω a r=0 := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp ha) (hf a hn)
    have hab : Ω a b=0 := by
      rw [←he,map_add,hΩ a,zero_add] at har
      exact har
    have hba : Ω b a=0 := by rw [alternating_skew Ω hΩ b a,hab,neg_zero]
    simp only [he,show b+a=r by rwa [add_comm],Finsupp.single_eq_same,hab,hba,
      zpow_zero,Units.val_one,mul_one]
    exact mul_comm _ _
  · have he' : b+a≠r := by rwa [add_comm]
    rw [Finsupp.single_eq_of_ne (Ne.symm he),Finsupp.single_eq_of_ne (Ne.symm he')]
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
