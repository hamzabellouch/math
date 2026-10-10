import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
namespace NilpotentInverse
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

                                                                             
                                                                 
theorem difference_pow (I : Ideal A) (f : A →ₐ[k] A)
    (haf : ∀ x : A, f x - x ∈ I)
    (hfirst : ∀ x ∈ I, f x - x ∈ I^2) (n : ℕ) :
    ∀ x ∈ I^n, f x - x ∈ I^(n+1) := by
  induction n with
  | zero => intro x _; simpa only [zero_add, pow_one] using haf x
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        have hfb : f b ∈ I := by
          simpa only [sub_add_cancel] using I.add_mem (haf b) hb
        have h₁ : (f a - a) * f b ∈ I^(n+1+1) := by
          rw [pow_succ]
          exact Ideal.mul_mem_mul (ih a ha) hfb
        have h₂ : a * (f b - b) ∈ I^(n+1+1) := by
          rw [show n+1+1 = n+2 by omega, pow_add]
          exact Ideal.mul_mem_mul ha (hfirst b hb)
        convert (I^(n+1+1)).add_mem h₁ h₂ using 1
        simp only [map_mul]
        ring
      · intro a b ha hb
        convert (I^(n+1+1)).add_mem ha hb using 1
        simp only [map_add]
        ring
                                                                     
                                                                      
theorem injective_of_first_jet (I : Ideal A) (hI : IsNilpotent I) (f : A →ₐ[k] A)
    (haf : ∀ x : A, f x - x ∈ I)
    (hfirst : ∀ x ∈ I, f x - x ∈ I^2) : Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  have hn (n : ℕ) : x ∈ I^n := by
    induction n with
    | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | succ n ih =>
        have ht := difference_pow I f haf hfirst n x ih
        rw [hx, zero_sub] at ht
        exact (I^(n+1)).neg_mem_iff.mp ht
  obtain ⟨n, hn₀⟩ := hI
  have ht := hn n
  rw [hn₀] at ht
  exact ht

theorem bijective_of_first_jet [Module.Finite k A] (I : Ideal A) (hI : IsNilpotent I)
    (f : A →ₐ[k] A)
    (haf : ∀ x : A, f x - x ∈ I)
    (hfirst : ∀ x ∈ I, f x - x ∈ I^2) : Function.Bijective f := by
  have hi := injective_of_first_jet I hI f haf hfirst
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := f.toLinearMap)).mp hi⟩

                                                                           
theorem first_jet_of_generators {σ : Type*} (c : σ → A) (f : A →ₐ[k] A)
    (haf : ∀ x : A, f x - x ∈ Ideal.span (Set.range c))
    (hgen : ∀ i, f (c i) - c i ∈ (Ideal.span (Set.range c))^2) :
    ∀ x ∈ Ideal.span (Set.range c), f x - x ∈ (Ideal.span (Set.range c))^2 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hgen i
  | zero => simp
  | add a b ha hb ha₁ hb₁ =>
      convert (Ideal.span (Set.range c)^2).add_mem ha₁ hb₁ using 1
      simp only [map_add]
      ring
  | smul a b hb hb₁ =>
      change f (a*b) - a*b ∈ _
      have ht : (f a - a)*b ∈ Ideal.span (Set.range c)^2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (haf a) hb
      have ht' := (Ideal.span (Set.range c)^2).mul_mem_left (f a) hb₁
      convert (Ideal.span (Set.range c)^2).add_mem ht' ht using 1
      simp only [map_mul]
      ring

end NilpotentInverse
end BoundaryOnly.FormalObstruction

end

end OAI
