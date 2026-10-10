import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingBarEvaluation

namespace OAI

/-! # Alternation of the integral signed bar class

These identities hold before passing to homology and in every characteristic.
-/

noncomputable section
namespace PolycyclicRecognition
variable {I V : Type} [Fintype I] [DecidableEq I] [AddCommGroup V]

theorem signed_sum_of_left_swap_invariant (a b : I) (hab : a ≠ b)
    (f : Equiv.Perm I → V) (hf : ∀ σ, f (Equiv.swap a b * σ) = f σ) :
    ∑ σ : Equiv.Perm I, (Equiv.Perm.sign σ : ℤ) • f σ = 0 := by
  classical
  apply Finset.sum_ninvolution (fun σ => Equiv.swap a b * σ)
  · intro σ
    rw [hf]
    simp [map_mul, Equiv.Perm.sign_swap hab]
  · intro σ _ hfix
    have hs : Equiv.swap a b = (1 : Equiv.Perm I) :=
      mul_right_cancel (hfix.trans (one_mul σ).symm)
    have he := Equiv.congr_fun hs a
    apply hab
    simpa using he.symm
  · intro σ
    exact Finset.mem_univ _
  · intro σ
    simp [← mul_assoc]

variable {A : Type} [CommGroup A]

omit [CommGroup A] in
theorem alternatingBarChain_eq_zero_of_eq {n : ℕ} (v : Fin n → A)
    {i j : Fin n} (h : v i = v j) (hij : i ≠ j) : alternatingBarChain v = 0 := by
  classical
  have hv : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst k
      simpa using h.symm
    by_cases hkj : k = j
    · subst k
      simpa using h
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  apply signed_sum_of_left_swap_invariant i j hij
  intro σ
  have he : v ∘ (Equiv.swap i j * σ) = v ∘ σ := by
    change (v ∘ Equiv.swap i j) ∘ σ = _
    rw [hv]
  rw [he]

theorem alternatingBarClass_eq_zero_of_eq {n : ℕ} (v : Fin (n + 1) → A)
    {i j : Fin (n + 1)} (h : v i = v j) (hij : i ≠ j) : alternatingBarClass v = 0 := by
  have hz : alternatingBarCycle v = 0 := by
    apply (ModuleCat.mono_iff_injective
      (groupHomology.iCycles (integralTrivialCoefficient A) (n + 1))).mp inferInstance
    rw [alternatingBarCycle_val, map_zero]
    exact alternatingBarChain_eq_zero_of_eq v h hij
  rw [alternatingBarClass, hz, map_zero]

end PolycyclicRecognition

end

end OAI
