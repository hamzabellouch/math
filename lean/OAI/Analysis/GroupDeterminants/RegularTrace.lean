import OAI.Analysis.GroupDeterminants.TransferAlgebra

namespace OAI

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section RegularTrace
variable {G : Type} [Group G] {n : ℕ}

theorem identityVector_apply [DecidableEq G] (i j : Fin n) (g : G) :
    identityVector i (j, g) = if j = i ∧ g = 1 then 1 else 0 := by
  classical
  simp only [identityVector, lp.single_apply, Pi.single_apply, Prod.mk.injEq]

theorem groupTrace_regular {A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ G)}
    {T : Hilbert G n →L[ℂ] Hilbert G n} (hT : IsRegularOperator A T) :
    groupTrace T = ∑ i : Fin n, ((A i i).coeff 1 : ℂ) := by
  classical
  unfold groupTrace
  apply Finset.sum_congr rfl
  intro i _
  have hi (ξ : Hilbert G n) : inner ℂ (identityVector i) ξ = ξ (i, 1) := by
    simp [identityVector, lp.inner_single_left, RCLike.inner_apply]
  rw [hi, hT]
  rw [Finset.sum_eq_single i]
  · rw [(A i i).coeff.sum_eq_single 1]
    · simp [identityVector_apply]
    · intro g _ hg
      simp [identityVector_apply, hg]
    · simp
  · intro j _ hji
    simp [identityVector_apply, hji]
  · simp

end RegularTrace

end GroupRingDeterminant

end

end OAI
