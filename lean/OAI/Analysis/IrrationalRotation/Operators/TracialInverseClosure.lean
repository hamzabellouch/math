import OAI.Analysis.IrrationalRotation.Operators.TracialDirectFiniteness

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {ξ : H}

theorem inverse_mem_of_two_sided_inverse
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hba : b * a = 1) (hab : a * b = 1) :
    b ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro w hw
  exact (InvariantRotation.ClosedRangeTransport.commute_partialInverse
    hba hab (one_mul b)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) a ha).symm
    (Commute.one_right w) (Commute.one_right w)).eq

theorem IsFaithfulTracialVector.left_inverse_mem
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hba : b * a = 1) : b ∈ M :=
  inverse_mem_of_two_sided_inverse ha hba (hτ.mul_eq_one_of_reverse ha hba)

theorem IsFaithfulTracialVector.isUnit_of_ambient_left_inverse
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hba : b * a = 1) :
    IsUnit (⟨a, ha⟩ : M) := by
  refine ⟨⟨⟨a, ha⟩, ⟨b, hτ.left_inverse_mem ha hba⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (hτ.mul_eq_one_of_reverse ha hba)
  · exact Subtype.ext hba

theorem IsFaithfulTracialVector.reverse_mul_eq_one
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hab : a * b = 1) : b * a = 1 := by
  have hstar : star b * star a = 1 := by
    simpa only [star_mul, star_one] using congrArg star hab
  have h := hτ.mul_eq_one_of_reverse (star_mem ha) hstar
  simpa only [star_mul, star_star, star_one] using congrArg star h

theorem IsFaithfulTracialVector.right_inverse_mem
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hab : a * b = 1) : b ∈ M :=
  inverse_mem_of_two_sided_inverse ha (hτ.reverse_mul_eq_one ha hab) hab

theorem IsFaithfulTracialVector.isUnit_of_ambient_right_inverse
    (hτ : IsFaithfulTracialVector M ξ)
    {a b : H →L[ℂ] H} (ha : a ∈ M) (hab : a * b = 1) :
    IsUnit (⟨a, ha⟩ : M) :=
  hτ.isUnit_of_ambient_left_inverse ha (hτ.reverse_mul_eq_one ha hab)

end Invariant233

end

end OAI
