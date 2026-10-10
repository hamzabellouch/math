import OAI.NumberTheory.DirichletL.Moments.CompleteCommon

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem primeSupport_mul (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    primeSupport (I*J)=primeSupport I∪primeSupport J := by
  simp only [primeSupport,normalizedFactors_mul hI hJ,Multiset.toFinset_add]

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

theorem reconstructed_commonSupport (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonSupport (C*a) (D*b)=primeSupport C := by
  unfold commonSupport
  rw [primeSupport_mul C a hC ha,primeSupport_mul D b hD hb,← hCD]
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  have h₃ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff ha hb).mpr hab
  ext P
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hc|ha',hd|hb'⟩
    · exact hc
    · exact hc
    · exact hd
    · exact False.elim (Finset.disjoint_left.mp h₃ ha' hb')
  · exact fun hp => ⟨Or.inl hp,Or.inl hp⟩

theorem reconstructed_commonParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonPart (C*a) (D*b)=C ∧ commonPart (D*b) (C*a)=D := by
  have hs := reconstructed_commonSupport C D a b hC hD ha hb hCD hCa hCb hab
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  constructor
  · rw [commonPart_eq_supportExtract,hs,supportExtract_mul C a hC ha,
      supportExtract_of_subset C hC _ (Finset.Subset.refl _),supportExtract_of_disjoint a _ h₁.symm,mul_one]
  · rw [commonPart_eq_supportExtract,commonSupport_comm (D*b) (C*a),hs,
      supportExtract_mul D b hD hb,
      supportExtract_of_subset D hD _ (by rw [hCD]),supportExtract_of_disjoint b _ h₂.symm,mul_one]

theorem reconstructed_residualParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    residualPart (C*a) (D*b)=a ∧ residualPart (D*b) (C*a)=b := by
  obtain ⟨h₁,h₂⟩ := reconstructed_commonParts C D a b hC hD ha hb hCD hCa hCb hab
  constructor
  · apply mul_left_cancel₀ hC
    have he := reconstruct (C*a) (D*b) (mul_ne_zero hC ha)
    rw [h₁] at he
    exact he.symm
  · apply mul_left_cancel₀ hD
    have he := reconstruct (D*b) (C*a) (mul_ne_zero hD hb)
    rw [h₂] at he
    exact he.symm

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
