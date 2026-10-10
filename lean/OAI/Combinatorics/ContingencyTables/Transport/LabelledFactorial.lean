import OAI.Combinatorics.ContingencyTables.Transport.FactorialSignatures

namespace OAI

/-!
# Literal subset factorial lifts and their conditioned copy displays

A display is the actual subtype of available labelled elements. Its group
fibres are reindexed by Fin of their exact cardinalities. Removing or adding
actual labels changes the group counts by the exact integer updates, so the
conditioned subset matrices are congruent to the proved factorial copy
matrices. No binary-lift signature is assumed.
-/

namespace ContingencyTables.LabelledFactorial

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS BinaryContraction FactorialSignatures

variable {I G : Type*} [Fintype I] [Fintype G]

noncomputable def groupCount (group : I → G) (S : Set I) : G → ℕ :=
  fun u => (Finset.univ.filter (fun i => i ∈ S ∧ group i = u)).card

omit [Fintype G] in
lemma groupCount_insert (group : I → G) (S : Set I) (i : I) (hi : i ∉ S) :
    groupCount group (insert i S) = fun u => groupCount group S u + if u = group i then 1 else 0 := by
  funext u
  have heq : Finset.univ.filter (fun j => j ∈ insert i S ∧ group j = u) =
      if group i = u then insert i (Finset.univ.filter (fun j => j ∈ S ∧ group j = u))
      else Finset.univ.filter (fun j => j ∈ S ∧ group j = u) := by
    ext j
    by_cases h : group i = u
    · simp only [h, ite_true, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_insert_iff, Finset.mem_insert]
      constructor
      · rintro ⟨hji | hjS, hjg⟩
        · exact Or.inl hji
        · exact Or.inr ⟨hjS,hjg⟩
      · rintro (rfl | ⟨hjS,hjg⟩)
        · exact ⟨Or.inl rfl,h⟩
        · exact ⟨Or.inr hjS,hjg⟩
    · simp only [h, ite_false, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | hjS,hjg⟩
        · exact (h hjg).elim
        · exact ⟨hjS,hjg⟩
      · rintro ⟨hjS,hjg⟩; exact ⟨Or.inr hjS,hjg⟩
  unfold groupCount
  have hc := congrArg Finset.card heq
  convert hc.trans ?_ using 1
  · congr 1; ext j; simp
  · by_cases h : group i = u
    · simp only [h, ite_true]
      apply Finset.card_insert_of_notMem
      simp [hi]
    · simp [h, Ne.symm h]

omit [Fintype G] in
lemma groupCount_remove (group : I → G) (S : Set I) (i : I) (hi : i ∈ S) :
    groupCount group (S \ {i}) = removeOne (groupCount group S) (group i) := by
  funext u
  have heq : Finset.univ.filter (fun j => j ∈ S \ {i} ∧ group j = u) =
      (Finset.univ.filter (fun j => j ∈ S ∧ group j = u)).erase i := by
    ext j; simp; tauto
  unfold groupCount removeOne
  have hc := congrArg Finset.card heq
  convert hc.trans ?_ using 1
  · congr 1; ext j; simp
  · by_cases h : group i = u
    · rw [Finset.card_erase_of_mem (by simp [hi,h])]
      simp [h]
    · rw [Finset.erase_eq_of_notMem (by simp [h])]
      simp [Ne.symm h]

omit [Fintype G] in
lemma groupCount_removeTwo (group : I → G) (S : Set I) (i j : I)
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    groupCount group (S \ {i,j}) = removeTwo (groupCount group S) (group i) (group j) := by
  have heq : S \ {i,j} = (S \ {i}) \ {j} := by ext x; simp; tauto
  rw [heq, groupCount_remove group _ j (by simp [hj,hij.symm]), groupCount_remove group S i hi]
  rfl

omit [Fintype G] in
lemma groupCount_addTwo (group : I → G) (S : Set I) (i j : I)
    (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    groupCount group (S ∪ {i,j}) = addTwo (groupCount group S) (group i) (group j) := by
  have heq : S ∪ {i,j} = insert j (insert i S) := by ext x; simp; tauto
  rw [heq, groupCount_insert group _ j (by simp [hj,hij.symm]), groupCount_insert group S i hi]
  funext u
  rfl

omit [Fintype G] in
lemma fibre_card (group : I → G) (S : Set I) (u : G) :
    Fintype.card {i : {i // i ∈ S} // group i.val = u} = groupCount group S u := by
  let E : {i : {i // i ∈ S} // group i.val = u} ≃
      {i : I // i ∈ Finset.univ.filter (fun i => i ∈ S ∧ group i = u)} :=
    { toFun := fun i => ⟨i.val.val, by simp [i.val.property,i.property]⟩
      invFun := fun i => ⟨⟨i.val, by simpa using (Finset.mem_filter.mp i.property).2.1⟩,
        (Finset.mem_filter.mp i.property).2.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  exact (Fintype.card_congr E).trans (Fintype.card_coe _)

/-- The actual finite display, reindexed fibre by fibre by its exact copy count. -/
noncomputable def displayCopyEquiv (group : I → G) (S : Set I) :
    {i // i ∈ S} ≃ Copies (groupCount group S) :=
  (Equiv.sigmaFiberEquiv (fun i : {i // i ∈ S} => group i.val)).symm.trans
    (Equiv.sigmaCongrRight (fun u => Fintype.equivFinOfCardEq (fibre_card group S u)))

omit [Fintype G] in
lemma displayCopyEquiv_group (group : I → G) (S : Set I) (i : {i // i ∈ S}) :
    (displayCopyEquiv group S i).1 = group i.val := rfl

lemma groupCount_total (group : I → G) (S : Set I) :
    ∑ u, groupCount group S u = S.ncard := by
  have h := Fintype.card_congr (displayCopyEquiv group S)
  simp only [Copies, Fintype.card_sigma, Fintype.card_fin] at h
  have hc : Fintype.card {i // i ∈ S} = S.ncard := by
    exact Set.fintypeCard_eq_ncard S
  omega

noncomputable def firstLift (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (S : Set I) : ℝ :=
  h (groupCount group S) * factorialProduct (groupCount group S) / D

noncomputable def secondLift (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (S : Set I) : ℝ :=
  h (groupCount group S) * factorialProduct (groupCount group Sᶜ) / D

/-- Every entry of the literal subset omission matrix equals the copy
matrix entry at the canonical labels of the available display. -/
theorem firstLift_omission_matrix (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (A : Set I) :
    faceHessian (complementWeight (firstLift group h D)) A =
      (removalLiftMatrix h (groupCount group Aᶜ) D).submatrix
        (displayCopyEquiv group Aᶜ) (displayCopyEquiv group Aᶜ) := by
  ext i j
  by_cases hij : i = j
  · simp [faceHessian, removalLiftMatrix, Matrix.submatrix_apply, hij]
  have he : displayCopyEquiv group Aᶜ i ≠ displayCopyEquiv group Aᶜ j :=
    fun h => hij ((displayCopyEquiv group Aᶜ).injective h)
  have hs : (A ∪ {i.val,j.val})ᶜ = Aᶜ \ {i.val,j.val} := by ext x; simp; tauto
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  simp only [faceHessian, hij, ite_false, Matrix.submatrix_apply, removalLiftMatrix, he,
    complementWeight, firstLift, displayCopyEquiv_group]
  rw [hs, groupCount_removeTwo group Aᶜ i.val j.val i.property j.property hval]

/-- The literal second-lift addition matrix has the exact remaining-capacity
factorials of the canonical copy matrix. -/
theorem secondLift_addition_matrix (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (A : Set I) :
    faceHessian (secondLift group h D) A =
      (additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D).submatrix
        (displayCopyEquiv group Aᶜ) (displayCopyEquiv group Aᶜ) := by
  ext i j
  by_cases hij : i = j
  · simp [faceHessian, additionLiftMatrix, Matrix.submatrix_apply, hij]
  have he : displayCopyEquiv group Aᶜ i ≠ displayCopyEquiv group Aᶜ j :=
    fun h => hij ((displayCopyEquiv group Aᶜ).injective h)
  have hs : (A ∪ {i.val,j.val})ᶜ = Aᶜ \ {i.val,j.val} := by ext x; simp; tauto
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  simp only [faceHessian, hij, ite_false, Matrix.submatrix_apply, additionLiftMatrix, he,
    secondLift, displayCopyEquiv_group]
  rw [hs, groupCount_removeTwo group Aᶜ i.val j.val i.property j.property hval,
    groupCount_addTwo group A i.val j.val i.property j.property hval]

/-- Integer removal signatures imply the omission property of the literal
first factorial lift, through the proved exact copy-display congruence. -/
theorem firstLift_omission (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (hh : ∀ n, 0 ≤ h n)
    (hsig : ∀ A : Set I, A.ncard + 2 = Fintype.card I - k →
      OnePositiveDirection (integerRemovalMatrix h (groupCount group Aᶜ)).toBilin') :
    OmissionProperty (firstLift group h D) k := by
  intro A hA
  rw [firstLift_omission_matrix]
  apply onePositive_reindex (displayCopyEquiv group Aᶜ)
  have hs := removalLift_onePositive h (groupCount group Aᶜ) D hD hh (hsig A hA)
  have hm := (signature_iff _ (matrix_bilin_symm _ (show ∀ i j,
      removalLiftMatrix h (groupCount group Aᶜ) D i j =
      removalLiftMatrix h (groupCount group Aᶜ) D j i from by
    intro i j
    simp only [removalLiftMatrix, eq_comm, removeTwo_comm]))).mp hs
  convert hm using 1
  congr 2; exact Subsingleton.elim _ _

/-- Integer addition signatures imply the addition property of the literal
complementary-factorial lift. -/
theorem secondLift_addition (group : I → G) (h : (G → ℕ) → ℝ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (hh : ∀ n, 0 ≤ h n)
    (hsig : ∀ A : Set I, A.ncard + 2 = k →
      OnePositiveDirection (integerAdditionMatrix h (groupCount group A) (groupCount group Aᶜ)).toBilin') :
    AdditionProperty (secondLift group h D) k := by
  intro A hA
  rw [secondLift_addition_matrix]
  apply onePositive_reindex (displayCopyEquiv group Aᶜ)
  have hs := additionLift_onePositive h (groupCount group A) (groupCount group Aᶜ) D hD hh (hsig A hA)
  have hsymm : ∀ i j, additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D i j =
      additionLiftMatrix h (groupCount group A) (groupCount group Aᶜ) D j i := by
    intro i j
    have ha : addTwo (groupCount group A) i.1 j.1 = addTwo (groupCount group A) j.1 i.1 := by
      funext u
      unfold addTwo
      omega
    simp only [additionLiftMatrix, eq_comm, removeTwo_comm, ha]
  have hm := (signature_iff _ (matrix_bilin_symm _ hsymm)).mp hs
  convert hm using 1
  congr 2; exact Subsingleton.elim _ _

end ContingencyTables.LabelledFactorial

end OAI
