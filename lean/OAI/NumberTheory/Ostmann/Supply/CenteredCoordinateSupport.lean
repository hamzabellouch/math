import OAI.NumberTheory.Ostmann.Supply.FiniteCoordinateEnergy
import OAI.NumberTheory.Ostmann.Characters.SparseTruncatedWeight

namespace OAI

/-! # Decomposing the actual tensor coordinates by their centered support -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def supportedCoordinates {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) (i : Fin n) : Option (ZMod (p i)) :=
  if hi : i ∈ T then some (z ⟨i, hi⟩) else none

@[simp] theorem supportedCoordinates_support {n : ℕ} (p : Fin n → ℕ)
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) :
    centeredCoordinateSupport (supportedCoordinates p T z) = T := by
  ext i
  simp [centeredCoordinateSupport, supportedCoordinates]

theorem supportedCoordinates_injective {n : ℕ} (p : Fin n → ℕ) :
    Function.Injective (fun z : Σ T : Finset (Fin n), (∀ i : T, ZMod (p i)) =>
      supportedCoordinates p z.1 z.2) := by
  rintro ⟨T, z⟩ ⟨U, w⟩ h
  have hT := congrArg centeredCoordinateSupport h
  simp only [supportedCoordinates_support] at hT
  subst U
  congr 1
  funext i
  have hi := congrFun h i
  simpa [supportedCoordinates, i.property] using hi

private theorem supportedCoordinates_reconstruct {n : ℕ} (p : Fin n → ℕ)
    (x : ∀ i, Option (ZMod (p i))) :
    supportedCoordinates p (centeredCoordinateSupport x) (fun i => (x i).get
      (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp i.property).2)) = x := by
  funext i
  by_cases hi : x i = none
  · simp [supportedCoordinates, centeredCoordinateSupport, hi]
  · have hmem : i ∈ centeredCoordinateSupport x := by
      simp [centeredCoordinateSupport, hi]
    simp only [supportedCoordinates, dite_eq_left hmem]
    exact Option.some_get _

noncomputable def centeredSupportEquiv {n : ℕ} (p : Fin n → ℕ) :
    (∀ i, Option (ZMod (p i))) ≃ Σ T : Finset (Fin n), (∀ i : T, ZMod (p i)) where
  toFun x := ⟨centeredCoordinateSupport x, fun i => (x i).get
    (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp i.property).2)⟩
  invFun z := supportedCoordinates p z.1 z.2
  left_inv := supportedCoordinates_reconstruct p
  right_inv z := by
    apply supportedCoordinates_injective p
    exact supportedCoordinates_reconstruct p _

theorem tensorPointCoordinates_supported {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
    (T : Finset (Fin n)) (z : ∀ i : T, ZMod (p i)) (a : ∀ i, ZMod (p i)) :
    tensorPointCoordinates p S a (supportedCoordinates p T z) =
      centeredSubsetVector p S T a z := by
  unfold tensorPointCoordinates centeredSubsetVector
  calc
    _ = ∏ i ∈ T, residuePointCoordinates (S i) (a i)
        (supportedCoordinates p T z i) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ T)
      intro i _ hi
      simp [supportedCoordinates, hi, residuePointCoordinates]
    _ = ∏ i : T, residuePointCoordinates (S i) (a i)
        (supportedCoordinates p T z i) := (Finset.prod_coe_sort T _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [supportedCoordinates, i.property, residuePointCoordinates]

/-- The low-mode norm appearing in the actual truncated-kernel pairing is the
sum of the centered subset energies, without a dimension-dependent loss. -/
theorem lowMode_tensor_energy {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) {ι : Type*} (A : Finset ι)
    (a : ι → ∀ i, ZMod (p i)) (K : ℕ) :
    countingVectorNorm (lowModeVector K
      (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))) ^ 2 =
      ∑ T : Finset (Fin n), if T.card ≤ K then centeredSubsetEnergy p S T A a else 0 := by
  rw [countingVectorNorm_sq, ← (centeredSupportEquiv p).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T _
  change (∑ z : (∀ i : T, ZMod (p i)),
    ‖lowModeVector K (averagedCoordinates A (fun x => tensorPointCoordinates p S (a x)))
      (supportedCoordinates p T z)‖ ^ 2) = _
  simp only [lowModeVector, supportedCoordinates_support]
  by_cases hT : T.card ≤ K
  · simp only [hT, ite_true]
    rw [centeredSubsetEnergy, countingVectorNorm_sq]
    apply Finset.sum_congr rfl
    intro z _
    simp only [averagedCoordinates, tensorPointCoordinates_supported]
  · simp [hT]

end Ostmann

end OAI
