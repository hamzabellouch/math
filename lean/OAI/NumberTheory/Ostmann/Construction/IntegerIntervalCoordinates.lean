import OAI.NumberTheory.Ostmann.Supply.RestrictedSubsetEnergy

namespace OAI

/-! # Identifying actual integer sets with the interval coordinates of the sieve -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def integerIntervalIndices (A : Finset ℤ) (J : ℤ) (M : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => J + (i.val : ℤ) ∈ A)

def integerIntervalPoint (J : ℤ) {M : ℕ} (i : Fin M) : ℤ := J + (i.val : ℤ)

 theorem integerIntervalPoint_injective (J : ℤ) (M : ℕ) :
    Function.Injective (integerIntervalPoint J (M := M)) := by
  intro i j h
  apply Fin.ext
  dsimp [integerIntervalPoint] at h
  omega

 theorem integerIntervalIndices_image (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) :
    (integerIntervalIndices A J M).image (integerIntervalPoint J) = A := by
  ext a
  constructor
  · rintro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  · intro ha
    obtain ⟨hlo, hhi⟩ := hA a ha
    have hsub : 0 ≤ a - J := by omega
    have hcast : ((a - J).toNat : ℤ) = a - J := Int.toNat_of_nonneg hsub
    let i : Fin M := ⟨(a - J).toNat, by omega⟩
    have hi : integerIntervalPoint J i = a := by dsimp [integerIntervalPoint, i]; omega
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    change integerIntervalPoint J i ∈ A
    rwa [hi]

 theorem integerIntervalIndices_card (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) :
    (integerIntervalIndices A J M).card = A.card := by
  have hh := congrArg Finset.card (integerIntervalIndices_image A J M hA)
  rw [Finset.card_image_of_injective _ (integerIntervalPoint_injective J M)] at hh
  exact hh

 theorem averagedCoordinates_image {ι κ α : Type*} (A : Finset ι) (f : ι → κ)
    (hf : Function.Injective f) (V : κ → α → ℂ) :
    averagedCoordinates (A.image f) V = averagedCoordinates A (fun x => V (f x)) := by
  funext x
  unfold averagedCoordinates
  rw [Finset.card_image_of_injective _ hf, Finset.sum_image]
  exact fun _ _ _ _ h => hf h

 theorem integerIntervalIndices_average (A : Finset ℤ) (J : ℤ) (M : ℕ)
    (hA : ∀ a ∈ A, J ≤ a ∧ a < J + M) {α : Type*} (V : ℤ → α → ℂ) :
    averagedCoordinates A V = averagedCoordinates (integerIntervalIndices A J M)
      (fun i => V (J + (i.val : ℤ))) := by
  funext x
  unfold averagedCoordinates
  rw [integerIntervalIndices_card A J M hA]
  congr 1
  symm
  apply Finset.sum_bij (fun i _ => integerIntervalPoint J i)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact integerIntervalPoint_injective J M hij
  · intro a ha
    have ha' : a ∈ (integerIntervalIndices A J M).image (integerIntervalPoint J) := by
      rwa [integerIntervalIndices_image A J M hA]
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ha'
    exact ⟨i, hi, he⟩
  · intro i hi
    rfl

 theorem restricted_integer_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n m M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hcover : ∀ q, q.Prime → q ≤ Q → ∃ i, p i = q)
    (A : Finset ℤ) (hA : A.Nonempty) (J : ℤ)
    (hArange : ∀ a ∈ A, J ≤ a ∧ a < J + M)
    (ha : ∀ x ∈ A, ∀ i, (x : ZMod (p i)) ∈ S i)
    (e : Fin m ↪ Fin n) (K : ℕ)
    (hprod : ∀ T : Finset (Fin m), T.card ≤ K → (∏ i ∈ T, p (e i)) ≤ Q)
    (hsmall : ∀ T : Finset (Fin m), T.card ≤ K →
      (∑ q ∈ T.image (fun i => p (e i)), (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      countingVectorNorm (lowModeVector K (averagedCoordinates A
        (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
          (fun i => (x : ZMod (p (e i))))))) ^ 2 ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  let I := integerIntervalIndices A J M
  have hcard : I.card = A.card := integerIntervalIndices_card A J M hArange
  have hI : I.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Finset.card_pos.mpr hA)
  have hh := restricted_lowMode_energy_budget ls p hc S hS κ hκ hκS hQ hM hcover I hI J
    (fun x hx i => ha _ (Finset.mem_filter.mp hx).2 i) e K hprod hsmall B hB hP
  rw [hcard] at hh
  have havg := integerIntervalIndices_average A J M hArange
    (fun x => tensorPointCoordinates (fun i => p (e i)) (fun i => S (e i))
      (fun i => (x : ZMod (p (e i)))))
  rw [← havg] at hh
  exact hh

end Ostmann

end OAI
