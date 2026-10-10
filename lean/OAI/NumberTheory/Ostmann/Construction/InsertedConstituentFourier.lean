import OAI.NumberTheory.Ostmann.Construction.InsertedConstituentWords

namespace OAI

/-! # The actual fixed-pivot weight in the supported word-Fourier coordinates -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform

theorem inserted_full_fourier_eq_grouped {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t =
    groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
      childBound pivotBound ranges ψ X lo hi t (insertedConstituentValues role size n M l u) := by
  rw [groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext v
  exact (insertedConstituentWord_prod role size n M l u v).symm

theorem inserted_full_fourier_permuted {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (e (constituentH role size n h k)))
        (fun y => ∏ k, u (constituentY role size n y k))) t =
    groupedFullCoprimeFourierWeight role n
      (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
      childBound pivotBound ranges ψ X lo hi t (insertedConstituentValues role size n M l u) := by
  rw [groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext v
  rw [List.map_map]
  rw [insertedConstituentValues_perm]
  exact (insertedConstituentWord_prod role size n M (l ∘ e) u v).symm

theorem constituentUnweighted_fourier_eq_grouped {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M a =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) then
      groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi (hist a.2)
        (insertedConstituentValues role size n M (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  unfold constituentUnweightedTransferWeight
  rw [inserted_full_fourier_eq_grouped role size n childBound pivotBound ranges ψ X lo hi
    (hist a.2) M (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))]

theorem constituentUnweighted_permuted_fourier_eq_grouped {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) (d : D) :
    constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l ∘ e, d) =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) then
      groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi (hist d)
        (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n))
  let q := Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
  have he : Sum.elim (fun h => (l (e h) : ℕ)) (fun y => (u y : ℕ)) = q ∘ σ := by
    funext i
    cases i <;> rfl
  have hp : Pairwise (fun i j => (q (σ i)).Coprime (q (σ j))) ↔
      Pairwise (fun i j => (q i).Coprime (q j)) := by
    constructor
    · intro h i j hij
      simpa only [Equiv.apply_symm_apply] using h (σ.symm.injective.ne hij)
    · intro h i j hij
      exact h (σ.injective.ne hij)
  unfold constituentUnweightedTransferWeight
  simp only [Function.comp_apply, he]
  change (if Pairwise (fun i j => (q (σ i)).Coprime (q (σ j))) then _ else 0) = _
  rw [hp]
  congr 1
  exact inserted_full_fourier_permuted role size n childBound pivotBound ranges ψ X lo hi
    (hist d) M (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) e

theorem insertedExpandedTemplate_size {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (S : ℕ) (hS : 1 ≤ S) (hsize : ∀ i, size i ≤ S) :
    (expandedRootTemplate role n (insertedConstituentWord role size n)
      childBound pivotBound).WordsBounded (2 * 3 ^ n * Fintype.card I * S + 4) := by
  exact expandedRootTemplate_size role n (insertedConstituentWord role size n)
    childBound pivotBound S hS (insertedConstituentWord_length_le role size n S hS hsize)

/-- The fixed pivot is a constant coordinate of the exact word formula; it
receives no prime marginal. All inherited coprimality and interval tests remain. -/
theorem inserted_full_fourier_coefficient {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, starRingEnd ℂ (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    let words := insertedConstituentWord role size n
    let q := insertedConstituentValues role size n M l u
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t =
      if ∀ c ∈ atomPairChecks words, c.Holds q then
        (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
          (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
          (expandedRootRanges role n words (totalAtomUnitRanges role))
          (expandedRootRanges role n words ranges)
          (expandedRootTemplate role n words childBound pivotBound) t ht q
      else 0 := by
  dsimp only
  rw [inserted_full_fourier_eq_grouped]
  exact groupedFullCoprimeFourierWeight_coefficient role n (insertedConstituentWord role size n)
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi t ht _ hu

end Ostmann

end OAI
