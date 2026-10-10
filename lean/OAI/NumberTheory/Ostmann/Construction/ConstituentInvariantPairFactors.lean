import OAI.NumberTheory.Ostmann.Construction.ConstituentPairFactors
import OAI.NumberTheory.Ostmann.Construction.ConstituentInvariantFourier

namespace OAI

/-! # Original conjugate-role characters in the exact masked pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform
section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ)

noncomputable def constituentInvariantUnary (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
    (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ) (t t' : FrequencyTree ℤ n) : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → ℕ → ℂ :=
  let g := scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t
  let ω := scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t'
  let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
  fun i p => constituentCounterpartMask Q e i p *
    (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) g ν M i p *
      conj (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) g ω M (σ.symm i) p))

omit [Fintype I] in
theorem constituentInvariantUnary_norm (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ)
    (t t' : FrequencyTree ℤ n) (i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (p : ℕ) :
    ‖constituentInvariantUnary role size χ κ pivot n e Q M t t' i p‖ ≤ 1 := by
  have hh (s : FrequencyTree ℤ n) (i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) :
      ‖externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
        (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n s) M i p‖ ≤ 1 :=
    externalPivotUnary_norm_le_one _ _ _ M
      (scheduledRetainedUnary_norm ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot hκ n s) i p
  unfold constituentInvariantUnary
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * (1 * 1) := mul_le_mul (constituentCounterpartMask_norm Q e i p)
      (mul_le_mul (hh t i) (hh t' _) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 1 := by norm_num

theorem constituentMaskedPair_invariant_fourier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t t' : FrequencyTree ℤ n)
    (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
    (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
    (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ) (x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := constituentCharacterCore role size χ κ pivot n P hP
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ((∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0) : ℂ) *
      (core ((fun h => x (.inl h)), t) * conj (core ((fun h => x (.inl (e h))), t'))) =
    if ∀ c ∈ constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)), c.Holds (fixedPivotPrimeValues M (fun i => (x i : ℕ))) then
      finiteEdgeWeight (dirichletGraphEdge (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (constituentMatchedGraph role size pivot n e))
        (constituentInvariantUnary role size χ κ pivot n e Q M t t') (fun i => (x i : ℕ)) *
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi t (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
      conj (groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi t' (fixedPivotPrimeValues M (fun i => (x i : ℕ)))))
    else 0 := by
  dsimp only
  simp only [constituentPrimePairChecks_iff]
  have hx : Sum.elim (fun h => (x (.inl h) : ℕ)) (fun y => (x (.inr y) : ℕ)) =
      (fun i => (x i : ℕ)) := by funext i; cases i <;> rfl
  have hv : insertedConstituentValues role size n M (fun h => (x (.inl h) : ℕ))
      (fun y => (x (.inr y) : ℕ)) = fixedPivotPrimeValues M (fun i => (x i : ℕ)) := by
    funext i; rcases i with _ | (h | y) <;> rfl
  have hp := constituentCharacterCore_invariant_pair_fourier role size χ κ pivot n P hP
    childBound pivotBound ranges ψ X lo hi (fun z : FrequencyTree ℤ n => z)
    (fun y => x (.inr y)) M (fun h => x (.inl h)) e hχ t t'
  simp only [hx, hv] at hp
  trans (∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0 : ℂ) *
    (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) then
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi t (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
      conj (groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi t' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) *
      finiteEdgeWeight (dirichletGraphEdge (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (constituentMatchedGraph role size pivot n e))
        (fun i p => externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n)
          (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
          (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t) M i p *
          conj (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n)
            (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
            (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t') M
            ((Equiv.sumCongr e (Equiv.refl (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))).symm i) p)) (fun i => (x i : ℕ))
    else 0)
  · congr 1
  split_ifs
  · rw [← constituentCounterpartMask_prod Q e (fun i => (x i : ℕ))]
    unfold constituentMatchedGraph constituentInvariantUnary
    conv_rhs => rw [← finiteEdgeWeight_mul_unary]
    ring
  · simp only [mul_zero]

end
end Ostmann

end OAI
