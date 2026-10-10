import OAI.NumberTheory.Ostmann.Construction.ConstituentMatchedFourier
import OAI.NumberTheory.Ostmann.Construction.FixedPivotTopConditions

namespace OAI

/-! # Exact prime guard and counterpart mask in the actual matched pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

noncomputable def constituentPrimePairChecks (K : Type*) [Fintype K] :
    List (TopPrimeCondition (Option K)) := atomPairChecks (fun i : K => [some i])

theorem constituentPrimePairChecks_hasVariable (K : Type*) [Fintype K] :
    ∀ c ∈ constituentPrimePairChecks K, c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi
  simp only [List.mem_singleton, reduceCtorEq] at hi

theorem constituentPrimePairChecks_iff {K : Type*} [Fintype K]
    (M : ℕ) (x : K → ℕ) :
    (∀ c ∈ constituentPrimePairChecks K, c.Holds (fixedPivotPrimeValues M x)) ↔
      Pairwise (fun i j => (x i).Coprime (x j)) := by
  simpa only [constituentPrimePairChecks, List.map_singleton, List.prod_singleton,
    fixedPivotPrimeValues] using
      (atomPairChecks_iff (fun i : K => [some i]) (fixedPivotPrimeValues M x))

theorem finiteEdgeWeight_mul_unary {K : Type*} [Fintype K]
    (E : K → K → ℕ → ℕ → ℂ) (η ν : K → ℕ → ℂ) (x : K → ℕ) :
    (∏ i, η i (x i)) * finiteEdgeWeight E ν x =
      finiteEdgeWeight E (fun i p => η i p * ν i p) x := by
  simp only [finiteEdgeWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

noncomputable def constituentCounterpartMask {H Y : Type*}
    (Q : H → Finset ℕ) (e : Equiv.Perm H) : H ⊕ Y → ℕ → ℂ
  | .inl h, p => if p ∈ Q (e.symm h) then 1 else 0
  | .inr _, _ => 1

theorem constituentCounterpartMask_norm {H Y : Type*}
    (Q : H → Finset ℕ) (e : Equiv.Perm H) (i : H ⊕ Y) (p : ℕ) :
    ‖constituentCounterpartMask Q e i p‖ ≤ 1 := by
  cases i <;> simp only [constituentCounterpartMask]
  · split_ifs <;> norm_num
  · norm_num

theorem constituentCounterpartMask_prod {H Y : Type*} [Fintype H] [Fintype Y]
    (Q : H → Finset ℕ) (e : Equiv.Perm H) (x : H ⊕ Y → ℕ) :
    (∏ i, constituentCounterpartMask Q e i (x i)) =
      ((∏ h, if x (.inl h) ∈ Q (e.symm h) then (1 : ℝ) else 0) : ℂ) := by
  rw [Fintype.prod_sum_type]
  simp only [constituentCounterpartMask, Finset.prod_const_one, mul_one,
    Complex.ofReal_one]

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ)
local notation "ρ" => (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
local notation "H" => CopyScheduleH ρ n
local notation "Y" => CopyScheduleY ρ n
local notation "K" => H ⊕ Y

noncomputable def constituentMatchedUnary (e : Equiv.Perm H)
    (Q : H → Finset ℕ) (M : ℕ) (t t' : FrequencyTree ℤ n) : K → ℕ → ℂ :=
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n t
  let ω := scheduledRetainedUnary ρ (fun _ => χ) κ pivot n t'
  let σ := Equiv.sumCongr e (Equiv.refl Y)
  fun i p => constituentCounterpartMask Q e i p *
    (externalPivotUnary (fun _ => χ) g ν M i p *
      conj (externalPivotUnary (fun _ => χ) g ω M (σ.symm i) p))

noncomputable def constituentMatchedGraph (e : Equiv.Perm H) : K → K → ℤ :=
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  graphDifference (retainedInternalGraph g)
    (transportGraph (Equiv.sumCongr e (Equiv.refl Y)) (retainedInternalGraph g))

omit [Fintype I] in
theorem constituentMatchedUnary_norm (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (e : Equiv.Perm H) (Q : H → Finset ℕ) (M : ℕ)
    (t t' : FrequencyTree ℤ n) (i : K) (p : ℕ) :
    ‖constituentMatchedUnary role size χ κ pivot n e Q M t t' i p‖ ≤ 1 := by
  have hh (s : FrequencyTree ℤ n) (i : K) :
      ‖externalPivotUnary (fun _ => χ) (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
        (scheduledRetainedUnary ρ (fun _ => χ) κ pivot n s) M i p‖ ≤ 1 :=
    externalPivotUnary_norm_le_one _ _ _ M
      (scheduledRetainedUnary_norm ρ (fun _ => χ) κ pivot hκ n s) i p
  unfold constituentMatchedUnary
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * (1 * 1) := mul_le_mul (constituentCounterpartMask_norm Q e i p)
      (mul_le_mul (hh t i) (hh t' _) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 1 := by norm_num

theorem constituentMaskedPair_fourier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t t' : FrequencyTree ℤ n)
    (e : Equiv.Perm H) (Q : H → Finset ℕ) (M : ℕ) (x : K → P) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := constituentCharacterCore role size (fun _ => χ) κ pivot n P hP
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ((∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0) : ℂ) *
      (core ((fun h => x (.inl h)), t) * conj (core ((fun h => x (.inl (e h))), t'))) =
    if ∀ c ∈ constituentPrimePairChecks K, c.Holds (fixedPivotPrimeValues M (fun i => (x i : ℕ))) then
      finiteEdgeWeight (dirichletGraphEdge (fun _ => χ) (constituentMatchedGraph role size pivot n e))
        (constituentMatchedUnary role size χ κ pivot n e Q M t t') (fun i => (x i : ℕ)) *
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
  have hp := constituentCharacterCore_pair_fourier role size χ κ pivot n P hP
    childBound pivotBound ranges ψ X lo hi (fun z : FrequencyTree ℤ n => z)
    (fun y => x (.inr y)) M (fun h => x (.inl h)) e t t'
  simp only [hx, hv] at hp
  trans (∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0 : ℂ) *
    (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) then
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi t (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
      conj (groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi t' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) *
      finiteEdgeWeight (dirichletGraphEdge (fun _ => χ) (constituentMatchedGraph role size pivot n e))
        (fun i p => externalPivotUnary (fun _ => χ)
          (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
          (scheduledRetainedUnary ρ (fun _ => χ) κ pivot n t) M i p *
          conj (externalPivotUnary (fun _ => χ)
            (scheduledRetainedGraph ρ initialCompleteGraph pivot n)
            (scheduledRetainedUnary ρ (fun _ => χ) κ pivot n t') M
            ((Equiv.sumCongr e (Equiv.refl Y)).symm i) p)) (fun i => (x i : ℕ))
    else 0)
  · congr 1
  split_ifs
  · rw [← constituentCounterpartMask_prod Q e (fun i => (x i : ℕ))]
    unfold constituentMatchedGraph constituentMatchedUnary
    conv_rhs => rw [← finiteEdgeWeight_mul_unary]
    ring
  · simp only [mul_zero]

end
end Ostmann

end OAI
