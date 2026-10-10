import OAI.NumberTheory.EgyptianFractions.RandomCommonRealization
import OAI.NumberTheory.EgyptianFractions.ResidueWideDenominator

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Reindex Boolean product words by the two-element finite type used in the
auxiliary-denominator construction. No product values are identified. -/
def residueWordEquiv (m : ℕ) : (Fin m → Fin 2) ≃ (Fin m → Bool) :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) finTwoEquiv

/-- The same labelled samples, in the paired-block interface. -/
def residueSamplePairs {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) : Fin m → Fin 2 → ℕ :=
  fun j e => (f (j, finTwoEquiv e) : ℕ)

@[simp] theorem pairedEntry_residueSamplePairs {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) (I : Fin m → Fin 2) :
    ResidueConstruction.pairedEntry (residueSamplePairs f) I =
      sampledProduct f (residueWordEquiv m I) := by
  rfl

@[simp] theorem sampledProduct_residueWordEquiv_symm {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) (I : Fin m → Bool) :
    ResidueConstruction.pairedEntry (residueSamplePairs f)
      ((residueWordEquiv m).symm I) = sampledProduct f I := by
  rw [pairedEntry_residueSamplePairs, Equiv.apply_symm_apply]

/-- Reindexing preserves every normalized product statistic, including the
complex Fourier averages used by the common-realization theorem. -/
theorem expect_pairedEntry_eq_sampledProduct {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (g : ℕ → A) :
    (𝔼 I : Fin m → Fin 2, g (ResidueConstruction.pairedEntry (residueSamplePairs f) I)) =
      𝔼 I : Fin m → Bool, g (sampledProduct f I) := by
  apply Fintype.expect_equiv (residueWordEquiv m)
  intro I
  rfl

/-- Exact preservation of filtered list cardinalities retains multiplicities
when separate words happen to have equal product values. -/
theorem card_pairedEntry_eq_sampledProduct {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) (R : ℕ → Prop) [DecidablePred R] :
    (Finset.univ.filter (fun I : Fin m → Fin 2 =>
      R (ResidueConstruction.pairedEntry (residueSamplePairs f) I))).card =
    (Finset.univ.filter (fun I : Fin m → Bool => R (sampledProduct f I))).card := by
  apply Finset.card_bij (fun I _ => residueWordEquiv m I)
  · intro I hI
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      pairedEntry_residueSamplePairs] using hI
  · intro I hI J hJ hIJ
    exact (residueWordEquiv m).injective hIJ
  · intro J hJ
    refine ⟨(residueWordEquiv m).symm J, ?_, Equiv.apply_symm_apply _ _⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      sampledProduct_residueWordEquiv_symm] using hJ

/-- A single denominator simultaneously contains the deterministic subset
products and the original Boolean-indexed sampled products. The conclusion is
valid for every realization of the prime samples; no probabilistic independence
or Fourier hypothesis is needed for this arithmetic construction. -/
theorem construct_sampled_residue_denominator {m : ℕ} {P : Finset ℕ}
    (p : Fin m → ℕ) (f : Fin 1000 → ((Fin m × Bool) → P)) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hp : ∀ j, S ^ 100 ≤ (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101)
    (hP : ∀ q ∈ P, S ^ 100 ≤ (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Fin 2, ResidueConstruction.subsetEntry p I ∣ M ∧
        1 ≤ ResidueConstruction.subsetEntry p I ∧
        (ResidueConstruction.subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Bool), sampledProduct (f i) I ∣ M ∧
        1 ≤ sampledProduct (f i) I ∧
        (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  have hSpos : 0 < S := by linarith
  have hpPos : ∀ j, 0 < p j := by
    intro j
    exact_mod_cast (lt_of_lt_of_le (pow_pos hSpos 100) (hp j).1)
  have hqPos : ∀ i j e, 0 < residueSamplePairs (f i) j e := by
    intro i j e
    exact_mod_cast (lt_of_lt_of_le (pow_pos hSpos 100)
      (hP _ (f i (j, finTwoEquiv e)).property).1)
  have hpLower : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ) := by
    intro j
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (pow_pos hSpos 100) (hp j).1
  have hpUpper : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S := by
    intro j
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by exact_mod_cast hpPos j) (hp j).2
  have hqUpper : ∀ i j e,
      Real.log (residueSamplePairs (f i) j e : ℝ) ≤ 101 * Real.log S := by
    intro i j e
    simpa only [Real.log_pow, Nat.cast_ofNat, residueSamplePairs] using
      Real.log_le_log (by exact_mod_cast hqPos i j e)
        (hP _ (f i (j, finTwoEquiv e)).property).2
  obtain ⟨M, hMl, hMu, hb, hfixed, hpaired⟩ :=
    ResidueConstruction.construct_residue_denominator_wide p
      (fun i => residueSamplePairs (f i)) hpPos hqPos hS hlog hlarge hmLower hmUpper
      hpLower hpUpper hqUpper
  refine ⟨M, hMl, hMu, hb, hfixed, ?_⟩
  intro i I
  simpa only [sampledProduct_residueWordEquiv_symm] using
    hpaired i ((residueWordEquiv m).symm I)

/-- The deterministic subset list on the same Boolean-word index type as the
sampled lists. This changes indices only, never the list entries or multiplicities. -/
def residueSubsetProduct {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Bool) : ℕ :=
  ResidueConstruction.subsetEntry p ((residueWordEquiv m).symm I)

/-- The reindexed deterministic list has the usual subset-product formula. -/
theorem residueSubsetProduct_eq_prod {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Bool) :
    residueSubsetProduct p I = ∏ j, if I j then p j else 1 := by
  unfold residueSubsetProduct ResidueConstruction.subsetEntry
  apply Finset.prod_congr rfl
  intro j hj
  change p j ^ (finTwoEquiv.symm (I j)).val = _
  cases I j <;> simp [finTwoEquiv]

/-- The deterministic Boolean-indexed list remains injective for distinct primes. -/
theorem residueSubsetProduct_injective {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (residueSubsetProduct p) := by
  exact (ResidueConstruction.subsetEntry_injective p hp hinj).comp
    (residueWordEquiv m).symm.injective

/-- Any normalized statistic of the deterministic list is unchanged by reindexing. -/
theorem expect_residueSubsetProduct {m : ℕ} (p : Fin m → ℕ)
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A] (g : ℕ → A) :
    (𝔼 I : Fin m → Bool, g (residueSubsetProduct p I)) =
      𝔼 I : Fin m → Fin 2, g (ResidueConstruction.subsetEntry p I) := by
  apply Fintype.expect_equiv (residueWordEquiv m).symm
  intro I
  rfl

/-- The denominator construction with the single common Boolean-word index
used by both high-level deterministic and lower-level sampled residue estimates. -/
theorem construct_sampled_residue_denominator_common_index {m : ℕ} {P : Finset ℕ}
    (p : Fin m → ℕ) (f : Fin 1000 → ((Fin m × Bool) → P)) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hp : ∀ j, S ^ 100 ≤ (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101)
    (hP : ∀ q ∈ P, S ^ 100 ≤ (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Bool, residueSubsetProduct p I ∣ M ∧
        1 ≤ residueSubsetProduct p I ∧
        (residueSubsetProduct p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Bool), sampledProduct (f i) I ∣ M ∧
        1 ≤ sampledProduct (f i) I ∧
        (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  obtain ⟨M, hMl, hMu, hb, hfixed, hsampled⟩ :=
    construct_sampled_residue_denominator p f hS hlog hlarge hmLower hmUpper hp hP
  exact ⟨M, hMl, hMu, hb, (fun I => hfixed ((residueWordEquiv m).symm I)), hsampled⟩

end Problem337.RandomProducts

end

end OAI
