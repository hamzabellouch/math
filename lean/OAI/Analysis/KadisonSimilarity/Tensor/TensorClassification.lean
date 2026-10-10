import OAI.Analysis.KadisonSimilarity.Tensor.TensorDensity
import OAI.Analysis.KadisonSimilarity.Tensor.TensorPermutations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-!
# From finite-stage pairings to permutation operators

The operator classification follows from the finite-stage coefficient
identity, using density, same-side-pair elimination, and completed tensor
permutations. The finite-stage identity remains a separately stated prerequisite.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Source letters precede all test letters in the orientation of a pair. -/
def sourceFirstRank {k l : ℕ} : Fin k ⊕ Fin l → ℕ :=
  Sum.elim Fin.val (fun j => k + j.val)

theorem sourceFirstRank_injective {k l : ℕ} :
    Function.Injective (@sourceFirstRank k l) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (Fin.ext hab)
    | inr j => simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr] at hab; omega
  | inr i =>
    cases b with
    | inl j => simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr] at hab; omega
    | inr j =>
      simp only [sourceFirstRank, Sum.elim_inr] at hab
      exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hab))

@[simp] theorem crossPairingEquiv_left {k l : ℕ}
    (P : PerfectMatching (Fin k ⊕ Fin l)) (hcross : IsCrossPairing P.1) (i : Fin k) :
    P.1 (Sum.inl i) = Sum.inr (crossPairingEquiv P.1 P.2.1 hcross i) :=
  (hcross.1 i).choose_spec

@[simp] theorem crossPairingEquiv_right {k l : ℕ}
    (P : PerfectMatching (Fin k ⊕ Fin l)) (hcross : IsCrossPairing P.1) (j : Fin l) :
    P.1 (Sum.inr j) = Sum.inl ((crossPairingEquiv P.1 P.2.1 hcross).symm j) :=
  (hcross.2 j).choose_spec

/-- For a cross pairing, the full polynomial has exactly one factor per source slot. -/
theorem pairingPolynomial_cross {k l : ℕ}
    (B : E →L[ℂ] E →L[ℂ] ℂ) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hcross : IsCrossPairing P.1) (x : Fin k → E) (z : Fin l → E) :
    pairingPolynomial sourceFirstRank B P (Sum.elim x z) =
      ∏ i, B (x i) (z (crossPairingEquiv P.1 P.2.1 hcross i)) := by
  classical
  have hleft (i : Fin k) : sourceFirstRank (k := k) (l := l) (Sum.inl i) <
      sourceFirstRank (P.1 (Sum.inl i)) := by
    rw [crossPairingEquiv_left P hcross]
    simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr]
    omega
  have hright (j : Fin l) : ¬ sourceFirstRank (k := k) (l := l) (Sum.inr j) <
      sourceFirstRank (P.1 (Sum.inr j)) := by
    rw [crossPairingEquiv_right P hcross]
    simp only [sourceFirstRank, Sum.elim_inl, Sum.elim_inr]
    omega
  unfold pairingPolynomial
  rw [Finset.prod_filter, Fintype.prod_sum_type]
  simp only [hleft, hright, ite_true, ite_false, Finset.prod_const_one, mul_one]
  simp only [crossPairingEquiv_left P hcross, Sum.elim_inl, Sum.elim_inr]

/-- The remaining contraction is the matrix coefficient of a position permutation. -/
theorem pairingPolynomial_eq_permutation_coefficient {n : ℕ}
    (J : E → E) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (P : PerfectMatching (Fin n ⊕ Fin n)) (hcross : IsCrossPairing P.1)
    (x y : Fin n → E) :
    pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y)) =
      inner ℂ (completedTensorWord y)
        (completedTensorPermutation (crossPairingEquiv P.1 P.2.1 hcross)
          (completedTensorWord x)) := by
  rw [pairingPolynomial_cross B P hcross, completedTensorPermutation_word,
    inner_completedTensorWord]
  simp only [Function.comp_apply, hB]
  let σ := crossPairingEquiv P.1 P.2.1 hcross
  have heq := Equiv.prod_comp σ (fun j => inner ℂ (y j) (x (σ.symm j)))
  simpa only [Equiv.symm_apply_apply] using heq

instance crossMatchingFintype (k l : ℕ) :
    Fintype {P : PerfectMatching (Fin k ⊕ Fin l) // IsCrossPairing P.1} :=
  Fintype.ofFinite _

/-- The explicit finite sum of the operators indexed by cross pairings. -/
def crossPairingOperator {n : ℕ}
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ) :
    CompletedTensorWord E n →L[ℂ] CompletedTensorWord E n :=
  ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1},
    c P.1 • (completedTensorPermutation
      (crossPairingEquiv P.1.1 P.1.2.1 P.2)).toContinuousLinearMap

/-- Density and boundedness eliminate all same-side terms in the finite-stage
formula and identify the completed operator as a finite sum of permutations. -/
theorem tensorOperator_eq_crossPairingOperator_of_stages {n : ℕ}
    (Y : CompletedTensorWord E n →L[ℂ] CompletedTensorWord E n)
    (J : E → E) (hJ : Continuous J) (hJJ : Function.Involutive J)
    (B : E →L[ℂ] E →L[ℂ] ℂ) (hB : ∀ x y, B x (J y) = inner ℂ y x)
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ)
    (h : ℕ → E) (hh : Orthonormal ℂ h) (hfix : ∀ m, J (h m) = h m)
    (S : ℕ → Set E) (hmono : Monotone S) (hdense : Dense (⋃ m, S m))
    (hstage : ∀ m, ∀ v : Fin n ⊕ Fin n → E, (∀ i, v i ∈ S m) →
      tracialWordCoefficient Y J v =
        ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    Y = crossPairingOperator c := by
  classical
  have hfull := tracial_pairing_identity_of_stages Y J hJ B sourceFirstRank c
    S hmono hdense hstage
  have hlabels (a b : ℕ) : B (h a) (h b) = if a = b then 1 else 0 := by
    rw [← hfix b, hB]
    simpa only [eq_comm] using (orthonormal_iff_ite.mp hh b a)
  have hexp := labelPairingExpansion_of_tracial_identity Y J B sourceFirstRank
    sourceFirstRank_injective c h hfix hlabels hfull
  have hzero (P : PerfectMatching (Fin n ⊕ Fin n)) (hP : ¬ IsCrossPairing P.1) : c P = 0 := by
    by_contra hc
    exact hP (nonzero_pairing_coefficient_isCrossPairing Y h hh c hexp P hc)
  apply sub_eq_zero.mp
  apply tensorOperator_eq_zero_of_word_coefficients
  intro x y
  have heq := hfull (Sum.elim x (J ∘ y))
  have hsum : (∑ P, c P * pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y))) =
      ∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1},
        c P.1 * pairingPolynomial sourceFirstRank B P.1 (Sum.elim x (J ∘ y)) := by
    symm
    rw [← Finset.sum_subtype
      (p := fun P : PerfectMatching (Fin n ⊕ Fin n) => IsCrossPairing P.1)
      (Finset.univ.filter (fun P : PerfectMatching (Fin n ⊕ Fin n) => IsCrossPairing P.1))
      (by simp) (fun P => c P * pairingPolynomial sourceFirstRank B P (Sum.elim x (J ∘ y)))]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro P _ hP
    have hn : ¬ IsCrossPairing P.1 := by simpa only [Finset.mem_filter,
      Finset.mem_univ, true_and] using hP
    rw [hzero P hn, zero_mul]
  rw [hsum] at heq
  have hJJ' (z : E) : J (J z) = z := hJJ z
  simp only [tracialWordCoefficient, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    hJJ'] at heq
  change inner ℂ (completedTensorWord y)
    (Y (completedTensorWord x) - crossPairingOperator c (completedTensorWord x)) = 0
  rw [inner_sub_right, heq]
  apply sub_eq_zero.mpr
  simp only [crossPairingOperator, sum_apply,
    smul_apply, inner_sum, inner_smul_right,
    LinearIsometry.coe_toContinuousLinearMap]
  apply Finset.sum_congr rfl
  intro P _
  rw [pairingPolynomial_eq_permutation_coefficient J B hB P.1 P.2]

/-- The usual statement as membership in the span of permutation operators. -/
theorem crossPairingOperator_mem_span_permutations {n : ℕ}
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ) :
    crossPairingOperator (E := E) c ∈ Submodule.span ℂ
      (Set.range (fun σ : Equiv.Perm (Fin n) =>
        (completedTensorPermutation (E := E) σ).toContinuousLinearMap)) := by
  classical
  apply Submodule.sum_mem
  intro P _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨_, rfl⟩

/-- Repeated-letter words see only the sum of the surviving coefficients. -/
theorem crossPairingOperator_constant {n : ℕ}
    (c : PerfectMatching (Fin n ⊕ Fin n) → ℂ) (x : E) :
    crossPairingOperator c (completedTensorWord (fun _ : Fin n => x)) =
      (∑ P : {P : PerfectMatching (Fin n ⊕ Fin n) // IsCrossPairing P.1}, c P.1) •
        completedTensorWord (fun _ : Fin n => x) := by
  classical
  simp only [crossPairingOperator, sum_apply,
    smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    completedTensorPermutation_constant, Finset.sum_smul]

end KadisonSimilarity

end

end OAI
