import OAI.Analysis.KadisonSimilarity.Tensor.TensorWords
import OAI.Analysis.KadisonSimilarity.Tensor.PairingLabels
import Mathlib.Data.Nat.Pairing

namespace OAI

/-!
# Hilbert tensor tests excluding same-side pairings

The source and test vectors are finite sums of actual elementary Hilbert
tensors. Their orthonormal summands give the square-root norm growth, whereas
the isolated pairing coefficient grows with the full number of labels.
-/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {k l : ℕ}

/-- The restriction of a pairing expansion to an orthonormal alphabet. This
is the concrete finite-expansion data used by the test, not an invariant
classification hypothesis. -/
def LabelPairingExpansion {J : Type*} [DecidableEq J]
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : J → E) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) : Prop :=
  ∀ (s : Fin k → J) (t : Fin l → J),
    inner ℂ (completedTensorWord (fun i => h (t i)))
      (Y (completedTensorWord (fun i => h (s i)))) =
      ∑ Q, c Q * pairingLabelKernel Q (Sum.elim s t)

/-- Relabeling an orthonormal alphabet by an injection preserves the formula. -/
theorem LabelPairingExpansion.comp {I J : Type*} [DecidableEq I] [DecidableEq J]
    {Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l}
    {h : J → E} {c : PerfectMatching (Fin k ⊕ Fin l) → ℂ}
    (hexp : LabelPairingExpansion Y h c) (f : I → J) (hf : Function.Injective f) :
    LabelPairingExpansion Y (h ∘ f) c := by
  intro s t
  change inner ℂ (completedTensorWord (fun i => h ((f ∘ t) i)))
    (Y (completedTensorWord (fun i => h ((f ∘ s) i)))) = _
  rw [hexp (f ∘ s) (f ∘ t)]
  apply Finset.sum_congr rfl
  intro Q _
  congr 1
  unfold pairingLabelKernel
  apply Finset.prod_congr rfl
  intro i _
  have heq (i : Fin k ⊕ Fin l) : Sum.elim (f ∘ s) (f ∘ t) i = f (Sum.elim s t i) := by
    cases i <;> rfl
  simp only [heq, hf.eq_iff]

/-- Independent label choices on source-source pairs. -/
def sourcePairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (M : ℕ) : CompletedTensorWord E k := by
  classical
  exact ∑ f : SourcePairClasses P → Fin M,
    completedTensorWord (fun i => h (sourcePairLabels P f i))

/-- Independent label choices on test-test pairs. -/
def testPairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (M : ℕ) : CompletedTensorWord E l := by
  classical
  exact ∑ g : TestPairClasses P → Fin M,
    completedTensorWord (fun j => h (testPairLabels P g j))

theorem norm_sourcePairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (hh : Orthonormal ℂ h) (M : ℕ) :
    ‖sourcePairingTest P h M‖ = Real.sqrt ((M : ℝ) ^ Fintype.card (SourcePairClasses P)) := by
  have ho := (orthonormal_completedTensorWords h hh k).comp
    (sourcePairLabels P (M := M)) (sourcePairLabels_injective P M)
  simpa [sourcePairingTest, Function.comp_def, Fintype.card_fun] using norm_sum_orthonormal _ ho

theorem norm_testPairingTest (P : PerfectMatching (Fin k ⊕ Fin l))
    (h : PermutationCycles P.1 × ℕ → E) (hh : Orthonormal ℂ h) (M : ℕ) :
    ‖testPairingTest P h M‖ = Real.sqrt ((M : ℝ) ^ Fintype.card (TestPairClasses P)) := by
  have ho := (orthonormal_completedTensorWords h hh l).comp
    (testPairLabels P (M := M)) (testPairLabels_injective P M)
  simpa [testPairingTest, Function.comp_def, Fintype.card_fun] using norm_sum_orthonormal _ ho

private theorem pairingExpansion_label_test
    (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ) :
    (∑ Q, c Q * pairingLabelKernel Q
      (Sum.elim (sourcePairLabels P f) (testPairLabels P g))) = c P := by
  classical
  simp [pairingLabelKernel_isolate P _ _ (pairLabels_eq_iff P f g)]

/-- Every summand contributes the same isolated coefficient. -/
theorem inner_pairingTests
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (M : ℕ) :
    inner ℂ (testPairingTest P h M) (Y (sourcePairingTest P h M)) =
      c P * (M : ℂ) ^ (Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) := by
  classical
  unfold LabelPairingExpansion at hexp
  simp only [sourcePairingTest, testPairingTest, map_sum, sum_inner, inner_sum]
  simp_rw [hexp, pairingExpansion_label_test P]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]
  rw [pow_add]
  ring

private theorem sqrt_power_product (M a b : ℕ) :
    Real.sqrt ((M : ℝ) ^ a) * Real.sqrt ((M : ℝ) ^ b) =
      (M : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) := by
  rw [← Real.sqrt_mul (by positivity), ← pow_add, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The isolated coefficient grows as M^(rS+rT), while the two actual tensor
norms grow as M^((rS+rT)/2). -/
theorem pairing_coefficient_growth_bound
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (hh : Orthonormal ℂ h) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (M : ℕ) :
    ‖c P‖ * (M : ℝ) ^ ((Fintype.card (SourcePairClasses P) +
      Fintype.card (TestPairClasses P) : ℕ) : ℝ) ≤
      ‖Y‖ * (M : ℝ) ^ (((Fintype.card (SourcePairClasses P) +
        Fintype.card (TestPairClasses P) : ℕ) : ℝ) / 2) := by
  have hbound : ‖inner ℂ (testPairingTest P h M) (Y (sourcePairingTest P h M))‖ ≤
      ‖Y‖ * (‖sourcePairingTest P h M‖ * ‖testPairingTest P h M‖) := by
    calc
      _ ≤ ‖testPairingTest P h M‖ * ‖Y (sourcePairingTest P h M)‖ := norm_inner_le_norm _ _
      _ ≤ ‖testPairingTest P h M‖ * (‖Y‖ * ‖sourcePairingTest P h M‖) :=
        mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  rw [inner_pairingTests Y P h c hexp M, norm_mul, norm_pow, Complex.norm_natCast,
    norm_sourcePairingTest P h hh M, norm_testPairingTest P h hh M,
    sqrt_power_product] at hbound
  simpa only [Real.rpow_natCast] using hbound

/-- Boundedness excludes any coefficient with a same-side pair. -/
theorem same_side_pairing_coefficient_eq_zero
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (P : PerfectMatching (Fin k ⊕ Fin l)) (h : PermutationCycles P.1 × ℕ → E)
    (hh : Orthonormal ℂ h) (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c)
    (hpair : 0 < Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) :
    c P = 0 := by
  apply same_side_pairing_coefficient_zero (c P) ‖Y‖
    (Fintype.card (SourcePairClasses P)) (Fintype.card (TestPairClasses P)) hpair
  intro M _
  exact pairing_coefficient_growth_bound Y P h hh c hexp M

/-- Disjoint countable pools can be selected from one orthonormal sequence. -/
def cyclePoolIndex (P : PerfectMatching (Fin k ⊕ Fin l)) : PermutationCycles P.1 × ℕ → ℕ :=
  fun q => Nat.pair (Fintype.equivFin (PermutationCycles P.1) q.1).val q.2

theorem cyclePoolIndex_injective (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Function.Injective (cyclePoolIndex P) := by
  intro a b hab
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.mp hab
  apply Prod.ext ?_ h₂
  exact (Fintype.equivFin _).injective (Fin.ext h₁)

/-- A single infinite orthonormal family suffices for all matching tests. -/
theorem same_side_pairing_coefficient_eq_zero_of_sequence
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hpair : 0 < Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P)) :
    c P = 0 :=
  same_side_pairing_coefficient_eq_zero Y P (h ∘ cyclePoolIndex P)
    (hh.comp _ (cyclePoolIndex_injective P)) c
    (hexp.comp _ (cyclePoolIndex_injective P)) hpair

/-- Every nonzero coefficient must join source slots to test slots. -/
theorem nonzero_pairing_coefficient_isCrossPairing
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (P : PerfectMatching (Fin k ⊕ Fin l))
    (hc : c P ≠ 0) : IsCrossPairing P.1 := by
  have hz : Fintype.card (SourcePairClasses P) + Fintype.card (TestPairClasses P) = 0 := by
    by_contra hn
    exact hc (same_side_pairing_coefficient_eq_zero_of_sequence Y h hh c hexp P
      (Nat.pos_of_ne_zero hn))
  exact isCrossPairing_of_no_same_side P (by omega) (by omega)

/-- In unequal degrees every pairing coefficient vanishes. -/
theorem pairing_coefficients_zero_of_degrees_ne
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (hkl : k ≠ l) : c = 0 := by
  funext P
  by_contra hc
  exact hkl (degrees_eq_of_crossPairing P.1 P.2.1
    (nonzero_pairing_coefficient_isCrossPairing Y h hh c hexp P hc))

/-- The finite family of matchings which join source slots to test slots. -/
def crossPairings (k l : ℕ) : Finset (PerfectMatching (Fin k ⊕ Fin l)) := by
  classical
  exact Finset.univ.filter (fun P => IsCrossPairing P.1)

/-- The surviving expansion contains precisely cross pairings. -/
theorem label_pairing_expansion_restrict_cross
    (Y : CompletedTensorWord E k →L[ℂ] CompletedTensorWord E l)
    (h : ℕ → E) (hh : Orthonormal ℂ h)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (hexp : LabelPairingExpansion Y h c) (s : Fin k → ℕ) (t : Fin l → ℕ) :
    inner ℂ (completedTensorWord (fun i => h (t i)))
      (Y (completedTensorWord (fun i => h (s i)))) =
      ∑ P ∈ crossPairings k l, c P * pairingLabelKernel P (Sum.elim s t) := by
  classical
  rw [hexp]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro P _ hP
  have hc : c P = 0 := by
    by_contra hn
    exact hP (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      nonzero_pairing_coefficient_isCrossPairing Y h hh c hexp P hn⟩)
  rw [hc, zero_mul]

end KadisonSimilarity

end

end OAI
