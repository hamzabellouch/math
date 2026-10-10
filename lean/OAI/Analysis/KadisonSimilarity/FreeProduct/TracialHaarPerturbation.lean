import OAI.Analysis.KadisonSimilarity.Representation.SimultaneousSymmetrization

namespace OAI

/-! Quantitative proximity in Haar symmetrization. The finite-factor argument
uses a cluster point within the original scalar commutator bound. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap Filter ContinuousLinearMapWOT
open scoped Topology

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- A weak integral stays in every operator norm ball containing its field. -/
theorem norm_weakOperatorIntegral_sub_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ g, ‖A g - T‖ ≤ δ) :
    ‖weakOperatorIntegral μ A hA R hbound - T‖ ≤ δ := by
  apply norm_le_of_matrix_coefficients _ hδ
  intro x y
  rw [← norm_inner_symm]
  have he : inner ℂ ((weakOperatorIntegral μ A hA R hbound - T) x) y =
      ∫ g, inner ℂ ((A g - T) x) y ∂μ := by
    simp only [_root_.sub_apply, inner_sub_left, weakOperatorIntegral_inner]
    rw [integral_sub (hA x y) (integrable_const _), integral_const]
    simp
  rw [he]
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ ((A g - T) x) y‖ ≤ δ * ‖x‖ * ‖y‖ :=
    Eventually.of_forall fun g => calc
      _ ≤ ‖(A g - T) x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖A g - T‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((A g - T).le_opNorm x) (norm_nonneg y)
      _ ≤ δ * ‖x‖ * ‖y‖ := by gcongr; exact hclose g
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [probReal_univ, mul_one] at hi
  convert hi using 1
  ring

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]

omit [MeasurableSpace X] [IsProbabilityMeasure μ] [CompleteSpace H]
  [MeasurableSpace Γ] [MeasurableMul Γ] in
/-- Conjugating by a contractive group representation moves an operator by
at most its commutator with the group element. -/
theorem norm_unitaryConjugate_sub_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) {δ : ℝ}
    (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ δ) (g : Γ) :
    ‖unitaryConjugate U T g - T‖ ≤ δ := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have he : T - unitaryConjugate U T g = commutator T (U g) * U g⁻¹ := by
    simp only [unitaryConjugate, commutator, sub_mul, mul_assoc, hi, mul_one]
  rw [norm_sub_rev, he]
  calc
    _ ≤ ‖commutator T (U g)‖ * ‖U g⁻¹‖ := norm_mul_le _ _
    _ ≤ δ * 1 := mul_le_mul (hcomm g) (hU _) (norm_nonneg _)
      ((norm_nonneg _).trans (hcomm g))
    _ = δ := mul_one _

omit [MeasurableMul Γ] in
/-- The Haar average is close to the original operator by the scalar bound. -/
theorem norm_haarTwirl_sub_le (ν : Measure Γ) [IsProbabilityMeasure ν]
    (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable ν (unitaryConjugate U T))
    {δ : ℝ} (hδ : 0 ≤ δ) (hcomm : ∀ g, ‖commutator T (U g)‖ ≤ δ) :
    ‖haarTwirl ν U hU T hI - T‖ ≤ δ :=
  norm_weakOperatorIntegral_sub_le ν _ hI _ _ T hδ
    (norm_unitaryConjugate_sub_le U hU T hcomm)

/-- The norm perturbation controls the full scalar commutator seminorm. -/
theorem scalarCommutatorNorm_le_of_close (P : VonNeumannAlgebra H)
    (S T : H →L[ℂ] H) {δ : ℝ} (hclose : ‖S - T‖ ≤ δ) :
    scalarCommutatorNorm P S ≤ scalarCommutatorNorm P T + 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hclose
  have hT := scalarCommutatorNorm_nonneg P T
  apply (scalarCommutatorNorm_le_iff P S (by positivity)).mpr
  intro a ha
  have h := norm_commutator_le_of_approx S T a
    (norm_commutator_le_scalarCommutatorNorm P T a ha) hclose
  nlinarith

section IncreasingGroups

variable {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, MeasurableSpace (G n)]
  [∀ n, MeasurableMul (G n)] (ν : ∀ n, Measure (G n))
  [∀ n, IsProbabilityMeasure (ν n)] [∀ n, (ν n).IsMulLeftInvariant]

/-- Increasing Haar averages give a single invariant operator within the
original commutator bound. There is no invariant operator among the inputs. -/
theorem exists_simultaneously_symmetrized_close
    (U : ∀ n, G n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (embedding : ∀ n m, n ≤ m → G n → G m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (ν n) (unitaryConjugate (U n) T))
    {δ : ℝ} (hδ : 0 ≤ δ) (hcomm : ∀ n g, ‖commutator T (U n g)‖ ≤ δ) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ ‖T‖ ∧ ‖S - T‖ ≤ δ ∧
      ∀ n g, commutator S (U n g) = 0 := by
  let averages : ℕ → H →L[ℂ] H := fun n => haarTwirl (ν n) (U n) (hU n) T (hI n)
  obtain ⟨S, hS, hc⟩ := exists_weakOperator_cluster averages (norm_nonneg T)
    (fun n => norm_haarTwirl_le (ν n) (U n) (hU n) T (hI n))
  refine ⟨S, hS, ?_, ?_⟩
  · apply norm_sub_le_of_weakOperator_cluster averages S T hc hδ
    exact Eventually.of_forall fun n =>
      norm_haarTwirl_sub_le (ν n) (U n) (hU n) T (hI n) hδ (hcomm n)
  · intro n g
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_cluster averages S (U n g) hc (le_refl 0)
    filter_upwards [eventually_ge_atTop n] with m hm
    have he := haarTwirl_commute (ν m) (U m) (hU m) T (hI m) (embedding n m hm g)
    rw [hcompat] at he
    simp only [averages, he, norm_zero, le_refl]

/-- The finite-factor averaging step, including the factor-three scalar
commutator bound used before passage to the ultrapower. -/
theorem exists_scalar_symmetrization (P : VonNeumannAlgebra H)
    (U : ∀ n, G n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (hmem : ∀ n g, U n g ∈ P)
    (embedding : ∀ n m, n ≤ m → G n → G m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (ν n) (unitaryConjugate (U n) T)) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ ‖T‖ ∧
      ‖S - T‖ ≤ scalarCommutatorNorm P T ∧
      scalarCommutatorNorm P S ≤ 3 * scalarCommutatorNorm P T ∧
      ∀ n g, commutator S (U n g) = 0 := by
  obtain ⟨S, hS, hclose, hc⟩ := exists_simultaneously_symmetrized_close ν U hU
    embedding hcompat T hI (scalarCommutatorNorm_nonneg P T) (fun n g =>
      (norm_commutator_le_scalarCommutatorNorm P T _ (hmem n g)).trans
        (mul_le_of_le_one_right (scalarCommutatorNorm_nonneg P T) (hU n g)))
  refine ⟨S, hS, hclose, ?_, hc⟩
  have hb := scalarCommutatorNorm_le_of_close P S T hclose
  linarith

end IncreasingGroups
end KadisonSimilarity

end

end OAI
