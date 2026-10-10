import OAI.Analysis.KadisonSimilarity.Tensor.InvariantCoefficients
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

namespace OAI

/-!
# Matrix-unit isolation of invariant-tensor coefficients

The permutation contractions are given by their coordinate sums. Their
normalization is the number of cycles, including fixed points. We prove the
matrix-unit isolation and uniqueness steps in the invariant-intertwiner
argument. Schur--Weyl spanning is expressed as a multilinear-form property.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The coordinate formula for the trace contraction of a permutation tensor.
Each index follows the successor convention in the manuscript. -/
def permutationContraction (π : Equiv.Perm ι) (v : ι → Matrix α α ℂ) : ℂ :=
  ∑ f : ι → α, ∏ i, v i (f i) (f (π i))

/-- A matrix unit with row `a` and column `b`. -/
def tensorMatrixUnit (a b : α) : Matrix α α ℂ :=
  fun r c => if r = a ∧ c = b then 1 else 0

omit [Fintype α] in
@[simp] theorem tensorMatrixUnit_apply (a b r c : α) :
    tensorMatrixUnit a b r c = if r = a ∧ c = b then 1 else 0 := rfl

/-- Distinct labels assigned to the vertices of a permutation give its test
tuple of matrix units. -/
def permutationTest (j : ι → α) (π : Equiv.Perm ι) : ι → Matrix α α ℂ :=
  fun i => tensorMatrixUnit (j i) (j (π i))

omit [Fintype α] in
private theorem contraction_test_summand (j : ι → α) (hj : Function.Injective j)
    (π ρ : Equiv.Perm ι) (f : ι → α) :
    (∏ i, permutationTest j π i (f i) (f (ρ i))) =
      if f = j ∧ ρ = π then 1 else 0 := by
  classical
  by_cases hf : f = j
  · subst f
    by_cases hρ : ρ = π
    · subst ρ
      simp [permutationTest]
    · have hdiff : ∃ i, ρ i ≠ π i := by
        by_contra! h
        exact hρ (Equiv.ext h)
      obtain ⟨i, hi⟩ := hdiff
      simp only [hρ]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hij : j (ρ i) ≠ j (π i) := fun h => hi (hj h)
      simp [permutationTest, hij]
  · have hdiff : ∃ i, f i ≠ j i := by
      by_contra! h
      exact hf (funext h)
    obtain ⟨i, hi⟩ := hdiff
    simp only [hf, false_and, ↓reduceIte]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [permutationTest, hi]

/-- A matrix-unit tuple isolates exactly its prescribed permutation. This
proves the independence assertion, independently of Schur--Weyl duality. -/
theorem permutationContraction_test (j : ι → α) (hj : Function.Injective j)
    (π ρ : Equiv.Perm ι) :
    permutationContraction ρ (permutationTest j π) = if ρ = π then 1 else 0 := by
  classical
  simp only [permutationContraction, contraction_test_summand j hj]
  by_cases hρ : ρ = π <;> simp [hρ]

/-- The number of cycles of a permutation, with singleton cycles included. -/
def permutationCycleCount (π : Equiv.Perm ι) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid π))

/-- Normalizing each cycle trace by the matrix dimension gives the coordinate
formula for the normalized cycle-trace form `Φ_π` in the paper. -/
def normalizedPermutationContraction (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) : ℂ :=
  (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π * permutationContraction π v

theorem normalizedPermutationContraction_test
    (j : ι → α) (hj : Function.Injective j) (π ρ : Equiv.Perm ι) :
    normalizedPermutationContraction ρ (permutationTest j π) =
      if ρ = π then (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π else 0 := by
  classical
  rw [normalizedPermutationContraction, permutationContraction_test j hj]
  split_ifs with h <;> simp [h]

/-- Evaluation at the associated matrix units recovers one coefficient of
any expansion in normalized permutation contractions. -/
theorem normalizedPermutationContraction_sum_test
    (j : ι → α) (hj : Function.Injective j) (π : Equiv.Perm ι)
    (c : Equiv.Perm ι → ℂ) :
    (∑ ρ, c ρ * normalizedPermutationContraction ρ (permutationTest j π)) =
      c π * (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π := by
  classical
  simp [normalizedPermutationContraction_test j hj]

/-- In the stable range, expansion coefficients are unique. This is the
specific independence step needed when comparing nested matrix stages. -/
theorem normalizedPermutationContraction_coefficients_unique
    [Nonempty α] (j : ι → α) (hj : Function.Injective j)
    (c d : Equiv.Perm ι → ℂ)
    (heq : ∀ v : ι → Matrix α α ℂ,
      (∑ π, c π * normalizedPermutationContraction π v) =
        ∑ π, d π * normalizedPermutationContraction π v) : c = d := by
  funext π
  have h := heq (permutationTest j π)
  rw [normalizedPermutationContraction_sum_test j hj,
    normalizedPermutationContraction_sum_test j hj] at h
  exact mul_right_cancel₀ (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr
    Fintype.card_ne_zero))) h

/-- The contraction is multilinear in its matrix variables. -/
def permutationContractionMultilinear (π : Equiv.Perm ι) :
    MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ :=
  ∑ f : ι → α, (MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    (fun i => Matrix.entryLinearMap ℂ ℂ (f i) (f (π i)))

omit [DecidableEq α] in
@[simp] theorem permutationContractionMultilinear_apply (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) :
    permutationContractionMultilinear π v = permutationContraction π v := by
  simp [permutationContractionMultilinear, permutationContraction]

/-- The bundled normalized cycle-trace form. -/
def normalizedPermutationMultilinear (π : Equiv.Perm ι) :
    MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ :=
  ((Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π) •
    permutationContractionMultilinear π

omit [DecidableEq α] in
@[simp] theorem normalizedPermutationMultilinear_apply (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) :
    normalizedPermutationMultilinear π v = normalizedPermutationContraction π v := by
  simp [normalizedPermutationMultilinear, normalizedPermutationContraction]

/-- Invariance under simultaneous conjugation of all matrix arguments. -/
def UnitaryConjugationInvariant
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ) : Prop :=
  ∀ (u : Matrix.unitaryGroup α ℂ) (v : ι → Matrix α α ℂ),
    F (fun i => (u : Matrix α α ℂ) * v i * star (u : Matrix α α ℂ)) = F v

/-- The finite-dimensional consequence of Schur--Weyl duality used in the
paper. Source: Grinko--Ozols, *Linear programming with unitary-equivariant
constraints*, Comm. Math. Phys. 405 (2024), article 278, Theorem 3.1, combined
with the nondegenerate matrix trace pairing. Matrix-unit isolation and
uniqueness establish independence in the stable range. -/
def SchurWeylMultilinearSpanning (ι α : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : Prop :=
  ∀ F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ,
    UnitaryConjugationInvariant F →
    ∃ c : Equiv.Perm ι → ℂ, ∀ v,
      F v = ∑ π, c π * normalizedPermutationContraction π v

/-- The stable-range uniqueness part of the invariant expansion follows from
the explicit tests, and is not a second published assumption. -/
theorem existsUnique_invariant_expansion [Nonempty α]
    (spanning : SchurWeylMultilinearSpanning ι α)
    (j : ι → α) (hj : Function.Injective j)
    (F : MultilinearMap ℂ (fun _ : ι => Matrix α α ℂ) ℂ)
    (hF : UnitaryConjugationInvariant F) :
    ∃! c : Equiv.Perm ι → ℂ, ∀ v,
      F v = ∑ π, c π * normalizedPermutationContraction π v := by
  obtain ⟨c, hc⟩ := spanning F hF
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact normalizedPermutationContraction_coefficients_unique j hj d c
    (fun v => (hd v).symm.trans (hc v))

/-- The norm of the isolated coefficient has exactly the decay factor used
in the endpoint estimate. -/
theorem norm_normalizedPermutationContraction_sum_test
    (j : ι → α) (hj : Function.Injective j) (π : Equiv.Perm ι)
    (c : Equiv.Perm ι → ℂ) :
    ‖∑ ρ, c ρ * normalizedPermutationContraction ρ (permutationTest j π)‖ =
      ‖c π‖ * (Fintype.card α : ℝ) ^ (-(permutationCycleCount π : ℝ)) := by
  rw [normalizedPermutationContraction_sum_test j hj, norm_mul, norm_pow,
    norm_inv, Complex.norm_natCast, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

/-- Passing the actual matrix-stage test estimate to the coefficient limit
removes every permutation below the cycle threshold. The finite-stage forms
and their test estimates are explicit local data; the invariant conclusion
is not assumed. -/
theorem cycle_coefficient_zero_of_matrix_stage_tests
    (p k l : ℕ) (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (hmp : ∀ s, p ≤ m s)
    (hmTop : Filter.Tendsto (fun s => (m s : ℝ)) Filter.atTop Filter.atTop)
    (c : Equiv.Perm (Fin p) → ℂ) (π : Equiv.Perm (Fin p)) (C : ℝ)
    (hfew : (permutationCycleCount π : ℝ) < 1 + ((k : ℝ) + l) / 2)
    (htest : ∀ s,
      ‖∑ ρ, c ρ * normalizedPermutationContraction ρ
          (permutationTest (Fin.castLE (hmp s)) π)‖ ≤
        C * (m s : ℝ) ^ (-1 - ((k : ℝ) + l) / 2)) : c π = 0 := by
  apply cycle_coefficient_zero (fun s => (m s : ℝ))
    (fun s => by exact_mod_cast hm s) hmTop k l (permutationCycleCount π) (c π) C hfew
  intro s
  simpa only [norm_normalizedPermutationContraction_sum_test _ (Fin.castLE_injective _),
    Fintype.card_fin] using htest s

section BlockAmplification

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Labels constant along each cycle are exactly functions on the cycle
quotient. This is the counting mechanism behind trace normalization. -/
abbrev CycleConstantLabelings (π : Equiv.Perm ι) (β : Type*) :=
  {f : ι → β // ∀ i, f (π i) = f i}

omit [DecidableEq ι] [Fintype β] [DecidableEq β] in
private theorem cycleConstantLabelings_eq_of_sameCycle (π : Equiv.Perm ι)
    (f : CycleConstantLabelings π β) {i j : ι} (h : π.SameCycle i j) : f.1 i = f.1 j := by
  have hit (n : ℕ) (i : ι) : f.1 ((π ^ n) i) = f.1 i := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, f.2]
      exact ih
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact (hit n i).symm

/-- A concrete equivalence, rather than an assumed formula for orbit counts. -/
def cycleConstantLabelingsEquiv (π : Equiv.Perm ι) :
    CycleConstantLabelings π β ≃ (Quotient (Equiv.Perm.SameCycle.setoid π) → β) where
  toFun f := Quotient.lift f.1 (fun _ _ h => cycleConstantLabelings_eq_of_sameCycle π f h)
  invFun g := ⟨fun i => g ⟦i⟧, fun i => congrArg g (Quotient.sound
    ((show π.SameCycle i (π i) from ⟨1, by simp⟩).symm))⟩
  left_inv _ := rfl
  right_inv g := by
    funext q
    induction q using Quotient.inductionOn
    rfl

theorem card_cycleConstantLabelings (π : Equiv.Perm ι) :
    Fintype.card (CycleConstantLabelings π β) =
      Fintype.card β ^ permutationCycleCount π := by
  classical
  let : Fintype (Quotient (Equiv.Perm.SameCycle.setoid π)) := Fintype.ofFinite _
  rw [Fintype.card_congr (cycleConstantLabelingsEquiv (β := β) π), Fintype.card_fun]
  rw [permutationCycleCount, Nat.card_eq_fintype_card]

/-- The usual unital inclusion `M_α → M_(α×β)`, sending a matrix to repeated
diagonal blocks (equivalently, tensoring by the identity matrix). -/
def repeatedBlockMatrix (v : Matrix α α ℂ) : Matrix (α × β) (α × β) ℂ :=
  fun r c => if r.2 = c.2 then v r.1 c.1 else 0

omit [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype β] in
private theorem repeatedBlockMatrix_contraction_summand (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) (f : ι → α) (g : ι → β) :
    (∏ i, repeatedBlockMatrix (β := β) (v i) (f i, g i) (f (π i), g (π i))) =
      (∏ i, v i (f i) (f (π i))) * if ∀ i, g (π i) = g i then 1 else 0 := by
  classical
  by_cases h : ∀ i, g (π i) = g i
  · rw [ite_eq_left h, mul_one]
    apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_left (h i).symm
  · obtain ⟨i, hi⟩ := not_forall.mp h
    simp only [h, ↓reduceIte, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [repeatedBlockMatrix, Ne.symm hi]

omit [DecidableEq α] in
/-- Under block repetition, an unnormalized contraction gains one factor of
the number of blocks for each cycle. -/
theorem permutationContraction_repeatedBlockMatrix (π : Equiv.Perm ι)
    (v : ι → Matrix α α ℂ) :
    permutationContraction π (fun i => repeatedBlockMatrix (β := β) (v i)) =
      permutationContraction π v * (Fintype.card β : ℂ) ^ permutationCycleCount π := by
  classical
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => α) (fun _ => β))
    _ (fun fg => (∏ i, v i (fg.1 i) (fg.1 (π i))) *
      if ∀ i, fg.2 (π i) = fg.2 i then 1 else 0)]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul (Finset.univ : Finset (ι → α))
      (fun f : ι → α => ∏ i, v i (f i) (f (π i)))
      (∑ g : ι → β, if ∀ i, g (π i) = g i then (1 : ℂ) else 0)]
    congr 1
    rw [Finset.sum_boole, ← Fintype.card_subtype]
    exact_mod_cast card_cycleConstantLabelings (β := β) π
  · intro f
    exact repeatedBlockMatrix_contraction_summand π v (fun i => (f i).1)
      (fun i => (f i).2)

omit [DecidableEq α] in
/-- Normalized cycle contractions are compatible with full matrix stage
inclusions. The cycle-count factors cancel exactly. -/
theorem normalizedPermutationContraction_repeatedBlockMatrix [Nonempty β]
    (π : Equiv.Perm ι) (v : ι → Matrix α α ℂ) :
    normalizedPermutationContraction π (fun i => repeatedBlockMatrix (β := β) (v i)) =
      normalizedPermutationContraction π v := by
  rw [normalizedPermutationContraction, permutationContraction_repeatedBlockMatrix,
    normalizedPermutationContraction, Fintype.card_prod, Nat.cast_mul, mul_inv, mul_pow]
  have hb : (Fintype.card β : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (Fintype.card α : ℂ)⁻¹ ^ permutationCycleCount π * permutationContraction π v *
      ((Fintype.card β : ℂ)⁻¹ ^ permutationCycleCount π *
        (Fintype.card β : ℂ) ^ permutationCycleCount π) := by ring
    _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hb, one_pow, mul_one]

/-- Compatibility of the forms between two matrix stages forces their
coefficients to agree. No stability assumption on coefficients is needed. -/
theorem invariant_coefficients_stable_under_blocks [Nonempty α] [Nonempty β]
    (j : ι → α) (hj : Function.Injective j)
    (F : (ι → Matrix α α ℂ) → ℂ)
    (G : (ι → Matrix (α × β) (α × β) ℂ) → ℂ)
    (c d : Equiv.Perm ι → ℂ)
    (hc : ∀ v, F v = ∑ π, c π * normalizedPermutationContraction π v)
    (hd : ∀ v, G v = ∑ π, d π * normalizedPermutationContraction π v)
    (hFG : ∀ v, G (fun i => repeatedBlockMatrix (v i)) = F v) : c = d := by
  apply normalizedPermutationContraction_coefficients_unique j hj
  intro v
  rw [← hc v, ← hFG v, hd]
  simp only [normalizedPermutationContraction_repeatedBlockMatrix]

end BlockAmplification

end KadisonSimilarity

end

end OAI
