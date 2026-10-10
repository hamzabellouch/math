import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic

namespace OAI

/-!
# Fourier identities for the finite-tree obstruction

The scalar Fourier identities establish `lem:finite-fourier`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Finset RCLike

namespace TreeEdit.BinaryLower.FiniteFourier

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The normalized Fourier coefficient, with conjugation on the character. -/
def coefficient (f : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  RCLike.wInner RCLike.cWeight (χ : A → ℂ) f

omit [AddCommGroup A] in
lemma wInner_sum_left {ι : Type*} (s : Finset ι) (w : A → ℝ)
    (f : ι → A → ℂ) (g : A → ℂ) :
    RCLike.wInner (𝕜 := ℂ) w (∑ i ∈ s, f i) g =
      ∑ i ∈ s, RCLike.wInner (𝕜 := ℂ) w (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, RCLike.wInner_add_left, ih]

omit [AddCommGroup A] in
lemma wInner_sum_right {ι : Type*} (s : Finset ι) (w : A → ℝ)
    (f : A → ℂ) (g : ι → A → ℂ) :
    RCLike.wInner (𝕜 := ℂ) w f (∑ i ∈ s, g i) =
      ∑ i ∈ s, RCLike.wInner (𝕜 := ℂ) w f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, RCLike.wInner_add_right, ih]

lemma coefficient_eq_repr (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient f χ = (AddChar.complexBasis A).repr f χ := by
  classical
  unfold coefficient
  conv_lhs => arg 3; rw [← (AddChar.complexBasis A).sum_repr f]
  rw [wInner_sum_right]
  simp [RCLike.wInner_smul_right, AddChar.wInner_cWeight_eq_boole]

lemma expansion (f : A → ℂ) :
    (∑ χ : AddChar A ℂ, coefficient f χ • (χ : A → ℂ)) = f := by
  simp_rw [coefficient_eq_repr, ← AddChar.complexBasis_apply]
  exact (AddChar.complexBasis A).sum_repr f

lemma parseval_complex (f : A → ℂ) :
    RCLike.wInner RCLike.cWeight f f =
      ∑ χ : AddChar A ℂ, star (coefficient f χ) * coefficient f χ := by
  conv_lhs => arg 2; rw [← expansion f]
  rw [wInner_sum_left]
  simp only [RCLike.wInner_smul_left, smul_eq_mul, coefficient]

lemma parseval (f : A → ℂ) :
    (∑ x : A, ‖f x‖ ^ 2) / Fintype.card A =
      ∑ χ : AddChar A ℂ, ‖coefficient f χ‖ ^ 2 := by
  have h := congrArg Complex.re (parseval_complex f)
  simpa [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
    RCLike.inner_apply, Complex.div_ofReal_re,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow] using h

lemma coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → A → ℂ)
    (χ : AddChar A ℂ) :
    coefficient (∑ i ∈ s, f i) χ = ∑ i ∈ s, coefficient (f i) χ := by
  exact wInner_sum_right s _ _ _

lemma coefficient_smul (a : ℂ) (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient (a • f) χ = a * coefficient f χ := by
  exact RCLike.wInner_smul_right a _ _ _

lemma coefficient_char (ψ χ : AddChar A ℂ) :
    coefficient (ψ : A → ℂ) χ = if χ = ψ then 1 else 0 :=
  AddChar.wInner_cWeight_eq_boole χ ψ

lemma displacement_expansion (f : A → ℂ) (z : A) :
    (fun x => f (x + z) - f x) =
      ∑ χ : AddChar A ℂ, ((χ z - 1) * coefficient f χ) • (χ : A → ℂ) := by
  funext x
  have h₁ := congrFun (expansion f) (x + z)
  have h₂ := congrFun (expansion f) x
  rw [← h₁, ← h₂]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  rw [AddChar.map_add_eq_mul]
  ring

lemma coefficient_displacement (f : A → ℂ) (z : A) (χ : AddChar A ℂ) :
    coefficient (fun x => f (x + z) - f x) χ =
      (χ z - 1) * coefficient f χ := by
  classical
  rw [displacement_expansion, coefficient_sum]
  simp [coefficient_smul, coefficient_char]

/-- Parseval for the displacement by a fixed group element. -/
lemma displacement_parseval (f : A → ℂ) (z : A) :
    (∑ x : A, ‖f (x + z) - f x‖ ^ 2) / Fintype.card A =
      ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ‖coefficient f χ‖ ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [coefficient_displacement, norm_mul, mul_pow, norm_sub_rev]

/-- Indicator differences have equal absolute value and squared complex norm. -/
lemma indicator_difference (u v : ℝ) (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1) :
    |u - v| = ‖(u : ℂ) - (v : ℂ)‖ ^ 2 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> norm_num

/-- The identity for one zero-one valued cut. -/
lemma indicator_displacement (U : A → ℝ) (hU : ∀ x, U x = 0 ∨ U x = 1) (z : A) :
    (∑ x : A, |U (x + z) - U x|) / Fintype.card A =
      ∑ χ : AddChar A ℂ,
        ‖1 - χ z‖ ^ 2 * ‖coefficient (fun x => (U x : ℂ)) χ‖ ^ 2 := by
  simp_rw [indicator_difference _ _ (hU _) (hU _)]
  exact displacement_parseval (fun x => (U x : ℂ)) z

/-- Finite nonnegative cut combinations have a nonnegative Fourier representation. -/
theorem exists_weights_of_cutRepresentation {ι : Type*} [Fintype ι]
    (ρ : A → A → ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (U : ι → A → ℝ) (hU : ∀ i x, U i x = 0 ∨ U i x = 1)
    (hρ : ∀ x y, ρ x y = ∑ i : ι, a i * |U i x - U i y|) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z : A, (∑ x : A, ρ x (x + z)) / Fintype.card A =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by
  refine ⟨fun χ => ∑ i : ι, a i * ‖coefficient (fun x => (U i x : ℂ)) χ‖ ^ 2,
    fun χ => Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sq_nonneg _)), ?_⟩
  intro z
  simp_rw [hρ]
  rw [Finset.sum_comm, Finset.sum_div]
  calc
    _ = ∑ i : ι, a i * ((∑ x : A, |U i (x + z) - U i x|) / Fintype.card A) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, mul_div_assoc]
      congr 2
      apply Finset.sum_congr rfl
      intro x _
      exact abs_sub_comm _ _
    _ = ∑ i : ι, a i * (∑ χ : AddChar A ℂ,
        ‖1 - χ z‖ ^ 2 * ‖coefficient (fun x => (U i x : ℂ)) χ‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [indicator_displacement _ (hU i) z]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro i _
      ring

end TreeEdit.BinaryLower.FiniteFourier

end

end OAI
