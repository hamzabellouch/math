import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMinor
import Mathlib.Analysis.Normed.Operator.Bilinear

namespace OAI

/-! # Fixed-degree polynomial formulas in the independent amplitudes -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial
open scoped BigOperators

/-- The external parameter changes coefficients, but not the degree bound. -/
def HasPolynomialFormula {P : Type*} {m : ℕ} (f : P → (Fin m → ℝ) → ℝ) : Prop :=
  ∃ D : ℕ, ∀ a, ∃ p : MvPolynomial (Fin m) ℝ,
    p.totalDegree ≤ D ∧ ∀ x, MvPolynomial.eval x p = f a x

theorem hasPolynomialFormula_const {P : Type*} {m : ℕ} (c : P → ℝ) :
    HasPolynomialFormula (fun a (_ : Fin m → ℝ) => c a) :=
  ⟨0, fun a => ⟨C (c a), by simp, fun _ => by simp⟩⟩

theorem hasPolynomialFormula_coordinate {P : Type*} {m : ℕ} (j : Fin m) :
    HasPolynomialFormula (fun (_ : P) (x : Fin m → ℝ) => x j) :=
  ⟨1, fun _ => ⟨X j, by simp, fun _ => by simp⟩⟩

theorem HasPolynomialFormula.add {P : Type*} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x + g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p + q, (totalDegree_add p q).trans (max_le (by omega) (by omega)),
    fun x => by simp [he, he']⟩

theorem HasPolynomialFormula.mul {P : Type*} {m : ℕ} {f g : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialFormula f) (hg : HasPolynomialFormula g) :
    HasPolynomialFormula (fun a x => f a x * g a x) := by
  obtain ⟨D, hD⟩ := hf
  obtain ⟨E, hE⟩ := hg
  refine ⟨D + E, fun a => ?_⟩
  obtain ⟨p, hp, he⟩ := hD a
  obtain ⟨q, hq, he'⟩ := hE a
  exact ⟨p * q, (totalDegree_mul p q).trans (Nat.add_le_add hp hq),
    fun x => by simp [he, he']⟩

theorem hasPolynomialFormula_sum {P I : Type*} {m : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialFormula (f i)) :
    HasPolynomialFormula (fun a x => ∑ i ∈ s, f i a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasPolynomialFormula_const (P := P) (m := m) (fun _ => 0)
  | @insert i s hi ih =>
      have h₁ := hf i (Finset.mem_insert_self i s)
      have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using h₁.add h₂

def HasPolynomialCoordinates {P : Type*} {m n : ℕ}
    (f : P → (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ i, HasPolynomialFormula (fun a x => f a x i)

theorem HasPolynomialCoordinates.exists_uniform_polynomials
    {P : Type*} {m n : ℕ} {f : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) :
    ∃ D : ℕ, ∃ q : P → Fin n → MvPolynomial (Fin m) ℝ,
      (∀ a i, (q a i).totalDegree ≤ D) ∧
      ∀ a x i, MvPolynomial.eval x (q a i) = f a x i := by
  classical
  choose d hd using hf
  choose q hq hvalue using (fun a i => hd i a)
  refine ⟨∑ i, d i, q, ?_, fun a x i => hvalue a i x⟩
  intro a i
  exact (hq a i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i))

theorem hasPolynomialCoordinates_const {P : Type*} {m n : ℕ} (v : P → Fin n → ℝ) :
    HasPolynomialCoordinates (fun a (_ : Fin m → ℝ) => v a) :=
  fun i => hasPolynomialFormula_const (fun a => v a i)

theorem HasPolynomialCoordinates.smul {P : Type*} {m n : ℕ}
    {f : P → (Fin m → ℝ) → (Fin n → ℝ)} {t : P → (Fin m → ℝ) → ℝ}
    (hf : HasPolynomialCoordinates f) (ht : HasPolynomialFormula t) :
    HasPolynomialCoordinates (fun a x => t a x • f a x) :=
  fun i => ht.mul (hf i)

theorem bilinear_pi_expansion {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v w : Fin n → ℝ) :
    B v w = ∑ i : Fin n, ∑ j : Fin n,
      (v i * w j) • B (Pi.single i 1) (Pi.single j 1) := by
  calc
    B v w = B (∑ i, v i • Pi.single i 1) (∑ j, w j • Pi.single j 1) := by
      rw [← pi_eq_sum_univ' v, ← pi_eq_sum_univ' w]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]

theorem HasPolynomialCoordinates.bilinear {P : Type*} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun a x => B a (f a x) (g a x)) := by
  intro l
  have he : (fun a x => B a (f a x) (g a x) l) =
      (fun a x => ∑ i : Fin n, ∑ j : Fin n,
        (f a x i * g a x j) * B a (Pi.single i 1) (Pi.single j 1) l) := by
    funext a x
    rw [bilinear_pi_expansion]
    simp
  rw [he]
  apply hasPolynomialFormula_sum
  intro i _
  apply hasPolynomialFormula_sum
  intro j _
  exact ((hf i).mul (hg j)).mul (hasPolynomialFormula_const
    (fun a => B a (Pi.single i 1) (Pi.single j 1) l))

end PolycyclicRecognition

end

end OAI
