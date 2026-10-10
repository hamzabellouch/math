import OAI.Analysis.Cotype.BinaryRank
import OAI.Analysis.Cotype.BiasedFourier

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def xorCube (ε η : ι → Bool) : ι → Bool := fun i => Bool.xor (ε i) (η i)

@[simp] theorem sign_xor (a b : Bool) : sign (Bool.xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [Bool.xor]

omit [DecidableEq ι] in
theorem character_xor (P ε η : ι → Bool) :
    character P (xorCube ε η) = character P ε * character P η := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases P i <;> simp [xorCube]

def setIndex (s : Finset ι) : ι → Bool := fun i => decide (i ∈ s)

theorem character_setIndex (s : Finset ι) (ε : ι → Bool) :
    character (setIndex s) ε = ∏ i ∈ s, sign (ε i) := by
  simp [character, setIndex]

theorem character_rectangle (s : Finset ι) (t : Finset κ) (S : (ι × κ) → Bool) :
    character (rectangle s t) S = ∏ i ∈ s, ∏ j ∈ t, sign (S (i,j)) := by
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  unfold character
  rw [← Finset.prod_filter, he, Finset.prod_product]

def rowCube (σ : ι → Bool) : (ι × κ) → Bool := fun ij => σ ij.1

def columnCube (τ : κ → Bool) : (ι × κ) → Bool := fun ij => τ ij.2

theorem character_rectangle_row (s : Finset ι) (t : Finset κ)
    (ht : Odd t.card) (σ : ι → Bool) :
    character (rectangle s t) (rowCube σ) = character (setIndex s) σ := by
  rw [character_rectangle, character_setIndex]
  apply Finset.prod_congr rfl
  intro i _
  simp only [rowCube, Finset.prod_const]
  cases σ i <;> simp [ht.neg_one_pow]

theorem character_rectangle_column (s : Finset ι) (t : Finset κ)
    (hs : Odd s.card) (τ : κ → Bool) :
    character (rectangle s t) (columnCube τ) = character (setIndex t) τ := by
  rw [character_rectangle, Finset.prod_comm, character_setIndex]
  apply Finset.prod_congr rfl
  intro j _
  simp only [columnCube, Finset.prod_const]
  cases τ j <;> simp [hs.neg_one_pow]

theorem biasedExpectation_setIndex (s : Finset ι) (a : ℝ) :
    biasedExpectation (character (setIndex s)) (fun _ => a) = a ^ s.card := by
  rw [biasedExpectation_character]
  simp [setIndex]

theorem biasedExpectation_rectangle (s : Finset ι) (t : Finset κ) (c : ℝ) :
    biasedExpectation (character (rectangle s t)) (fun _ => c) = c ^ (s.card * t.card) := by
  rw [biasedExpectation_character]
  have he : Finset.univ.filter (fun ij => rectangle s t ij = true) = s ×ˢ t := by
    ext ij
    simp [rectangle]
  rw [← Finset.prod_filter, he]
  simp

def dampedSample (σ : ι → Bool) (τ : κ → Bool) (R : (ι × κ) → Bool) :
    (ι × κ) → Bool := xorCube (rowCube σ) (xorCube (columnCube τ) R)

def dampedExpectation (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) : ℝ :=
  biasedExpectation (fun σ => biasedExpectation (fun τ => biasedExpectation
    (fun R => f (dampedSample σ τ R)) (fun _ => c)) (fun _ => b)) (fun _ => a)

theorem dampedExpectation_bound {f : ((ι × κ) → Bool) → ℝ} {M a b c : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hf : ∀ S, |f S| ≤ M) :
    |dampedExpectation f a b c| ≤ M := by
  apply biasedExpectation_bound (fun _ => ha)
  intro σ
  apply biasedExpectation_bound (fun _ => hb)
  intro τ
  exact biasedExpectation_bound (fun _ => hc) (fun R => hf (dampedSample σ τ R))

theorem dampedExpectation_odd_rectangle (s : Finset ι) (t : Finset κ)
    (hs : Odd s.card) (ht : Odd t.card) (a b c : ℝ) :
    dampedExpectation (character (rectangle s t)) a b c =
      a ^ s.card * b ^ t.card * c ^ (s.card * t.card) := by
  unfold dampedExpectation dampedSample
  simp_rw [character_xor, character_rectangle_row s t ht, character_rectangle_column s t hs]
  simp_rw [biasedExpectation_const_mul, biasedExpectation_mul_const,
    biasedExpectation_rectangle, biasedExpectation_setIndex]
  ring

theorem dampedExpectation_fourier (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) :
    dampedExpectation f a b c =
      ∑ P, fourier f P * dampedExpectation (character P) a b c := by
  calc
    dampedExpectation f a b c = dampedExpectation
        (fun S => ∑ P, fourier f P * character P S) a b c := by
      congr 1
      funext S
      exact (fourier_inversion f S).symm
    _ = _ := by
      simp only [dampedExpectation]
      simp_rw [biasedExpectation_sum, biasedExpectation_const_mul]

end Cotype

end

end OAI
