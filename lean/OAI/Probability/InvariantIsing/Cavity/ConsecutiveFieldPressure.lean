import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockPrior
import OAI.Probability.InvariantIsing.Fields.SpinGroupSlice
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressure

namespace OAI

/-! A repeated constrained block contributes its exact deterministic
external-field term to the full pressure. -/
noncomputable section
open IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

def consecutiveBlockField {n : ℕ} (K : ℕ) (b : Fin n → ℝ) : Fin (K*n) → ℝ :=
  fun i => b (finProdFinEquiv.symm i).2

lemma fieldEnergy_consecutive_constraint {n K : ℕ} (C : Finset (Spin n))
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    {σ : Spin (K*n)} (hσ : σ ∈ consecutiveBlockConstraint n K C) :
    fieldEnergy (consecutiveBlockField K b) σ=(K : ℝ)*M := by
  rw [fieldEnergy, ← Equiv.sum_comp (finProdFinEquiv : Fin K × Fin n ≃ Fin (K*n))]
  simp only [consecutiveBlockField, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have hb := (mem_consecutiveBlockConstraint C σ).mp hσ
  have he (j : Fin K) : (∑ i : Fin n, b i*spinValue (σ (finProdFinEquiv (j,i))))=M :=
    hM _ (hb j)
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma restrictedSpinLog_consecutive_field {n K : ℕ} (C : Finset (Spin n)) (hC : C.Nonempty)
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    (H : Spin (K*n) → ℝ) :
    restrictedSpinLog (consecutiveBlockConstraint n K C)
      (fun σ => H σ+fieldEnergy (consecutiveBlockField K b) σ) =
      restrictedSpinLog (consecutiveBlockConstraint n K C) H+(K : ℝ)*M := by
  rw [← restrictedSpinLog_add_const _ (consecutiveBlockConstraint_nonempty C hC)]
  unfold restrictedSpinLog
  congr 2
  apply Finset.sum_congr rfl
  intro σ hσ
  dsimp only
  rw [fieldEnergy_consecutive_constraint C b M hM hσ]

lemma spinGroupFieldConstant_magnetization {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (b γ mag : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a)
    (hk : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2)) :
    spinGroupFieldConstant group k b=(n : ℝ)*∑ a, γ a*b a*mag a := by
  unfold spinGroupFieldConstant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hk, hcount]
  ring

lemma consecutive_field_pressure_lower {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (b : Fin n → ℝ) (M : ℝ) (hM : ∀ σ ∈ C, fieldEnergy b σ=M)
    (eig : Fin (K*n) → ℝ) (U : Rotation (K*n)) :
    restrictedRotatedPressure (consecutiveBlockConstraint n K C) eig U (fun _ => 0)+M/n ≤
      rotatedPressure eig U (consecutiveBlockField K b) := by
  have hb := restrictedRotatedPressure_le_full (consecutiveBlockConstraint n K C)
    (consecutiveBlockConstraint_nonempty C hC) eig U (consecutiveBlockField K b)
  rw [restrictedRotatedPressure, restrictedSpinLog_consecutive_field C hC b M hM] at hb
  have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hKz : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have he : ((K*n : ℕ) : ℝ)⁻¹*(restrictedSpinLog (consecutiveBlockConstraint n K C)
      (fun σ => rotatedEnergy eig U σ)+(K : ℝ)*M) =
      restrictedRotatedPressure (consecutiveBlockConstraint n K C) eig U (fun _ => 0)+M/n := by
    simp only [restrictedRotatedPressure, fieldEnergy, zero_mul, Finset.sum_const_zero,
      add_zero, Nat.cast_mul]
    field_simp
  exact he ▸ hb

end InvariantIsing

end

end OAI
