import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier
import OAI.NumberTheory.Ostmann.Characters.AffineCoefficients

namespace OAI

/-!
# The affine action in the Fourier basis

On nonzero additive frequencies the affine action is a matrix whose entries
are additive character sums. Parseval bounds its squared matrix norm by
`p` times the coefficient energy. This is the finite matrix estimate in
the proof of the uniform Mellin bound in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def additiveCharacterSum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ξ : ZMod p) : ℂ :=
  ∑ b : ZMod p, f b * ZMod.stdAddChar (ξ * b)

theorem additiveCharacterSum_eq {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (ξ : ZMod p) :
    additiveCharacterSum f ξ = (p : ℂ) * additiveFourier f (-ξ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [additiveFourier_apply, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  simp only [additiveCharacterSum, mul_neg, neg_neg, mul_comm ξ]

theorem additiveCharacterSum_energy {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ ξ : ZMod p, ‖additiveCharacterSum f ξ‖ ^ 2) =
      (p : ℝ) * ∑ b : ZMod p, ‖f b‖ ^ 2 := by
  simp_rw [additiveCharacterSum_eq, norm_mul, Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have hreindex : (∑ ξ : ZMod p, ‖additiveFourier f (-ξ)‖ ^ 2) =
      ∑ ξ : ZMod p, ‖additiveFourier f ξ‖ ^ 2 :=
    (Equiv.neg (ZMod p)).bijective.sum_comp (fun ξ => ‖additiveFourier f ξ‖ ^ 2)
  rw [hreindex, additiveFourier_parseval]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp [hp]

theorem additiveCharacterSum_unit_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) :
    (∑ ξ : (ZMod p)ˣ, ‖additiveCharacterSum f ξ‖ ^ 2) ≤
      (p : ℝ) * ∑ b : ZMod p, ‖f b‖ ^ 2 := by
  classical
  rw [← additiveCharacterSum_energy]
  exact Finset.sum_le_sum_of_injOn (fun ξ : (ZMod p)ˣ => (ξ : ZMod p))
    Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun _ _ _ => sq_nonneg _)

/-- The input frequency is `ξ` and the output frequency is `η`. -/
noncomputable def affineFourierMatrix {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (η ξ : (ZMod p)ˣ) : ℂ :=
  additiveCharacterSum (fun b => c (η / ξ, b)) ξ

theorem affineFourierMatrix_energy_le {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) :
    (∑ η : (ZMod p)ˣ, ∑ ξ : (ZMod p)ˣ, ‖affineFourierMatrix c η ξ‖ ^ 2) ≤
      (p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2 := by
  classical
  have hreindex (ξ : (ZMod p)ˣ) :
      (∑ η : (ZMod p)ˣ, ‖affineFourierMatrix c η ξ‖ ^ 2) =
        ∑ a : (ZMod p)ˣ, ‖additiveCharacterSum (fun b => c (a, b)) ξ‖ ^ 2 := by
    calc
      _ = ∑ a : (ZMod p)ˣ, ‖affineFourierMatrix c (a * ξ) ξ‖ ^ 2 :=
        ((Equiv.mulRight ξ).bijective.sum_comp
          (fun η => ‖affineFourierMatrix c η ξ‖ ^ 2)).symm
      _ = _ := by simp only [affineFourierMatrix, mul_div_cancel_right]
  rw [Finset.sum_comm]
  simp_rw [hreindex]
  rw [Finset.sum_comm, Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => additiveCharacterSum_unit_energy_le (fun b => c (a, b)))

theorem complex_sum_mul_sq {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ j ∈ s, f j * g j‖ ^ 2 ≤
      (∑ j ∈ s, ‖f j‖ ^ 2) * ∑ j ∈ s, ‖g j‖ ^ 2 := by
  have hnorm : ‖∑ j ∈ s, f j * g j‖ ≤ ∑ j ∈ s, ‖f j‖ * ‖g j‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun j => f j * g j)
  have hn : 0 ≤ ∑ j ∈ s, ‖f j‖ * ‖g j‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun j => ‖f j‖) (fun j => ‖g j‖)
  nlinarith [norm_nonneg (∑ j ∈ s, f j * g j)]

theorem finite_matrix_energy_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℂ) (v : κ → ℂ) :
    (∑ i : ι, ‖∑ j : κ, A i j * v j‖ ^ 2) ≤
      (∑ i : ι, ∑ j : κ, ‖A i j‖ ^ 2) * ∑ j : κ, ‖v j‖ ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => complex_sum_mul_sq Finset.univ (A i) v)

theorem affineFourier_action_energy_bound {p : ℕ} [Fact p.Prime]
    (c : (ZMod p)ˣ × ZMod p → ℂ) (v : (ZMod p)ˣ → ℂ) :
    (∑ η : (ZMod p)ˣ, ‖∑ ξ : (ZMod p)ˣ, affineFourierMatrix c η ξ * v ξ‖ ^ 2) ≤
      ((p : ℝ) * ∑ ab : (ZMod p)ˣ × ZMod p, ‖c ab‖ ^ 2) *
        ∑ ξ : (ZMod p)ˣ, ‖v ξ‖ ^ 2 := by
  exact (finite_matrix_energy_bound (affineFourierMatrix c) v).trans
    (mul_le_mul_of_nonneg_right (affineFourierMatrix_energy_le c)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem affineFourier_collected_energy_bound {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (hG : (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ≤ (p : ℝ))
    (v : (ZMod p)ˣ → ℂ) :
    (∑ η : (ZMod p)ˣ,
      ‖∑ ξ : (ZMod p)ˣ, affineFourierMatrix (affineCoefficient G) η ξ * v ξ‖ ^ 2) ≤
      (3 / (p : ℝ)) * ∑ ξ : (ZMod p)ˣ, ‖v ξ‖ ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine (affineFourier_action_energy_bound (affineCoefficient G) v).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ (p : ℝ) * (3 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (affineCoefficient_sq_sum_le G hG) hp.le
    _ = 3 / (p : ℝ) := by field_simp [ne_of_gt hp]

end Ostmann

end OAI
