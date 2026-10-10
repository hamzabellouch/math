import OAI.Analysis.Laughlin.Tensor.ExteriorIsometry
import OAI.Analysis.Laughlin.Tensor.PairContraction

namespace OAI

/-! Exact one- and two-body matrix elements of the actual CAR operators on
normalized antisymmetric coefficient tensors. These are the finite algebraic
identities used to compare Slater integrals with occupation-space matrices. -/

noncomputable section
namespace ContinuumCoulomb.FockTensorCompression
open Laughlin Laughlin.Fock
open scoped BigOperators

private lemma annihilate_create_inner (Q : ℕ) (i : Fin (Q + 1)) (x y : Space Q) :
    occupationInner Q x (create i y) = occupationInner Q (annihilate i x) y := by
  have h := congrArg star (create_annihilate_adjoint Q i y x)
  simpa only [occupationInner_star] using h

private lemma factorial_normalizer (n : ℕ) :
    star ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) * (n.factorial : ℂ) = 1 := by
  have hp : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hs : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hp))
  have he : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← he]
  field_simp

lemma annihilation_inner (n Q : ℕ) (ψ φ : State (n + 1) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j : Fin (Q + 1)) :
    occupationInner Q
      (annihilate i (normalizedTensorExterior (n + 1) Q ψ))
      (annihilate j (normalizedTensorExterior (n + 1) Q φ)) =
      (n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  simp only [normalizedTensorExterior, map_smul, annihilate_tensorExterior n Q ψ hψ,
    annihilate_tensorExterior n Q φ hφ, occupationInner_smul_left, occupationInner_smul_right,
    tensorExterior_inner n Q _ _ (antisymmetric_cons hφ j)]
  have hn := factorial_normalizer (n + 1)
  have hf : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal,
    map_natCast, map_add, map_one] at *
  calc
    _ = (star ((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ : ℂ) *
      ((n + 1).factorial : ℂ)) *
      ((n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a)) := by
        rw [hf]
        simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
        ring
    _ = _ := by
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [hn, one_mul]

lemma oneBody_inner (n Q : ℕ) (ψ φ : State (n + 1) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j : Fin (Q + 1)) :
    occupationInner Q (normalizedTensorExterior (n + 1) Q ψ)
      (create i (annihilate j (normalizedTensorExterior (n + 1) Q φ))) =
      (n + 1 : ℂ) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i a)) * φ (Fin.cons j a) := by
  rw [annihilate_create_inner]
  exact annihilation_inner n Q ψ φ hψ hφ i j

lemma pair_annihilation_inner (n Q : ℕ) (ψ φ : State (n + 2) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j k l : Fin (Q + 1)) :
    occupationInner Q
      (annihilate j (annihilate i (normalizedTensorExterior (n + 2) Q ψ)))
      (annihilate l (annihilate k (normalizedTensorExterior (n + 2) Q φ))) =
      ((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a)) := by
  simp only [normalizedTensorExterior, map_smul,
    two_annihilate_tensorExterior n Q ψ hψ, two_annihilate_tensorExterior n Q φ hφ,
    occupationInner_smul_left, occupationInner_smul_right,
    tensorExterior_inner n Q _ _ (antisymmetric_cons (antisymmetric_cons hφ k) l)]
  have hn := factorial_normalizer (n + 2)
  have hf : ((n + 2).factorial : ℂ) =
      (n + 2 : ℂ) * ((n + 1 : ℂ) * (n.factorial : ℂ)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal,
    map_mul, map_natCast, map_add, map_one, map_ofNat] at *
  calc
    _ = (star ((Real.sqrt ((n + 2).factorial : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt ((n + 2).factorial : ℝ))⁻¹ : ℂ) *
      ((n + 2).factorial : ℂ)) *
      (((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a))) := by
        rw [hf]
        simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
        ring
    _ = _ := by
      simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
      rw [hn, one_mul]

lemma twoBody_inner (n Q : ℕ) (ψ φ : State (n + 2) Q)
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) (i j k l : Fin (Q + 1)) :
    occupationInner Q (normalizedTensorExterior (n + 2) Q ψ)
      (create i (create j (annihilate l (annihilate k
        (normalizedTensorExterior (n + 2) Q φ))))) =
      ((n + 2 : ℂ) * (n + 1 : ℂ)) * ∑ a : Laughlin.Configuration n Q,
        star (ψ (Fin.cons i (Fin.cons j a))) * φ (Fin.cons k (Fin.cons l a)) := by
  rw [annihilate_create_inner, annihilate_create_inner]
  exact pair_annihilation_inner n Q ψ φ hψ hφ i j k l

end ContinuumCoulomb.FockTensorCompression

end

end OAI
