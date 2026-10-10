import OAI.NumberTheory.JointDickman.Counting.CountingForwardRows

namespace OAI

/-! # A single finite index for the actual counting-model row -/
namespace JointDickman
open Finset Classical

abbrev CountingFeatureIndex (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) :=
  Σ d : P.support, Fin (m d.val) × Fin (m d.val)

theorem countingForwardRow_features_flat (F : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M u : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (z : ℕ → ℂ) (i : Fin M) :
    countingForwardRow F P m B L T H M u τ C c D σ z i =
      ∑ e : CountingFeatureIndex P m,
        ((independentRootMean B L τ C : ℂ)*
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m e.1.val) B e.2.2)
            (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1))))*
          countingTermRow F P e.1.val (m e.1.val) B T H M u
            (c e.1.val) (D e.1.val) σ z i e.2.1 e.2.2 := by
  rw [countingForwardRow_features]
  simp only [CountingFeatureIndex,Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [sum_coe_sort P.support (fun d => ∑ a : Fin (m d), ∑ b : Fin (m d),
    ((independentRootMean B L τ C : ℂ)*
      (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature (m d) B b)
        (u+(i.val+1)) : ℂ)*star (z (u+(i.val+1))))*
      countingTermRow F P d (m d) B T H M u (c d) (D d) σ z i a b)]
  simp only [mul_sum]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

end JointDickman

end OAI
