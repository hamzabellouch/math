import OAI.Probability.InvariantIsing.Cavity.CavityBlockFactor

namespace OAI

/-! Temperature scaling of the actual quadratic cavity factor. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavityQuadratic_smul {d : ℕ} (t : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) :
    cavityQuadratic (t • K) y = t * cavityQuadratic K y := by
  simp only [cavityQuadratic, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, y i * (t*K i j) * y j = t*(y i*K i j*y j) from fun i j => by ring]
  simp only [← Finset.mul_sum]
  ring

lemma cavityLogFactor_smul {d n : ℕ} (t : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin d → ℝ) (ε : Spin n) :
    cavityLogFactor (t • K) (t • L) (t • C) y ε = t * cavityLogFactor K L C y ε := by
  simp only [cavityLogFactor, cavityQuadratic_smul, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i j, y i * (t*L i j) * spinValue (ε j) =
    t*(y i*L i j*spinValue (ε j)) from fun i j => by ring]
  simp only [← Finset.mul_sum]
  ring

lemma cavity_radial_square_cutoff {α : Type*} (Y : α → ℝ) (hY : ∀ x, 0 ≤ Y x)
    {R : ℝ} (hR : 0 ≤ R) :
    {x | Y x ≤ R} = {x | 1+(Y x)^2 ≤ 1+R^2} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have hy := hY x
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hR hy)]
  · intro h
    nlinarith [hY x]

end InvariantIsing

end

end OAI
