import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings
import OAI.Analysis.RieszRectifiability.Kernel.SymmetricKernelL2

namespace OAI

/-!
# Bilinear Schur estimates

A nonnegative symmetric kernel with uniformly bounded row integrals defines an
integrable bilinear pairing on square-integrable functions. Factoring the kernel
through its square root reduces the quantitative bound to Cauchy–Schwarz on the
product measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function Set

variable {X : Type*} [MeasurableSpace X]

theorem schur_bilinear_integrable_and_sq_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q) (hsymm : ∀ x y, k (y, x) = k (x, y))
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod μ) ∧
      (∫ q : X × X, f q.1 * g q.2 * k q ∂μ.prod μ) ^ 2 ≤
        B ^ 2 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  obtain ⟨hif, hbf⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hbound f hfm hf
  obtain ⟨hig, hbg⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hbound g hgm hg
  have hswap (q : X × X) : k q.swap = k q := hsymm q.1 q.2
  have hig' : Integrable (fun q : X × X => g q.2 ^ 2 * k q) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, hswap] using! hig.swap
  have hbg' : (∫ q : X × X, g q.2 ^ 2 * k q ∂μ.prod μ) ≤ B * (∫ x, g x ^ 2 ∂μ) := by
    have heq := integral_prod_swap (μ := μ) (ν := μ) (fun q : X × X => g q.1 ^ 2 * k q)
    simp only [Prod.fst_swap, hswap] at heq
    exact heq.trans_le hbg
  let F : X × X → ℝ := fun q => f q.1 * Real.sqrt (k q)
  let G : X × X → ℝ := fun q => g q.2 * Real.sqrt (k q)
  have hFsq (q : X × X) : F q ^ 2 = f q.1 ^ 2 * k q := by
    dsimp only [F]
    rw [mul_pow, Real.sq_sqrt (hk0 q)]
  have hGsq (q : X × X) : G q ^ 2 = g q.2 ^ 2 * k q := by
    dsimp only [G]
    rw [mul_pow, Real.sq_sqrt (hk0 q)]
  have hF : MemLp F 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable F (μ.prod μ))).mpr
    simpa only [hFsq] using! hif
  have hG : MemLp G 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable G (μ.prod μ))).mpr
    simpa only [hGsq] using! hig'
  have hprod : (fun q : X × X => F q * G q) = fun q => f q.1 * g q.2 * k q := by
    funext q
    change (f q.1 * Real.sqrt (k q)) * (g q.2 * Real.sqrt (k q)) = _
    calc
      _ = f q.1 * g q.2 * (Real.sqrt (k q)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hk0 q)]
  have hI : Integrable (fun q => F q * G q) (μ.prod μ) :=
    memLp_one_iff_integrable.mp (hF.mul hG)
  refine ⟨hprod ▸ hI, ?_⟩
  have hcs := integral_mul_cauchy_schwarz_sq (μ.prod μ) F G hF hG
  rw [hprod] at hcs
  simp only [hFsq, hGsq] at hcs
  calc
    _ ≤ (∫ q : X × X, f q.1 ^ 2 * k q ∂μ.prod μ) *
        (∫ q : X × X, g q.2 ^ 2 * k q ∂μ.prod μ) := hcs
    _ ≤ (B * (∫ x, f x ^ 2 ∂μ)) * (B * (∫ x, g x ^ 2 ∂μ)) :=
      mul_le_mul hbf hbg' (integral_nonneg fun q => mul_nonneg (sq_nonneg _) (hk0 q))
        (mul_nonneg hB (integral_nonneg fun x => sq_nonneg (f x)))
    _ = _ := by ring

end

end RieszRectifiability

end OAI
