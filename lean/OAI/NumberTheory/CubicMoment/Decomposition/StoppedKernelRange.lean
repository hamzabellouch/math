import OAI.NumberTheory.CubicMoment.Decomposition.StoppedActualRange
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDyadPartition
import OAI.NumberTheory.CubicMoment.Estimates.CentralProductSupport

namespace OAI

/-! Norm geometry of the actual stopped kernel, before any analytic
estimate. Sharp side dyads imply the strengthened bilinear length range. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma centeredHeightKernel_norm_range (ℓ : ℤ) (H T : ℝ) {X : ℝ}
    (hX : 0 < X) {n : Eisenstein}
    (hne : centeredHeightKernel ℓ primeProductEnvelope H T X X n ≠ 0) :
    X/2 < norm n ∧ norm n < 3*X := by
  have hW : primeProductEnvelope (norm n/X) ≠ 0 := by
    intro hz
    apply hne
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  constructor
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero_lower
    exact (div_le_iff₀ hX).mpr (by linarith)
  · by_contra hn
    apply hW
    apply primeProductEnvelope_zero
    exact (le_div_iff₀ hX).mpr (by linarith)

lemma centeredHeightKernel_squarefree (ℓ : ℤ) (H T X X₀ : ℝ)
    {n : Eisenstein} (hn : primary n)
    (hne : centeredHeightKernel ℓ primeProductEnvelope H T X X₀ n ≠ 0) :
    Squarefree n := by
  by_contra hs
  apply hne
  simp only [centeredHeightKernel,centeredGauss_vanishes hn hs,mul_zero,zero_mul]

lemma stopped_dyad_product_range {X A B : ℝ} {a b : Eisenstein}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : A ≤ norm a ∧ norm a ≤ 2*A)
    (hb : B/2 ≤ norm b ∧ norm b ≤ B)
    (hprod : X/2 ≤ norm (a*b) ∧ norm (a*b) ≤ 3*X) :
    X/4 ≤ A*B ∧ A*B ≤ 6*X := by
  rw [norm_mul_eq] at hprod
  have hu := mul_le_mul ha.2 hb.2 (norm_nonneg _) (by positivity : 0 ≤ 2*A)
  have hl := mul_le_mul ha.1 hb.1 (by positivity : 0 ≤ B/2) (norm_nonneg _)
  constructor <;> nlinarith

theorem eventually_stopped_kernel_dyad_range (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (ℓ : ℤ) (H T A B : ℝ) (a b : Eisenstein),
      0 ≤ A → 0 ≤ B →
      A ≤ norm a → norm a ≤ 2*A → B/2 ≤ norm b → norm b ≤ B →
      X^(7/20:ℝ) ≤ B → B ≤ X^(39/100:ℝ) →
      centeredHeightKernel ℓ primeProductEnvelope H T X X (a*b) ≠ 0 →
      2*B^(3/2:ℝ) ≤ A ∧ A ≤ B^2/(Real.log X)^G := by
  filter_upwards [eventually_stopped_actual_range G,eventually_gt_atTop (0:ℝ)] with X hr hX
  intro ℓ H T A B a b hA hB ha ha' hb hb' hBlo hBhi hne
  have hk := centeredHeightKernel_norm_range ℓ H T hX hne
  have hp := stopped_dyad_product_range hA hB ⟨ha,ha'⟩ ⟨hb,hb'⟩ ⟨hk.1.le,hk.2.le⟩
  exact hr A B (by linarith [hp.1]) (by linarith [hp.2]) hBlo hBhi

end CubicFirstMoment

end

end OAI
