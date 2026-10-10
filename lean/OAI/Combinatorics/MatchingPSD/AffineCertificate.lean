import Mathlib
import OAI.Combinatorics.MatchingPSD.PSDDuality
import OAI.Combinatorics.MatchingPSD.AffineSums

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma affine_slack_certificate (L : AffineSubspace ℝ (Matrix R R ℝ))
    (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef) (hBL : ∀ i, B i ∈ L)
    (f : Matrix R R ℝ →ᵃ[ℝ] ℝ)
    (hn : ∀ X ∈ L, X.PosSemidef → 0 ≤ f X)
    (i₀ : I) (hz : f (B i₀) = 0) :
    ∃ A : Matrix R R ℝ, A.PosSemidef ∧ ∀ i, (A * B i).trace = f (B i) := by
  classical
  suffices ∃ A : Matrix R R ℝ, A.PosSemidef ∧ evaluation B A = fun i => f (B i) by
    obtain ⟨A, hA, he⟩ := this
    exact ⟨A, hA, fun i => congrFun he i⟩
  apply exists_psd_evaluation B hB
  intro c hc
  let s : ℝ := ∑ i, c i
  let t : ℝ := |s| + 1
  let q : ℝ := s + t
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hq : 0 < q := by dsimp [q, t]; linarith [neg_abs_le s]
  let w : I → ℝ := fun i => (c i + if i = i₀ then t else 0) / q
  have hw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, q, s] using div_self hq.ne'
  have hmatrix : ∑ i, w i • B i = q⁻¹ • ((∑ i, c i • B i) + t • B i₀) := by
    simp only [w, div_eq_inv_mul, mul_smul, ← Finset.smul_sum, add_smul,
      Finset.sum_add_distrib]
    congr 1
    simp
  have hpos : (∑ i, w i • B i).PosSemidef := by
    rw [hmatrix]
    exact (hc.add ((hB i₀).smul ht)).smul (inv_nonneg.mpr hq.le)
  have hnonneg := hn _ (affine_sum_mem L B hBL w hw) hpos
  rw [affine_sum_apply f B w hw] at hnonneg
  have hvalue : ∑ i, w i • f (B i) = (∑ i, c i * f (B i)) / q := by
    simp only [w, smul_eq_mul, add_div, add_mul, Finset.sum_add_distrib,
      div_mul_eq_mul_div, ← Finset.sum_div]
    simp [hz]
  rw [hvalue] at hnonneg
  have hh := (le_div_iff₀ hq).mp hnonneg
  simpa using hh

end AffinePSD

end OAI
