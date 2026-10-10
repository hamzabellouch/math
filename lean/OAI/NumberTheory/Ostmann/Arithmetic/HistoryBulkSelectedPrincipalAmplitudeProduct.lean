import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitudeRoot

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude
open Construction HistoryBulkSelectedIntegralReplacement HistoryBulkReplacementGeometry

private theorem scalar_norm_le_exp (mBulk : ℕ) (C : ℝ) (scalar : ℂ)
    (hscalar : ‖scalar‖ ≤ 64 * Real.exp (C * ((mBulk : ℝ)+1))) :
    ‖scalar‖ ≤ Real.exp ((C+64) * ((mBulk : ℝ)+1)) := by
  have hm : 0 ≤ (mBulk : ℝ) := Nat.cast_nonneg mBulk
  have h64 : (64 : ℝ) ≤ Real.exp (64 * ((mBulk : ℝ)+1)) := by
    have hexp := Real.add_one_le_exp (64 * ((mBulk : ℝ)+1))
    nlinarith
  apply hscalar.trans
  calc
    64 * Real.exp (C * ((mBulk : ℝ)+1)) ≤
        Real.exp (64 * ((mBulk : ℝ)+1)) * Real.exp (C * ((mBulk : ℝ)+1)) :=
      mul_le_mul_of_nonneg_right h64 (Real.exp_nonneg _)
    _ = Real.exp ((C+64) * ((mBulk : ℝ)+1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem norm_rootTest_mul_le (independent mixed : Bool) (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : ∀ q ∈ outside, q.Prime) (hV : ∀ q ∈ outside, ∀ j ≤ l, V j < q)
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (K : ℕ)
    (x : Fin (2^l) × Fin m → (ZMod (bulkModulus h g outside K))ˣ)
    (mBulk : ℕ) (C : ℝ) (scalar : ℂ)
    (hscalar : ‖scalar‖ ≤ 64 * Real.exp (C * ((mBulk : ℝ)+1))) :
    ‖rootTest independent mixed d h g hs gs hp hV σ K x * scalar‖ ≤
      (outside.prod : ℝ)^(2^(l+1)) * Real.exp ((C+64) * ((mBulk : ℝ)+1)) := by
  rw [norm_mul]
  exact mul_le_mul (norm_rootTest_le independent mixed d h g hs gs hp hV σ K x)
    (scalar_norm_le_exp mBulk C scalar hscalar) (norm_nonneg _) (by positivity)

theorem norm_mul_rootTest_le (independent mixed : Bool) (d : Decomposition)
    {l m : ℕ} {V : ℕ → ℕ} {outside : List ℕ} (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : ∀ q ∈ outside, q.Prime) (hV : ∀ q ∈ outside, ∀ j ≤ l, V j < q)
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (K : ℕ)
    (x : Fin (2^l) × Fin m → (ZMod (bulkModulus h g outside K))ˣ)
    (mBulk : ℕ) (C : ℝ) (scalar : ℂ)
    (hscalar : ‖scalar‖ ≤ 64 * Real.exp (C * ((mBulk : ℝ)+1))) :
    ‖scalar * rootTest independent mixed d h g hs gs hp hV σ K x‖ ≤
      (outside.prod : ℝ)^(2^(l+1)) * Real.exp ((C+64) * ((mBulk : ℝ)+1)) := by
  rw [mul_comm scalar]
  exact norm_rootTest_mul_le independent mixed d h g hs gs hp hV σ K x mBulk C scalar hscalar

end Ostmann.Arithmetic.HistoryBulkSelectedPrincipalAmplitude

end

end OAI
