import Mathlib
import OAI.Analysis.Commutator.WeakOperatorAlgebra

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutes_of_dense_contraction_tests (P : VonNeumannAlgebra H)
    (test : ℕ → H →L[ℂ] H)
    (hdense : ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)))
    (B : H →L[ℂ] H) (htest : ∀ n,Commute (test n) B)
    (A : H →L[ℂ] H) (hA : A∈P) : Commute A B := by
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  obtain ⟨k,hk⟩ := hdense (d⁻¹ • A) (P.smul_mem hA d⁻¹) hdn
  have hlim (x y : H) : Tendsto (fun n => inner ℂ (test (k n) x) y) atTop
      (𝓝 (inner ℂ ((d⁻¹ • A) x) y)) := (hk x).inner tendsto_const_nhds
  have hc := WeakOperatorLimit.intertwine hlim B B
    (Eventually.of_forall (fun n => (htest (k n)).eq))
  have h := congrArg (fun C : H →L[ℂ] H => d • C) hc
  change A*B=B*A
  simpa only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_inv_cancel₀ hd,one_smul] using h

end Kadison

end

end
end

end OAI
