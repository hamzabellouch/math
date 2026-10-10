import Mathlib
import OAI.Analysis.MatrixSigning.Potential.SymmetricMap
import OAI.Analysis.MatrixSigning.Matrices.PosLower

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma tight_of_complementarity [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (hP : P ∈ pd d) (hQ : Q ∈ pd d) (z : Point d)
    (hz : z ∈ feasible S η)
    (hc : inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 = 0) :
    residual S η z = 0 := by
  have hf := (feasible_iff_cone S η z).mp hz
  have hPz := inner_nonneg_of_psd P (-residual S η z).1 hP.posSemidef hf.2.1
  have hQz := inner_nonneg_of_psd Q (-residual S η z).2 hQ.posSemidef hf.2.2
  simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_right] at hPz hQz
  have h₁ : inner ℝ P (-(residual S η z).1) = 0 := by rw [inner_neg_right]; linarith
  have h₂ : inner ℝ Q (-(residual S η z).2) = 0 := by rw [inner_neg_right]; linarith
  have he₁ := eq_zero_of_inner_pd hP hf.2.1 h₁
  have he₂ := eq_zero_of_inner_pd hQ hf.2.2 h₂
  apply Prod.ext
  · exact neg_eq_zero.mp he₁
  · exact neg_eq_zero.mp he₂

theorem kkt [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε K : ℝ} (hε : 0 < ε)
    (hS₁ : -K • ((Hermitian.one : H d) : H d) ≤ S) (hS₂ : S ≤ K • ((Hermitian.one : H d) : H d))
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    ∃ P Q : H d, P ∈ pd d ∧ Q ∈ pd d ∧ P ≤ (Hermitian.one : H d) ∧ Q ≤ (Hermitian.one : H d) ∧
      realTrace P + realTrace Q = 1 ∧
      P = sandwich z.2.1 (η Q) + ε • sandwich z.2.1 (Hermitian.one : H d) ∧
      Q = sandwich z.2.2 (η P) + ε • sandwich z.2.2 (Hermitian.one : H d) ∧
      residual S η z = 0 ∧
      sandwich (invH z.2.1) P = η Q + ε • (Hermitian.one : H d) ∧
      sandwich (invH z.2.2) Q = η P + ε • (Hermitian.one : H d) := by
  obtain ⟨P,Q,hP,hQ,hc,hl⟩ := exists_matrix_multipliers S η hηpos hS₁ hS₂ z hz hmin
  have hzD := hz.1
  have htr := stationary_trace ε S η hηsym P Q z hzD hl
  have hX := stationary_X ε S η hηsym P Q z hzD hl
  have hY := stationary_Y ε S η hηsym P Q z hzD hl
  have hPX : P = sandwich z.2.1 (η Q + ε • (Hermitian.one : H d)) := by
    rw [← hX, sandwich_inverse_cancel _ _ hzD.1]
  have hQY : Q = sandwich z.2.2 (η P + ε • (Hermitian.one : H d)) := by
    rw [← hY, sandwich_inverse_cancel _ _ hzD.2]
  have hPpd : P ∈ pd d := hPX.symm ▸ (sandwich_pd _ _ hzD.1 (pd_sum_scalar (hηpos Q hQ) hε))
  have hQpd : Q ∈ pd d := hQY.symm ▸ (sandwich_pd _ _ hzD.2 (pd_sum_scalar (hηpos P hP) hε))
  have hPle : P ≤ (Hermitian.one : H d) := by
    have ht : realTrace P ≤ 1 := by linarith [realTrace_nonneg hQ]
    exact (trace_bound_above hP).trans (by simpa only [one_smul] using scalar_one_mono (d := d) ht)
  have hQle : Q ≤ (Hermitian.one : H d) := by
    have ht : realTrace Q ≤ 1 := by linarith [realTrace_nonneg hP]
    exact (trace_bound_above hQ).trans (by simpa only [one_smul] using scalar_one_mono (d := d) ht)
  refine ⟨P,Q,hPpd,hQpd,hPle,hQle,htr,?_,?_,tight_of_complementarity S η P Q hPpd hQpd z hz hc,hX,hY⟩
  · rw [hPX, sandwich_add, sandwich_smul]
  · rw [hQY, sandwich_add, sandwich_smul]

end
end CurrentKS.Variational

end OAI
