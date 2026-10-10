import Mathlib
import OAI.Analysis.MatrixSigning.Potential.VarianceH

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma realTrace_variance_rank_one (A : Fin N → H d) (hA : ∀ i,A i ∈ psdCone d)
    (hrank : ∀ i,(A i : Mat d).rank ≤ 1) :
    Hermitian.realTrace (varianceH A)=∑ i,(Hermitian.realTrace (A i))^2 := by
  rw [varianceH,Hermitian.realTrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sandwich_rank_one (A i) _ (hA i) (hrank i),inner_one',Hermitian.realTrace_smul]
  ring

lemma variance_lower [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d) ≤ operatorNorm (varianceH A) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : Fin N => (1:ℝ)) (fun i => Hermitian.realTrace (A i))
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,htr] at hcs
  have ht := realTrace_mono (le_operatorNorm_smul_one (varianceH A))
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one,realTrace_variance_rank_one A hA hrank] at ht
  have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0:ℝ)≤N)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<N*d)).mpr
  nlinarith

lemma variance_lower_paper [NeZero d] [NeZero N] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) :
    1/((N:ℝ)*d^2) ≤ operatorNorm (varianceH A) := by
  apply le_trans _ (variance_lower A hA hrank htr)
  have hdpos : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hNpos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  apply one_div_le_one_div_of_le (mul_pos hNpos hdpos)
  have hd : (1:ℝ) ≤ d := by exact_mod_cast NeZero.pos d
  exact mul_le_mul_of_nonneg_left (by nlinarith : (d:ℝ) ≤ (d:ℝ)^2) hNpos.le

lemma normalized_nonempty (A : Fin N → H d)
    (htr : ∑ i,Hermitian.realTrace (A i)=1) : N ≠ 0 := by
  intro hn
  subst N
  simp at htr

end
end CurrentKS.State

end OAI
