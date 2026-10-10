import OAI.NumberTheory.DirichletL.Detector.UnramifiedScalar
import OAI.NumberTheory.DirichletL.Detector.LocalWeights

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalMarkedTerm (eta a X W V : ℂ) (e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (6*m)) e l k m

include hc in
lemma localGamma_conjugate_three_sq :
    (star (localGamma p hp.ne_zero hg 3))^2 = actualSextic (Ideal.span {p}) hg (-1) := by
  have hg3 : localGamma p hp.ne_zero hg 3 ^ 2 = actualSextic (Ideal.span {p}) hg (-1) :=
    ProbePhase.normalizedTraceGauss_three_sq p hp.ne_zero hg hc
  rw [← star_pow, hg3]
  have hω := actualSextic_neg_one_sq (Ideal.span {p}) hg
  rcases (sq_eq_one_iff).mp hω with h | h
  · simp [h]
  · simp [h]

include hc in
lemma firstGauss_ne_zero : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 ≠ 0 := by
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro h
    have he : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 1).mp he
    norm_num at hd
  have he := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
  have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
    (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr isUnit_one.neg
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  intro hz
  rw [hz, zero_mul] at he
  exact (mul_ne_zero hω hQ) he.symm

omit [(Ideal.span {p}).IsMaximal] in
include hp in
lemma primeNorm_ne_zero : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

include hc

omit hc in
@[simp] theorem markedTerm_zero_index (eta a X W V : ℂ) (k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 0 k m = 0 := by
  simp only [principalMarkedTerm, mul_zero, add_zero, ite_true]

omit hc in
lemma markedTerm_higher_outer (eta a X W V : ℂ) (e l k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V e l (k+2) m = 0 := by
  unfold principalMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp, weightedScalar_zero]

lemma markedTerm_odd (eta a X W V : ℂ) (e r k m : ℕ) (he : e ≤ 1) :
    principalMarkedTerm p hp hg eta a X W V e (2*r+1) k m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega)]
  have hn : e+3*(2*r+1)-1 = 6*r+(e+2) := by omega
  rw [hn, unramified_odd_zero p hp hg hc r m k (e+2) (by omega), weightedScalar_zero]

lemma markedTerm_squarefree_boundary (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 r =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_left rfl]
  exact weighted_squarefree_boundary _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_squarefree_boundary_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_even_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*V^d) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_left (by omega)]
  exact weighted_even_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_even_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

lemma markedTerm_even_kone (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 (r+1) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_left rfl]
  exact weighted_even_kone _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_even_kone_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_squarefree_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V^(d+1)) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_left (by omega)]
  exact weighted_squarefree_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_squarefree_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI
