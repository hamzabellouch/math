import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Potential
import OAI.Analysis.MatrixSigning.Potential.VarianceH

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma norm_le_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ε lam ν : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1) (hlam : 0 ≤ lam)
    (hν1 : ν ≤ 1) (hvar : varianceH A ≤ ν • (Hermitian.one : H d))
    (x : Coordinates N) (hx : Cube x) : operatorNorm (S A x) ≤ potential 384 ε lam A x := by
  have hp := eta_positive (show (0:ℝ) ≤ 384 by norm_num) A hx
  have hb := S_bounds A hA htr hx
  have hηI : eta 384 A x (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d) := by
    apply (eta_one_bound (show (0:ℝ) ≤ 384 by norm_num) A hvar hx).trans
    exact scalar_one_mono (by linarith)
  obtain ⟨z,hz,_,hm⟩ := normalized_minimizer (S A x) (eta 384 A x) hp hε hεd hb.1 hb.2 hηI
  have hn := feasible_norm_le_objective ε hε.le (S A x) (eta 384 A x) hp z hz
  unfold potential
  rw [value_eq_of_min ε _ _ z hz hm]
  exact hn.trans (le_add_of_nonneg_right (mul_nonneg hlam
    (Finset.sum_nonneg (fun i _ => (psi_bounds (hx i)).1))))

lemma potential_nonneg [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ε lam ν : ℝ} (hε : 0 < ε) (hεd : ε*d ≤ 1) (hlam : 0 ≤ lam)
    (hν1 : ν ≤ 1) (hvar : varianceH A ≤ ν • (Hermitian.one : H d))
    (x : Coordinates N) (hx : Cube x) : 0 ≤ potential 384 ε lam A x :=
  (operatorNorm_nonneg _).trans (norm_le_potential A hA htr hε hεd hlam hν1 hvar x hx)

lemma potential_zero_le [NeZero d] [NeZero N] (A : Fin N → H d)
    {ν lam : ℝ} (hν : 0 < ν) (hlam : lam ≤ Real.sqrt ν/(100*N))
    (hvar : varianceH A ≤ ν • (Hermitian.one : H d)) :
    potential 384 (ν/d) lam A 0 ≤ (3931/100:ℝ)*Real.sqrt ν := by
  obtain ⟨z,hz,hzv⟩ := initial_scalar_point A hν hvar
  have hd : (0:ℝ) < d := by exact_mod_cast NeZero.pos d
  have hv := value_le_feasible (ν/d) (div_nonneg hν.le hd.le) _ _
    (eta_positive (show (0:ℝ) ≤ 384 by norm_num) A cube_zero) z hz
  have hm := mul_le_mul_of_nonneg_right hlam
    (Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (Fin N))) =>
      (psi_bounds (cube_zero i)).1))
  change objective (ν/d) z+(Real.sqrt ν/(100*N))*∑ i,psi ((0:Coordinates N) i)=_ at hzv
  unfold potential
  linarith

end
end CurrentKS.State

end OAI
