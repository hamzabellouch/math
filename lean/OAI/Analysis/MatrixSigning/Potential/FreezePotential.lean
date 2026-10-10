import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ShiftFeasibleMap
import OAI.Analysis.MatrixSigning.Optimization.NearestEndpoint
import OAI.Analysis.MatrixSigning.Matrices.OperatorNormSquare

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma freezeOne_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeOne (lam^2/ν) x i j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  unfold freezeOne
  split
  · rename_i hclose
    let xr : Coordinates N := fun j => (x j:ℝ)
    have hxr : Cube xr := fun j => by
      change |(x j:ℝ)| ≤ 1
      exact_mod_cast hx j
    have hord := S_bounds A hA htr hxr
    have ηbound := eta_one_bound (by norm_num : (0:ℝ)≤384) A hvar hxr
    have ηbound' : eta 384 A xr (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
      apply ηbound.trans
      exact scalar_mono_psd one_mem_psdCone (by exact_mod_cast (show 384*ν≤(384:ℚ) by linarith))
    obtain ⟨z,hz,_,hmin⟩ := normalized_minimizer (ε:=(ε:ℝ)) (S A xr) (eta 384 A xr)
      (eta_positive (by norm_num : (0:ℝ)≤384) A hxr) (by exact_mod_cast hε)
      (by exact_mod_cast hεd) hord.1 hord.2 ηbound'
    have ht : |(nearestEndpoint (x i):ℝ)|=1 := by exact_mod_cast nearestEndpoint_abs (x i)
    have hdist : |(nearestEndpoint (x i):ℝ)-xr i|=1-|xr i| := by
      change |(nearestEndpoint (x i):ℝ)-(x i:ℝ)|=1-|(x i:ℝ)|
      exact_mod_cast nearestEndpoint_dist (hx i)
    have hh := freeze_potential (by norm_num : (0:ℝ)≤384) (ε:=(ε:ℝ)) (lam:=(lam:ℝ)) (ν:=(ν:ℝ))
      (by exact_mod_cast hε.le) (by exact_mod_cast hlam) (by exact_mod_cast hν) A xr hxr i ht hdist
      (atom_operatorNorm_le_sqrt A (by exact_mod_cast hν.le) hvar i)
      (by change 1-|(x i:ℝ)| ≤ (lam:ℝ)^2/(ν:ℝ); exact_mod_cast hclose) z hz hmin
    have heq : (fun j => (Function.update x i (nearestEndpoint (x i)) j : ℝ)) =
        Function.update xr i (nearestEndpoint (x i) : ℝ) := by
      ext j
      by_cases hji : j=i
      · subst j;simp
      · simp [Function.update_of_ne hji,xr]
    simpa only [heq] using hh
  · exact le_refl _

lemma freezeList_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeList (lam^2/ν) x l j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  induction l generalizing x with
  | nil => exact le_refl _
  | cons i is ih =>
    exact (ih _ (freezeOne_cube _ _ hx i)).trans
      (freezeOne_potential A hA htr hν hν1 hlam hε hεd hvar x hx i)

end
end CurrentKS.RationalFace

end OAI
