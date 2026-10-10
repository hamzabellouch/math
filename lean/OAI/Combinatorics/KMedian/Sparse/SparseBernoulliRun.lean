import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseAlgorithm
import OAI.Combinatorics.KMedian.Sparse.SparseMarginalTools
import OAI.Combinatorics.KMedian.Sparse.SparseMomentAlgebra
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliFeatures

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def run (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ℕ → SparseIntegerLaw (Fin n → Bool)
  | 0 => .dirac (fun _ => false)
  | t+1 => if ht : t<n then
      (run p hp t).step (features (d := d)) (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)
    else run p hp t

theorem run_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) (ht : t ≤ n) (f : Fin d → Fin (n+1)) :
    (run (d := d) p hp t).moment (fun q => monomial q f)=target p t f := by
  induction t generalizing f with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,monomial,flag,target]
  | succ t ih =>
    have htn : t<n := by omega
    have hh := (run (d := d) p hp t).step_moment (features (d := d))
      (fun _ => p ⟨t,htn⟩) (fun _ => hp ⟨t,htn⟩)
      (fun q b => endpoint q ⟨t,htn⟩ b) (finFunctionFinEquiv f)
    simp only [features_code] at hh
    rw [run,dite_eq_left htn]
    refine hh.trans ?_
    rw [target_succ p t htn f]
    by_cases hi : (⟨t,htn⟩ : Fin n) ∈ used f
    · rw [ite_eq_left hi]
      calc
        _ = (run (d := d) p hp t).moment
            (fun q => p ⟨t,htn⟩*monomial q (without f ⟨t,htn⟩)) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp [monomial_endpoint,hi]
        _ = _ := by rw [SparseIntegerLaw.moment_mul,ih (by omega)]
    · rw [ite_eq_right hi]
      calc
        _ = (run (d := d) p hp t).moment (fun q => monomial q f) := by
          apply SparseIntegerLaw.moment_congr
          intro a
          simp only [monomial_endpoint,ite_eq_right hi]
          ring
        _ = _ := ih (by omega) f

theorem run_length (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℕ) : (run (d := d) p hp t).length ≤ (n+1)^d+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run (d := d) p hp t).branch (fun _ => p ⟨t,ht⟩)
        (fun _ => hp ⟨t,ht⟩) (fun q b => endpoint q ⟨t,ht⟩ b)).compressAuto_correct
          (features (d := d)) |>.1
    · exact ih

theorem run_spec (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    let μ := run (d := d) p hp n
    μ.length ≤ (n+1)^d+1 ∧ ∀ f : Fin d → Fin (n+1),
      μ.moment (fun q => monomial q f)=∏ i ∈ used f, p i := by
  refine ⟨run_length p hp n,fun f => ?_⟩
  rw [run_moment p hp n (le_refl n) f]
  simp only [target,Fin.isLt,ite_eq_left]

end MetricKMedian.SparseBernoulli

end OAI
