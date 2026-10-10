import Mathlib
import OAI.Analysis.AffineBernstein.LocalMaximumHessian

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EllipticComparison
open Filter
open scoped Topology

/-- Elementary strict comparison for the genuine inverse-Hessian operator.
No quantitative elliptic regularity or Harnack estimate is used here. -/
lemma inverseHessianTrace_strict_maximum_principle {n : ℕ}
    {u f : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hf : ContinuousOn f K)
    (hs : ∀ x ∈ interior K, ContDiffAt ℝ ∞ f x)
    (hp : ∀ x ∈ interior K, (hessian u x).PosDef)
    (hL : ∀ x ∈ interior K, 0 < inverseHessianTrace u f x)
    (hb : ∀ x ∈ K, x ∉ interior K → f x ≤ 0) :
    ∀ x ∈ K, f x ≤ 0 := by
  intro x hx
  by_contra H
  have hfx : 0 < f x := lt_of_not_ge H
  obtain ⟨y,hy,hm⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hf
  have hfy : 0 < f y := hfx.trans_le (hm hx)
  have hyi : y ∈ interior K := by
    by_contra H
    exact (not_lt_of_ge (hb y hy H)) hfy
  have hl : IsLocalMax f y := hm.isLocalMax (mem_of_superset (isOpen_interior.mem_nhds hyi) interior_subset)
  exact (not_lt_of_ge (inverseHessianTrace_nonpos_of_localMax (hs y hyi) (hp y hyi) hl)) (hL y hyi)

lemma inverseHessianTrace_sub {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {u f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    {x : Space n} (hx : x ∈ O) :
    inverseHessianTrace u (fun y => f y-g y) x = inverseHessianTrace u f x - inverseHessianTrace u g x := by
  simp only [inverseHessianTrace,hessian_sub_on hO hf hg hx,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

lemma inverseHessianTrace_add_constant {n : ℕ} {f u : Space n → ℝ} (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => f y+c) x = inverseHessianTrace u f x := by
  simp only [inverseHessianTrace,hessian_add_constant]

lemma inverseHessianTrace_sub_constant {n : ℕ} {f u : Space n → ℝ} (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => f y-c) x = inverseHessianTrace u f x := by
  simpa only [sub_eq_add_neg] using inverseHessianTrace_add_constant (f := f) (u := u) (-c) x

end EllipticComparison


end
end AffineBernstein
end

end OAI
