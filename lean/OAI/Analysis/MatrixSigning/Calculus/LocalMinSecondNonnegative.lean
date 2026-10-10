import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.Analysis
open Filter Set
open scoped Topology

lemma localMin_second_nonnegative {f : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra hn
  have hn' : deriv (deriv f) a < 0 := lt_of_not_ge hn
  have hm := isLocalMax_of_deriv_deriv_neg hn' h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [h,hm] with x hx hx'
    exact le_antisymm hx' hx
  have he' := he.deriv.deriv_eq
  simp only [deriv_const'] at he'
  linarith

lemma majorant_derivatives {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a)
    (heq : f a = g a) (hle : ∀ᶠ s in 𝓝 a, f s ≤ g s) :
    deriv f a = deriv g a ∧ deriv (deriv f) a ≤ deriv (deriv g) a := by
  have hm : IsLocalMin (fun s => g s - f s) a := by
    filter_upwards [hle] with s hs
    change g a - f a ≤ g s - f s
    rw [← heq,sub_self]
    exact sub_nonneg.mpr hs
  have hd := hm.deriv_eq_zero
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have he : deriv (fun s => g s - f s) =ᶠ[𝓝 a] fun s => deriv g s - deriv f s := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with s hs ht
    exact deriv_sub (ht.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num))
  have hf' := hf.derivWithin (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  have hg' := hg.derivWithin (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)
  have hdd := localMin_second_nonnegative hm (hg.continuousAt.sub hf.continuousAt)
  rw [he.deriv_eq] at hdd
  have hde := ((hg'.differentiableAt (by norm_num)).hasDerivAt.sub
    (hf'.differentiableAt (by norm_num)).hasDerivAt).deriv
  change deriv (fun s => deriv g s - deriv f s) a = _ at hde
  rw [hde] at hdd
  have hd0 := (hgd.hasDerivAt.sub hfd.hasDerivAt).deriv
  change deriv (fun s => g s - f s) a = _ at hd0
  rw [hd0] at hd
  exact ⟨(sub_eq_zero.mp hd).symm,sub_nonneg.mp hdd⟩

end CurrentKS.Analysis

end OAI
