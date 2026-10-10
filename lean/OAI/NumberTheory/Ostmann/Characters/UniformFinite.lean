import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction

def uniformPrior {α:Type*} (S:Finset α) (hS:S.Nonempty) : FinitePrior S where
  mass _ := (S.card:ℝ)⁻¹
  mass_nonneg _ := by positivity
  mass_total := by
    have hc : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
    simp [hc]

theorem uniformPrior_cmean {α:Type*} (S:Finset α) (hS:S.Nonempty) (f:α→ℂ) :
    (uniformPrior S hS).cmean (fun a=>f a.val)=(∑a∈S,f a)/(S.card:ℂ) := by
  simp only [FinitePrior.cmean, uniformPrior, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Finset.sum_coe_sort, div_eq_mul_inv]
  ring

theorem prior_cmean_re {α:Type*} [Fintype α] (μ:FinitePrior α) (f:α→ℂ) :
    (μ.cmean f).re=μ.mean (fun a=>(f a).re) := by
  change Complex.reCLM (∑i,(μ.mass i:ℂ)*f i)=_
  simp only [map_sum, Complex.reCLM_apply, FinitePrior.mean, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem prior_cmean_sub {α:Type*} [Fintype α] (μ:FinitePrior α) (f g:α→ℂ) :
    μ.cmean (fun a=>f a-g a)=μ.cmean f-μ.cmean g := by
  simp only [FinitePrior.cmean, mul_sub, Finset.sum_sub_distrib]

theorem prior_cmean_comm {α β:Type*} [Fintype α] [Fintype β]
    (μ:FinitePrior α) (ν:FinitePrior β) (f:α→β→ℂ) :
    μ.cmean (fun a=>ν.cmean (f a))=ν.cmean (fun b=>μ.cmean (fun a=>f a b)) := by
  simp only [FinitePrior.cmean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

end Ostmann.Characters

end

end OAI
