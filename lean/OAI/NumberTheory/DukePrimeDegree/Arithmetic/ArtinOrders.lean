import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkCharacters
import OAI.NumberTheory.PrimePackets.IdealThetaXi

namespace OAI

/-!
# Continuing finite Euler-product identities to zero orders

The cyclic permutation identity is first applied to Euler products in
the half-plane of absolute convergence. After clearing the pole at one,
the factors are entire. The identity theorem then gives the corresponding
integer relation among their zero orders everywhere.
-/

open scoped BigOperators Topology
open Filter Set

namespace DukePrimeDegree

open PrimeDegreePackets.HeckeMellin

/-- The actual Dedekind and Hecke continuations are analytic away from
zero and one. Equality on their Dirichlet-series ray determines them on
that connected domain, without choosing pole-clearing factors. -/
theorem analytic_off_zero_one_eq_of_real_eq
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ({0, 1} : Set ℂ)ᶜ)
    (hg : AnalyticOnNhd ℂ g ({0, 1} : Set ℂ)ᶜ)
    (heq : ∀ s : ℝ, 1 < s → f s = g s) :
    EqOn f g ({0, 1} : Set ℂ)ᶜ := by
  have hmem {z : ℂ} (hz : 1 < z.re) : z ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor <;> intro h <;> subst z <;> norm_num at hz
  have hhalf := halfPlane_eq_of_real_eq
    (fun z hz => (hf z (hmem hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z (hmem hz)).differentiableAt.differentiableWithinAt) heq
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (by simp : ({0, 1} : Set ℂ).Countable)).2 (z₀ := 2) (by norm_num)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (2 : ℂ).re by norm_num)] with z hz
  exact hhalf hz

/-- Equality of two finite products of entire factors on the real ray
above one determines the equality of their weighted zero orders. -/
theorem entire_product_orders_eq_of_real_eq
    {I : Type*} [Fintype I]
    (f : I → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (p q : I → ℕ)
    (heq : ∀ s : ℝ, 1 < s → (∏ i, f i s ^ p i) = ∏ i, f i s ^ q i)
    (β : ℂ) :
    (∑ i, (p i : WithTop ℤ) * meromorphicOrderAt (f i) β) =
      ∑ i, (q i : WithTop ℤ) * meromorphicOrderAt (f i) β := by
  classical
  have hp : Differentiable ℂ (fun z => ∏ i, f i z ^ p i) := by
    apply Differentiable.fun_finsetProd
    intro i _
    exact (hf i).pow (p i)
  have hq : Differentiable ℂ (fun z => ∏ i, f i z ^ q i) := by
    apply Differentiable.fun_finsetProd
    intro i _
    exact (hf i).pow (q i)
  have h := congrArg (fun F : ℂ → ℂ => meromorphicOrderAt F β)
    (entire_eq_of_real_eq hp hq heq)
  rw [meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ p i)
    (fun i _ => ((hf i).analyticAt β).meromorphicAt.pow (p i)),
    meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ q i)
    (fun i _ => ((hf i).analyticAt β).meromorphicAt.pow (q i))] at h
  change (∑ i, meromorphicOrderAt (f i ^ p i) β) =
    ∑ i, meromorphicOrderAt (f i ^ q i) β at h
  simpa only [meromorphicOrderAt_pow ((hf _).analyticAt β).meromorphicAt] using h

/-- When the factors have finite orders, the continued product identity
is an equality of ordinary integer zero orders. -/
theorem integer_orders_eq_of_entire_products
    {I : Type*} [Fintype I]
    (f : I → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (p q : I → ℕ)
    (heq : ∀ s : ℝ, 1 < s → (∏ i, f i s ^ p i) = ∏ i, f i s ^ q i)
    (β : ℂ) (m : I → ℤ)
    (hm : ∀ i, meromorphicOrderAt (f i) β = (m i : WithTop ℤ)) :
    (∑ i, (p i : ℤ) * m i) = ∑ i, (q i : ℤ) * m i := by
  have h := entire_product_orders_eq_of_real_eq f hf p q heq β
  simp only [hm] at h
  exact_mod_cast h

/-- A Dirichlet-series product identity gives its zero-order relation
at every point away from the possible poles at zero and one. -/
theorem product_orders_eq_off_zero_one
    {I : Type*} [Fintype I]
    (f : I → ℂ → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) ({0, 1} : Set ℂ)ᶜ)
    (p q : I → ℕ)
    (heq : ∀ s : ℝ, 1 < s → (∏ i, f i s ^ p i) = ∏ i, f i s ^ q i)
    (β : ℂ) (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    (∑ i, (p i : WithTop ℤ) * meromorphicOrderAt (f i) β) =
      ∑ i, (q i : WithTop ℤ) * meromorphicOrderAt (f i) β := by
  classical
  have hβ : β ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hβ0, hβ1]
  have hp : AnalyticOnNhd ℂ (fun z => ∏ i, f i z ^ p i) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => (hf i z hz).pow (p i))
  have hq : AnalyticOnNhd ℂ (fun z => ∏ i, f i z ^ q i) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ (fun i _ => (hf i z hz).pow (q i))
  have he := analytic_off_zero_one_eq_of_real_eq hp hq heq
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : (fun z => ∏ i, f i z ^ p i) =ᶠ[𝓝[≠] β]
      (fun z => ∏ i, f i z ^ q i) := by
    have hn : ∀ᶠ z in 𝓝 β, z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
    exact he hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ p i)
    (fun i _ => (hf i β hβ).meromorphicAt.pow (p i)),
    meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun i z => f i z ^ q i)
    (fun i _ => (hf i β hβ).meromorphicAt.pow (q i))] at H
  change (∑ i, meromorphicOrderAt (f i ^ p i) β) =
    ∑ i, meromorphicOrderAt (f i ^ q i) β at H
  simpa only [meromorphicOrderAt_pow (hf _ β hβ).meromorphicAt] using H

end DukePrimeDegree

end OAI
