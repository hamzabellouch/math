import OAI.NumberTheory.DukePrimeDegree.Arithmetic.HeckeFactors
import OAI.NumberTheory.PrimePackets.FunctionalEquation

namespace OAI

/-!
# Continued cyclic Artin factorizations

After realizing the nonprincipal cyclic characters as even ray
characters, the actual Artin factorization continues away from zero and
one. Its zero-order relation has nonnegative finite summands.
-/

noncomputable section

open Filter Set Module
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
variable {d e N : ℕ} [NeZero N]

/-- The principal factor is the incomplete Dedekind zeta function; the
other factors are the entire continuations of the realized characters. -/
def cyclicHeckeFactor (σ : OrderedEmbeddings (d + 1) F)
    (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) : ℂ → ℂ :=
  if χ = 1 then cosetMeromorphic σ hn N else (ψ χ).nonprincipalContinued σ hn

omit [NumberField.IsTotallyReal E] in
theorem cyclicHeckeFactor_eq_artinDirichlet
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    cyclicHeckeFactor σ hn ψ χ s = artinDirichlet F E χ N s := by
  by_cases hχ : χ = 1
  · subst χ
    simpa [cyclicHeckeFactor] using
      principal_continuation_eq_artinDirichlet F E σ hn N (NeZero.pos N) hs
  · simpa only [cyclicHeckeFactor, ite_eq_right hχ] using
      nonprincipal_continuation_eq_artinDirichlet F E σ hn χ (ψ χ) (hid χ) (hψ χ hχ) hs

omit [NumberField E] [IsGalois F E] [NumberField.IsTotallyReal E] in
theorem cyclicHeckeFactor_analytic
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) :
    AnalyticOnNhd ℂ (cyclicHeckeFactor σ hn ψ χ) ({0, 1} : Set ℂ)ᶜ := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using (not_or.mp hz).1
  have hz1 : z ≠ 1 := by simpa using (not_or.mp hz).2
  by_cases hχ : χ = 1
  · simp only [cyclicHeckeFactor, ite_eq_left hχ, cosetMeromorphic_eq_factor]
    exact (cosetXiFactor_analyticAt N hz0 hz1).mul
      ((completedThetaXi_entire σ hn).analyticAt z)
  · simpa only [cyclicHeckeFactor, ite_eq_right hχ] using
      ((ψ χ).nonprincipalContinued_entire σ hn).analyticAt z

omit [NumberField E] [IsGalois F E] [NumberField.IsTotallyReal E] in
theorem cyclicHeckeFactor_finite_nonnegative_order
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ m : ℕ, meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) =
      (m : WithTop ℤ) := by
  by_cases hχ : χ = 1
  · simp only [cyclicHeckeFactor, ite_eq_left hχ]
    rw [cosetMeromorphic_order_eq σ hn N hβ0 hβ1]
    have ha : ∀ z, AnalyticAt ℂ (completedThetaXi σ hn) z :=
      fun z => (completedThetaXi_entire σ hn).analyticAt z
    have hfin : analyticOrderAt (completedThetaXi σ hn) (β : ℂ) ≠ ⊤ := by
      intro H
      have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (β : ℂ) ha).mp H
      exact (completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn (s := 2)
        (by norm_num)) (congrFun hz 2)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    refine ⟨m, ?_⟩
    rw [(ha (β : ℂ)).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
    rfl
  · simpa only [cyclicHeckeFactor, ite_eq_right hχ] using
      (ψ χ).nonprincipalContinued_finite_nonnegative_order σ hn (hψ χ hχ) (β : ℂ)

section Cyclic

variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup
local instance : Fintype ((E ≃ₐ[F] E) →* ℂˣ) := Fintype.ofFinite _

theorem cyclicHeckeFactor_product_eq
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (τ : OrderedEmbeddings (e + 1) E) (he : finrank ℚ E = e + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N) {s : ℂ} (hs : 1 < s.re) :
    cosetMeromorphic τ he N s = ∏ χ, cyclicHeckeFactor σ hn ψ χ s := by
  have hc : (∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) *
      removedEulerPolynomial E N s = 1 := by
    unfold removedEulerPolynomial primeIdealEulerFactor
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p _
    rw [← Finset.prod_mul_distrib]
    simp only [inv_mul_cancel₀ (primeEuler_denominator_ne_zero E _ (zero_lt_one.trans hs)),
      Finset.prod_const_one]
  rw [cosetMeromorphic_eq_dedekindZeta τ he N hs,
    actual_cyclic_artin_factorization F E N (NeZero.pos N) hD hs]
  calc
    _ = ((∏ p ∈ badRationalPrimes N, primeIdealEulerFactor E p.val s) *
        removedEulerPolynomial E N s) * ∏ χ, artinDirichlet F E χ N s := by ring
    _ = ∏ χ, artinDirichlet F E χ N s := by rw [hc, one_mul]
    _ = _ := Finset.prod_congr rfl (fun χ _ =>
      (cyclicHeckeFactor_eq_artinDirichlet σ hn ψ hid hψ χ hs).symm)

theorem cyclicHeckeFactor_sum_orders
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (τ : OrderedEmbeddings (e + 1) E) (he : finrank ℚ E = e + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∑ χ, meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ)) =
      meromorphicOrderAt (completedThetaXi τ he) (β : ℂ) := by
  have hp : AnalyticOnNhd ℂ (fun z => ∏ χ, cyclicHeckeFactor σ hn ψ χ z)
      ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    exact Finset.analyticAt_fun_prod Finset.univ
      (fun χ _ => cyclicHeckeFactor_analytic σ hn ψ χ z hz)
  have hq : AnalyticOnNhd ℂ (cosetMeromorphic τ he N) ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    rw [cosetMeromorphic_eq_factor]
    exact (cosetXiFactor_analyticAt N (by simpa using (not_or.mp hz).1)
      (by simpa using (not_or.mp hz).2)).mul
        ((completedThetaXi_entire τ he).analyticAt z)
  have heq := analytic_off_zero_one_eq_of_real_eq hp hq (fun s hs =>
    (cyclicHeckeFactor_product_eq σ hn τ he ψ hid hψ hD hs).symm)
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : (fun z => ∏ χ, cyclicHeckeFactor σ hn ψ χ z) =ᶠ[𝓝[≠] (β : ℂ)]
      cosetMeromorphic τ he N := by
    have hn : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_fun_prod (s := Finset.univ)
    (f := fun χ => cyclicHeckeFactor σ hn ψ χ)
    (fun χ _ => (cyclicHeckeFactor_analytic σ hn ψ χ (β : ℂ) hβ).meromorphicAt),
    cosetMeromorphic_order_eq τ he N hβ0 hβ1] at H
  exact H

end Cyclic
end DukePrimeDegree

end

end OAI
