import OAI.Analysis.KadisonKastler.PoissonActionApproximation
import OAI.Analysis.KadisonKastler.MarginalStateApproximation

namespace OAI

/-! # Recovering full product agreement from normal marginals

The two states may be nonnormal on the ambient operator algebra. Their
normal marginals suffice to pass from the smoothed products to all products.
-/

namespace KadisonKastler

open Filter NaimarkZFC
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem productVectorState_square (Ω : H) (a : H →L[ℂ] H) :
    productVectorState Ω (star a*a)=((‖a Ω‖^2 : ℝ) : ℂ) := by
  change inner ℂ Ω (star a (a Ω))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  rfl

theorem normal_marginal_product_agreement
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M N : VonNeumannAlgebra H)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (φ ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (hψ : IsState ψ)
    (hφM : ∀ a ∈ M, φ a=productVectorState Ω a)
    (hψM : ∀ a ∈ M, ψ a=productVectorState Ω a)
    (hφN : ∀ a ∈ N, φ a=productVectorState Ω a)
    (hψN : ∀ a ∈ N, ψ a=productVectorState Ω a)
    (hagrees : ∀ a, Continuous (stateActionOrbit U a) → φ a=ψ a)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ N) : φ (a*b)=ψ (a*b) := by
  let r (n : ℕ) : ℝ := 1/(n+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let A (n : ℕ) := poissonActionApprox U hU a (r n)
  let B (n : ℕ) := poissonActionApprox U hU b (r n)
  have hAM (n : ℕ) : A n ∈ M := poissonActionApprox_mem U hU M hM a ha (r n)
  have hBN (n : ℕ) : B n ∈ N := poissonActionApprox_mem U hU N hN b hb (r n)
  have hconvA : Tendsto (fun n => star (A n-a) Ω) atTop (𝓝 0) := by
    have ht := ((poissonActionApprox_star_tendsto U hU a Ω).comp hrzero).sub_const (star a Ω)
    simpa only [A,Function.comp_def,star_sub,sub_apply,sub_self] using ht
  have hconvB : Tendsto (fun n => (B n-b) Ω) atTop (𝓝 0) := by
    have ht := ((poissonActionApprox_tendsto U hU b Ω).comp hrzero).sub_const (b Ω)
    simpa only [B,Function.comp_def,sub_apply,sub_self] using ht
  have hlim (ρ : (H →L[ℂ] H) →L[ℂ] ℂ) (hρ : IsState ρ)
      (hρM : ∀ c ∈ M, ρ c=productVectorState Ω c)
      (hρN : ∀ c ∈ N, ρ c=productVectorState Ω c) :
      Tendsto (fun n => ρ (A n*B n)) atTop (𝓝 (ρ (a*b))) := by
    apply state_product_tendsto_of_vector_marginals ρ hρ Ω A B a b
      (B := ‖b‖) (hB := fun n => poissonActionApprox_norm U hU b (r n))
      (hca := hconvA) (hcb := hconvB)
    · intro n
      have hd := M.sub_mem (hAM n) ha
      rw [hρM _ (M.mul_mem hd (M.toStarSubalgebra.star_mem' hd))]
      simpa only [star_star] using productVectorState_square Ω (star (A n-a))
    · intro n
      have hd := N.sub_mem (hBN n) hb
      rw [hρN _ (N.mul_mem (N.toStarSubalgebra.star_mem' hd) hd)]
      exact productVectorState_square Ω (B n-b)
  have he (n : ℕ) : φ (A n*B n)=ψ (A n*B n) := by
    apply hagrees
    change Continuous (fun t : ℝ => stateActionOrbit U (A n*B n) t)
    have hmul (t : ℝ) : stateActionOrbit U (A n*B n) t=
        stateActionOrbit U (A n) t*stateActionOrbit U (B n) t :=
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))).map_mul _ _
    simp_rw [hmul]
    exact (poissonActionApprox_orbit_continuous U hU a (hr n)).mul
      (poissonActionApprox_orbit_continuous U hU b (hr n))
  have ht := hlim ψ hψ hψM hψN
  rw [← funext he] at ht
  exact tendsto_nhds_unique (hlim φ hφ hφM hφN) ht

end

end KadisonKastler

end OAI
