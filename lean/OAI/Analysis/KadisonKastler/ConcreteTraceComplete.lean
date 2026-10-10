import OAI.Analysis.KadisonKastler.ConcreteWeakTransfer

namespace OAI

/-! # Completeness of bounded tracial two-norm balls

Strong trace transfer and Hilbert-space completeness retain tracial
limits in the von Neumann algebra, allowing continuous circle cutoffs
to converge to spectral projections.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- On a bounded operator ball the finite-vector trace is continuous for
strong convergence, also in the tracial two-norm. -/
theorem FiniteVectorTrace.traceTwoNorm_tendsto_of_strong
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    {J : Type*} {l : Filter J} (x : J → Algebra M) (a : Algebra M)
    {C : ℝ} (hx : ∀ j, ‖x j‖ ≤ C)
    (hstrong : ∀ ξ, Tendsto (fun j => (x j : H →L[ℂ] H) ξ) l
      (𝓝 ((a : H →L[ℂ] H) ξ))) :
    Tendsto (fun j => traceTwoNorm τ (x j - a)) l (𝓝 0) := by
  let d : J → Algebra M := fun j => x j - a
  have hd (ξ : H) : Tendsto (fun j => (d j : H →L[ℂ] H) ξ) l (𝓝 0) := by
    change Tendsto (fun j => (x j : H →L[ℂ] H) ξ - (a : H →L[ℂ] H) ξ) l (𝓝 0)
    simpa only [sub_self] using (hstrong ξ).sub (tendsto_const_nhds : Tendsto (fun _ : J => (a : H →L[ℂ] H) ξ) l (𝓝 ((a : H →L[ℂ] H) ξ)))
  have hdb (j : J) : ‖d j‖ ≤ C + ‖a‖ := (norm_sub_le _ _).trans (add_le_add (hx j) le_rfl)
  have hstar (ξ : H) : Tendsto
      (fun j => (star (d j) * d j : Algebra M).val ξ) l (𝓝 0) := by
    apply squeeze_zero_norm
    · intro j
      calc
        ‖(star (d j) * d j : Algebra M).val ξ‖ ≤ ‖star (d j : H →L[ℂ] H)‖ * ‖(d j : H →L[ℂ] H) ξ‖ :=
          (star (d j : H →L[ℂ] H)).le_opNorm _
        _ ≤ (C + ‖a‖) * ‖(d j : H →L[ℂ] H) ξ‖ := by
          rw [norm_star]
          exact mul_le_mul_of_nonneg_right (hdb j) (norm_nonneg _)
    · simpa only [norm_zero, mul_zero] using (hd ξ).norm.const_mul (C + ‖a‖)
  have ht := hτ.tendsto (fun j => star (d j) * d j) 0 (fun ξ η => by
    simpa only [ZeroMemClass.coe_zero, zero_apply, inner_zero_right] using
      tendsto_const_nhds.inner (hstar ξ))
  have hr := (Complex.continuous_re.tendsto _).comp ht
  have hs := (Real.continuous_sqrt.tendsto _).comp hr
  simpa only [traceTwoNorm, d, map_zero, Complex.zero_re, Real.sqrt_zero,
    Function.comp_def] using hs

/-- A uniformly bounded tracial two-Cauchy sequence has an actual limit
in the concrete von Neumann algebra, with strong and two-norm convergence. -/
theorem FiniteVectorTrace.bounded_complete
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (x : ℕ → Algebra M) {C : ℝ} (hC : 0 ≤ C) (hx : ∀ j, ‖x j‖ ≤ C)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε) :
    ∃ a : Algebra M, ‖a‖ ≤ C ∧
      (∀ ξ, Tendsto (fun j => (x j : H →L[ℂ] H) ξ) atTop
        (𝓝 ((a : H →L[ℂ] H) ξ))) ∧
      Tendsto (fun j => traceTwoNorm τ (x j - a)) atTop (𝓝 0) := by
  have hc (ξ : H) : CauchySeq (fun j => (x j : H →L[ℂ] H) ξ) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hτ.strongContinuous ξ (2 * C) (by positivity) ε hε
    obtain ⟨N, hN⟩ := hCauchy δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hnorm : ‖x m - x n‖ ≤ 2 * C := by
      have hb := (norm_sub_le (x m) (x n)).trans (add_le_add (hx m) (hx n))
      linarith
    have hs := hsmall (x m - x n) hnorm (hN m hm n hn)
    change ‖(x m : H →L[ℂ] H) ξ - (x n : H →L[ℂ] H) ξ‖ < ε at hs
    simpa only [dist_eq_norm] using hs
  have hex (ξ : H) := cauchySeq_tendsto_of_complete (hc ξ)
  choose v hv using hex
  let F : H →ₗ[ℂ] H :=
    { toFun := v
      map_add' := by
        intro ξ η
        apply tendsto_nhds_unique (hv (ξ + η))
        simpa only [map_add] using (hv ξ).add (hv η)
      map_smul' := by
        intro c ξ
        apply tendsto_nhds_unique (hv (c • ξ))
        simpa only [map_smul, RingHom.id_apply] using (hv ξ).const_smul c }
  have hF (ξ : H) : ‖F ξ‖ ≤ C * ‖ξ‖ := by
    exact le_of_tendsto (hv ξ).norm
      (Eventually.of_forall fun j => (x j).val.le_of_opNorm_le (hx j) ξ)
  let T : H →L[ℂ] H := F.mkContinuous C hF
  have hT (ξ : H) : Tendsto (fun j => (x j : H →L[ℂ] H) ξ) atTop (𝓝 (T ξ)) := hv ξ
  have hm : T ∈ M := Generator.Tracial.weak_operator_limit_mem M x T (fun ξ η =>
    tendsto_const_nhds.inner (hT ξ))
  let a : Algebra M := ⟨T, hm⟩
  refine ⟨a, ?_, hT, hτ.traceTwoNorm_tendsto_of_strong x a hx hT⟩
  exact T.opNorm_le_bound hC hF

end

end KadisonKastler

end OAI
