import OAI.Probability.InvariantIsing.Cavity.CavitySelectedHaarMoment
import OAI.Probability.InvariantIsing.Cavity.CavityHaarNumeratorAverage

namespace OAI

/-! The ordinary fourth moment bound after averaging over the original
Gibbs prior and the independent fresh Haar frames. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_selected_site_fourth_bound {m q d : ℕ} {N : Fin m → ℕ}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ a, ‖(WithLp.toLp 2 (v a) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (U : (a : Fin m) → Orthogonal (N a)) :
    ‖cavitySelectedSiteProjection e (fun a (_ : Unit) => v a)
      (cavityGroupHaarFrames A₀ U) ()‖^4 ≤ ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2 := by
  let Y := cavitySelectedSiteProjection e (fun a (_ : Unit) => v a) (cavityGroupHaarFrames A₀ U) ()
  have hb (j : Fin d) : (Y j)^2 ≤ C * ∑ a, (N a : ℝ) := by
    have hu := (cavity_orthonormal_of_gram (A₀ (e j).1) (hA₀ (e j).1)).norm_eq_one (e j).2
    have hi := abs_real_inner_le_norm (WithLp.toLp 2 (v (e j).1))
      (matrixRotation (U (e j).1) (WithLp.toLp 2 (fun l => A₀ (e j).1 l (e j).2)))
    rw [(matrixRotation _).norm_map, hu, mul_one] at hi
    have hsq : (Y j)^2 ≤ ‖(WithLp.toLp 2 (v (e j).1) :
        EuclideanSpace ℝ (Fin (N (e j).1)))‖^2 := by
      simpa only [Y, cavity_selected_site_inner, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) hi 2
    exact (hsq.trans (hv _)).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun a _ => Nat.cast_nonneg (N a)) (Finset.mem_univ (e j).1)) hC)
  have hs : ‖Y‖^2 ≤ (d : ℝ) * (C * ∑ a, (N a : ℝ)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  simpa only [← pow_mul, Nat.reduceMul, Y] using pow_le_pow_left₀ (sq_nonneg ‖Y‖) hs 2

lemma measurable_cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hv : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (fun p : (Ω × ((a : Fin m) → Orthogonal (N a))) × X =>
      cavitySelectedSiteProjection e (v p.1.1) (cavityGroupHaarFrames A₀ p.1.2) p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro j
  dsimp only [cavitySelectedSiteProjection]
  apply Finset.measurable_sum
  intro l _
  exact (((measurable_pi_apply l).comp ((measurable_pi_apply (e j).1).comp
    ((hv x).comp measurable_fst))).mul
      (((measurable_pi_apply (e j).2).comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply (e j).1).comp
          ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))))

theorem cavity_haar_prior_fourth_moment {m q d k : ℕ} {N : Fin m → ℕ}
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hN : ∀ a, 0 < N a)
    (μ : (a : Fin m) → Measure (Orthogonal (N a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (e : Fin d → Fin m × Fin q)
    (v : Ω → (a : Fin m) → X → Fin (N a) → ℝ)
    (hvM : ∀ x, Measurable (fun ω a => v ω a x))
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (hA₀ : ∀ a, (A₀ a).transpose * A₀ a = 1) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ ω x a, ‖(WithLp.toLp 2 (v ω a x) : EuclideanSpace ℝ (Fin (N a)))‖^2 ≤ C * N a)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let R := fun (p : Ω × ((a : Fin m) → Orthogonal (N a))) (x : X × Spin k) =>
      ‖cavitySelectedSiteProjection e (v p.1) (cavityGroupHaarFrames A₀ p.2) x.1‖^4
    (∀ p, Integrable (R p) ((ν p.1).prod π)) ∧
    Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) ∧
    (∫ p, ∫ x, R p x ∂(ν p.1).prod π ∂P.prod (Measure.pi μ)) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
  intro R
  let D := ((d : ℝ) * (C * ∑ a, (N a : ℝ)))^2
  have hbound p x : ‖R p x‖ ≤ D := by
    simp only [R, norm_pow, norm_norm]
    exact cavity_selected_site_fourth_bound e (fun a => v p.1 a x.1) A₀ hA₀ hC (hv p.1 x.1) p.2
  have hR : Measurable (Function.uncurry R) :=
    ((measurable_cavitySelectedSiteProjection e v hvM A₀).comp
      (measurable_fst.prodMk measurable_snd.fst)).norm.pow_const 4
  have hi p : Integrable (R p) ((ν p.1).prod π) :=
    Integrable.of_bound ((hR.comp measurable_prodMk_left).aestronglyMeasurable) D
      (ae_of_all _ (hbound p))
  let νK : Kernel Ω X := Kernel.mk ν hν
  let : IsMarkovKernel νK := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (ν ω))⟩
  let κ : Kernel (Ω × ((a : Fin m) → Orthogonal (N a))) (X × Spin k) :=
    (Kernel.comap νK Prod.fst measurable_fst).prod (Kernel.const _ π)
  have hm : Measurable (fun p => ∫ x, R p x ∂(ν p.1).prod π) := by
    simpa only [κ, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
      νK, Kernel.coe_mk, Function.uncurry_apply_pair] using
      (hR.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hmi : Integrable (fun p => ∫ x, R p x ∂(ν p.1).prod π) (P.prod (Measure.pi μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable D (ae_of_all _ fun p =>
      by simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := (ν p.1).prod π) (ae_of_all _ (hbound p)))
  refine ⟨hi, hmi, ?_⟩
  rw [integral_prod _ hmi]
  have hn p : 0 ≤ ∫ x, R p x ∂(ν p.1).prod π :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hpω (ω : Ω) : (∫ U, ∫ x, R (ω,U) x ∂(ν ω).prod π ∂Measure.pi μ) ≤
      (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 := by
    have hiω : Integrable (fun p : ((a : Fin m) → Orthogonal (N a)) × (X × Spin k) =>
        R (ω, p.1) p.2) ((Measure.pi μ).prod ((ν ω).prod π)) :=
      Integrable.of_bound ((hR.comp ((measurable_const.prodMk measurable_fst).prodMk
          measurable_snd)).aestronglyMeasurable) D
        (ae_of_all _ fun p => hbound (ω,p.1) p.2)
    rw [integral_integral_swap hiω]
    have hb x : (∫ U, R (ω,U) x ∂Measure.pi μ) ≤
        (d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2 :=
      cavity_selected_haar_fourth_moment hN μ e (fun a => v ω a x.1) A₀ hA₀ (hv ω x.1)
    have hi := integral_mono_of_nonneg (μ := (ν ω).prod π)
      (ae_of_all _ fun x => integral_nonneg (fun U => pow_nonneg (norm_nonneg _) 4))
      (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hb)
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have ht := integral_mono_of_nonneg (μ := P)
    (ae_of_all _ fun ω => integral_nonneg (fun U => hn (ω,U)))
    (integrable_const ((d : ℝ)^2 * cavityGaussianAbsMoment 4 * C^2)) (ae_of_all _ hpω)
  simpa only [integral_const, probReal_univ, one_smul] using ht

end InvariantIsing

end

end OAI
