import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedTranslationTests

namespace OAI

/-! # A translated product of arbitrary bounded tests is small against an L1 pair density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem translated_pair_product_zero {ρ : Velocity × Velocity → ℝ}
    (hρm : Measurable ρ) (hρ : Integrable ρ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p : Velocity × Velocity,
      ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) atTop (𝓝 0) := by
  let φ : ℕ → Velocity × Velocity → ℝ := fun n p => ψ n p.1*ψ n p.2
  have hφ n : Measurable (φ n) := ((hψ n).comp measurable_fst).mul ((hψ n).comp measurable_snd)
  have hφbound n p : |φ n p| ≤ C^2 := by
    rw [show φ n p = ψ n p.1*ψ n p.2 from rfl,abs_mul,pow_two]
    exact mul_le_mul (hbound n p.1) (hbound n p.2) (abs_nonneg _) hC
  have haa : Tendsto (fun n => (a n,a n)) atTop (𝓝 (0 : Velocity × Velocity)) :=
    ha.prodMk_nhds ha
  have ha0 : Tendsto (fun n => (a n,(0:Velocity))) atTop (𝓝 (0 : Velocity × Velocity)) :=
    ha.prodMk_nhds tendsto_const_nhds
  have h0a : Tendsto (fun n => ((0:Velocity),a n)) atTop (𝓝 (0 : Velocity × Velocity)) :=
    tendsto_const_nhds.prodMk_nhds ha
  have h1 := weighted_translation_tests_zero hρm hρ haa hφ (sq_nonneg C) hφbound
  have h2 := weighted_translation_tests_zero hρm hρ ha0 hφ (sq_nonneg C) hφbound
  have h3 := weighted_translation_tests_zero hρm hρ h0a hφ (sq_nonneg C) hφbound
  have hi n (b : Velocity × Velocity) : Integrable (fun p => ρ p*(φ n (p+b)-φ n p)) := by
    have hm := ((hφ n).comp (measurable_id.add_const b)).sub (hφ n)
    have hb p : |φ n (p+b)-φ n p| ≤ 2*C^2 := by
      calc
        _ ≤ |φ n (p+b)|+|φ n p| := abs_sub _ _
        _ ≤ C^2+C^2 := add_le_add (hφbound n _) (hφbound n _)
        _ = _ := by ring
    apply (hρ.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hb)).congr
    exact ae_of_all _ (fun _ => mul_comm _ _)
  have he n :
      (∫ p : Velocity × Velocity, ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) =
      ((∫ p, ρ p*(φ n (p+(a n,a n))-φ n p))-
        (∫ p, ρ p*(φ n (p+(a n,0))-φ n p)))-
        (∫ p, ρ p*(φ n (p+(0,a n))-φ n p)) := by
    have hfun : (fun p : Velocity × Velocity =>
        ρ p*((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2))) =
        ((fun p => ρ p*(φ n (p+(a n,a n))-φ n p))-
          (fun p => ρ p*(φ n (p+(a n,0))-φ n p)))-
          (fun p => ρ p*(φ n (p+(0,a n))-φ n p)) := by
      funext p
      simp only [φ,Pi.sub_apply,Prod.fst_add,Prod.snd_add,add_zero]
      ring
    rw [hfun]
    change (∫ p, (ρ p*(φ n (p+(a n,a n))-φ n p)-
      ρ p*(φ n (p+(a n,0))-φ n p))-ρ p*(φ n (p+(0,a n))-φ n p)) = _
    calc
      _ = (∫ p, ρ p*(φ n (p+(a n,a n))-φ n p)-ρ p*(φ n (p+(a n,0))-φ n p))-
          (∫ p, ρ p*(φ n (p+(0,a n))-φ n p)) :=
        integral_sub ((hi n (a n,a n)).sub (hi n (a n,0))) (hi n (0,a n))
      _ = _ := congrArg (fun x => x-(∫ p, ρ p*(φ n (p+(0,a n))-φ n p)))
        (integral_sub (hi n (a n,a n)) (hi n (a n,0)))
  have ht := (h1.sub h2).sub h3
  simp only [sub_zero] at ht
  exact ht.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
