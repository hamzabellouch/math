import OAI.Probability.InvariantIsing.Cavity.CavityOrbitFactorization

namespace OAI

/-! Haar averaging with orbit membership and equivariance required only
almost everywhere, as needed for full-rank Gaussian compression events. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

theorem cavity_orbit_factorization_ae {N M : ℕ} {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (Orthogonal M)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (e : Orthogonal N → Orthogonal M)
    (F : Orthogonal M → X) (T : Orthogonal M → Y)
    (hF : Measurable F) (hT : Measurable T)
    (act : Orthogonal N → X → X) (hact : Measurable (Function.uncurry act))
    (hmul : ∀ U V x, act (U * V) x = act U (act V x))
    (heF : ∀ V, ∀ᵐ U ∂μ, F (e V * U) = act V (F U))
    (heT : ∀ V, ∀ᵐ U ∂μ, T (e V * U) = T U)
    (x₀ : X) (horbit : ∀ᵐ U ∂μ, ∃ V, F U = act V x₀)
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hCg : 0 ≤ Cg)
    (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ y, ‖g y‖ ≤ Cg) :
    (∫ U, g (T U) * f (F U) ∂μ) =
      (∫ U, g (T U) ∂μ) * ∫ V, f (act V x₀) ∂ν := by
  let B := fun p : Orthogonal N × Orthogonal M => g (T p.2) * f (act p.1 (F p.2))
  have hm : Measurable B := (hg.comp (hT.comp measurable_snd)).mul
    (hf.comp (hact.comp (measurable_fst.prodMk (hF.comp measurable_snd))))
  have hi : Integrable B (ν.prod μ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Cg * Cf)
    exact ae_of_all _ (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hgb _) (hfb _) (norm_nonneg _) hCg)
  have hrow (V : Orthogonal N) :
      (∫ U, B (V, U) ∂μ) = ∫ U, g (T U) * f (F U) ∂μ := by
    calc
      _ = ∫ U, g (T (e V * U)) * f (F (e V * U)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [heF V, heT V] with U hFU hTU
        simp only [B, hTU, hFU]
      _ = _ := integral_mul_left_eq_self (fun U => g (T U) * f (F U)) (e V)
  have hcol : ∀ᵐ U ∂μ,
      (∫ V, B (V, U) ∂ν) = g (T U) * ∫ V, f (act V x₀) ∂ν := by
    filter_upwards [horbit] with U hU
    obtain ⟨W, hW⟩ := hU
    change (∫ V, g (T U) * f (act V (F U)) ∂ν) = _
    rw [integral_const_mul, hW]
    congr 1
    simp_rw [← hmul]
    exact integral_mul_right_eq_self (fun V => f (act V x₀)) W
  calc
    _ = ∫ V, ∫ U, B (V, U) ∂μ ∂ν := by simp only [hrow]; simp
    _ = ∫ U, ∫ V, B (V, U) ∂ν ∂μ := integral_integral_swap hi
    _ = _ := (integral_congr_ae hcol).trans (integral_mul_const _ _)


theorem cavity_orbit_factorization_right_ae {N M : ℕ} {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (Orthogonal M)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (e : Orthogonal N → Orthogonal M)
    (F : Orthogonal M → X) (T : Orthogonal M → Y)
    (hF : Measurable F) (hT : Measurable T)
    (act : Orthogonal N → X → X) (hact : Measurable (Function.uncurry act))
    (hmul : ∀ U V x, act (U * V) x = act U (act V x))
    (heF : ∀ V, ∀ᵐ U ∂μ, F (U * e V) = act V (F U))
    (heT : ∀ V, ∀ᵐ U ∂μ, T (U * e V) = T U)
    (x₀ : X) (horbit : ∀ᵐ U ∂μ, ∃ V, F U = act V x₀)
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hCg : 0 ≤ Cg)
    (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ y, ‖g y‖ ≤ Cg) :
    (∫ U, g (T U) * f (F U) ∂μ) =
      (∫ U, g (T U) ∂μ) * ∫ V, f (act V x₀) ∂ν := by
  let B := fun p : Orthogonal N × Orthogonal M => g (T p.2) * f (act p.1 (F p.2))
  have hm : Measurable B := (hg.comp (hT.comp measurable_snd)).mul
    (hf.comp (hact.comp (measurable_fst.prodMk (hF.comp measurable_snd))))
  have hi : Integrable B (ν.prod μ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (Cg * Cf)
    exact ae_of_all _ (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hgb _) (hfb _) (norm_nonneg _) hCg)
  have hrow (V : Orthogonal N) :
      (∫ U, B (V, U) ∂μ) = ∫ U, g (T U) * f (F U) ∂μ := by
    calc
      _ = ∫ U, g (T (U * e V)) * f (F (U * e V)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [heF V, heT V] with U hFU hTU
        simp only [B, hTU, hFU]
      _ = _ := integral_mul_right_eq_self (fun U => g (T U) * f (F U)) (e V)
  have hcol : ∀ᵐ U ∂μ,
      (∫ V, B (V, U) ∂ν) = g (T U) * ∫ V, f (act V x₀) ∂ν := by
    filter_upwards [horbit] with U hU
    obtain ⟨W, hW⟩ := hU
    change (∫ V, g (T U) * f (act V (F U)) ∂ν) = _
    rw [integral_const_mul, hW]
    congr 1
    simp_rw [← hmul]
    exact integral_mul_right_eq_self (fun V => f (act V x₀)) W
  calc
    _ = ∫ V, ∫ U, B (V, U) ∂μ ∂ν := by simp only [hrow]; simp
    _ = ∫ U, ∫ V, B (V, U) ∂ν ∂μ := integral_integral_swap hi
    _ = _ := (integral_congr_ae hcol).trans (integral_mul_const _ _)


end InvariantIsing

end

end OAI
