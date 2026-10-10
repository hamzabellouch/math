import OAI.Probability.InvariantIsing.Cavity.CavityOrbitFactorizationAE

namespace OAI

/-! Joint bounded tests in the orbit factorization retain the random
compression parameter inside the test. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

theorem cavity_orbit_joint_right_ae {N M : ℕ} {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure (Orthogonal M)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (e : Orthogonal N → Orthogonal M)
    (F : Orthogonal M → X) (T : Orthogonal M → Y)
    (hF : Measurable F) (hT : Measurable T)
    (act : Orthogonal N → X → X) (hact : Measurable (Function.uncurry act))
    (hmul : ∀ U V x, act (U*V) x = act U (act V x))
    (heF : ∀ V, ∀ᵐ U ∂μ, F (U*e V) = act V (F U))
    (heT : ∀ V, ∀ᵐ U ∂μ, T (U*e V) = T U)
    (x₀ : X) (horbit : ∀ᵐ U ∂μ, ∃ V, F U = act V x₀)
    (f : Y × X → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ p, ‖f p‖ ≤ C) :
    (∫ U, f (T U,F U) ∂μ) = ∫ U, ∫ V, f (T U,act V x₀) ∂ν ∂μ := by
  let B := fun p : Orthogonal N × Orthogonal M => f (T p.2,act p.1 (F p.2))
  have hm : Measurable B := hf.comp ((hT.comp measurable_snd).prodMk
    (hact.comp (measurable_fst.prodMk (hF.comp measurable_snd))))
  have hi : Integrable B (ν.prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun p => hb _)
  have hrow V : (∫ U, B (V,U) ∂μ) = ∫ U, f (T U,F U) ∂μ := by
    calc
      _ = ∫ U, f (T (U*e V),F (U*e V)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [heF V,heT V] with U hFU hTU
        simp only [B,hTU,hFU]
      _ = _ := integral_mul_right_eq_self (fun U => f (T U,F U)) (e V)
  have hcol : ∀ᵐ U ∂μ, (∫ V, B (V,U) ∂ν) = ∫ V, f (T U,act V x₀) ∂ν := by
    filter_upwards [horbit] with U hU
    obtain ⟨W,hW⟩ := hU
    change (∫ V, f (T U,act V (F U)) ∂ν) = _
    rw [hW]
    simp_rw [← hmul]
    exact integral_mul_right_eq_self (fun V => f (T U,act V x₀)) W
  calc
    _ = ∫ V, ∫ U, B (V,U) ∂μ ∂ν := by simp only [hrow]; simp
    _ = ∫ U, ∫ V, B (V,U) ∂ν ∂μ := integral_integral_swap hi
    _ = _ := integral_congr_ae hcol

end InvariantIsing

end

end OAI
