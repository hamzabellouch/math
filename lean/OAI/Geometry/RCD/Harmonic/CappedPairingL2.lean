import OAI.Geometry.RCD.Heat.CappedIntegralProduct

namespace OAI

/-! # L² control from pairings with capped nonnegative functions -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Testing only the capped function itself suffices for the L² conclusion. -/
theorem integral_sq_le_of_capped_pairing {f : X → ℝ}
    (hf : Measurable f) (hi : Integrable f μ) (hfn : ∀ x, 0 ≤ f x)
    {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ C : ℝ≥0, (∫ x, f x * min (f x) C ∂μ) ≤
      A * Real.sqrt (∫ x, (min (f x) C)^2 ∂μ)) :
    Integrable (fun x => (f x)^2) μ ∧ (∫ x, (f x)^2 ∂μ) ≤ A^2 := by
  have hcap (C : ℝ≥0) : Integrable (fun x => (min (f x) C)^2) μ := by
    simpa only [pow_two] using integrable_capped_product μ hi hi hfn hfn C
  have hfcap (C : ℝ≥0) : Integrable (fun x => f x * min (f x) C) μ :=
    hi.mul_bdd ((hf.min measurable_const).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hfn x) C.coe_nonneg)]
        exact min_le_right _ _)
  have hb (C : ℝ≥0) : (∫ x, (min (f x) C)^2 ∂μ) ≤ A^2 := by
    have hn : 0 ≤ ∫ x, (min (f x) C)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hs := Real.sq_sqrt hn
    have hle : (∫ x, (min (f x) C)^2 ∂μ) ≤ ∫ x, f x * min (f x) C ∂μ := by
      apply integral_mono (hcap C) (hfcap C)
      intro x
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (min_le_left (f x) (C:ℝ))
        (le_min (hfn x) C.coe_nonneg)
    have hh := hle.trans (hpair C)
    have hroot : Real.sqrt (∫ x, (min (f x) C)^2 ∂μ) ≤ A := by
      nlinarith [Real.sqrt_nonneg (∫ x, (min (f x) C)^2 ∂μ)]
    nlinarith
  let F (i : ℕ) (x : X) := ENNReal.ofReal ((min (f x) (i:ℝ))^2)
  have hm (i : ℕ) : Measurable (F i) := ((hf.min measurable_const).pow_const 2).ennreal_ofReal
  have hmono : Monotone F := by
    intro i j hij x
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ (le_min (hfn x) (by positivity)) (le_min (hfn x) (by positivity))).mpr
      (min_le_min_left _ (by exact_mod_cast hij))
  have he (x : X) : (⨆ i, F i x) = ENNReal.ofReal ((f x)^2) := by
    apply le_antisymm
    · apply iSup_le
      intro i
      apply ENNReal.ofReal_le_ofReal
      exact (sq_le_sq₀ (le_min (hfn x) (by positivity)) (hfn x)).mpr (min_le_left _ _)
    · obtain ⟨i,hi⟩ := exists_nat_ge (f x)
      apply le_iSup_of_le i
      dsimp only [F]
      rw [min_eq_left hi]
  have hlin : (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂μ) ≤ ENNReal.ofReal (A^2) := by
    have hefun : (fun x => ENNReal.ofReal ((f x)^2)) = (fun x => ⨆ i, F i x) :=
      funext fun x => (he x).symm
    rw [hefun]
    rw [lintegral_iSup hm hmono]
    apply iSup_le
    intro i
    have heq := ofReal_integral_eq_lintegral_ofReal (hcap (i:ℝ≥0))
      (Eventually.of_forall fun x => sq_nonneg (min (f x) (i:ℝ)))
    simp only [NNReal.coe_natCast] at heq
    change (∫⁻ x, ENNReal.ofReal ((min (f x) (i:ℝ))^2) ∂μ) ≤ _
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (hb i)
  have hsq : Integrable (fun x => (f x)^2) μ :=
    ⟨(hf.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (f x))).mpr
        (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hsq,?_⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hsq
    (Eventually.of_forall fun x => sq_nonneg (f x))
  rw [← heq] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg A)).mp hlin

end RegularPointCoordinates

end

end OAI
