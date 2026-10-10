import OAI.MeasureTheory.Falconer.Fourier.ComplexMaskJets
import OAI.MeasureTheory.Falconer.Geometry.AmbientChartBudget
import OAI.MeasureTheory.Falconer.Geometry.NormalizedInverseFactors

namespace OAI

/-! # Finite-budget angular jets as normalized recursive multipliers

A fixed chart constant is selected before the angular multiplier or its
previous derivative order. Taking a jet consumes that exact order from
the ambient budget; normalization does not enlarge the derivative scale.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def normalizedAngular (A : ℝ) {d : ℕ} (B : Space d → ℂ) : Space d → ℂ :=
  fun z => A⁻¹ • B z

theorem normalizedAngular_restore {d : ℕ} {A : ℝ} (hA : 0 < A)
    (B : Space d → ℂ) (z : Space d) :
    (A : ℂ)*normalizedAngular A B z = B z := by
  simp only [normalizedAngular,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    mul_inv_cancel₀ hA.ne',Complex.ofReal_one,one_mul]

/-- One fixed normalization controls both ambient and rotated chart jets. -/
theorem ambient_angular_normalization (n K : ℕ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ B : Space (n+2) → ℂ, ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 < C → 1 ≤ D →
      (∀ t ≤ K, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t B w‖ ≤ C*D^t) →
      ContDiff ℝ ∞ (normalizedAngular (H*C) B) ∧
      (∀ t ≤ K, ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (normalizedAngular (H*C) B) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) => normalizedAngular (H*C) B w) 1 D := by
  obtain ⟨H₀,hH₀,hchart⟩ := ambient_symbol_rotated_chart_budget n K
  let H := H₀+1
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hH₀H : H₀ ≤ H := by dsimp [H]; linarith
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hb
  have hHC : 0 < H*C := mul_pos (zero_lt_one.trans_le hH) hC
  have hCHC : C ≤ H*C := le_mul_of_one_le_left hC.le hH
  have hfactor : (H*C)⁻¹*C ≤ 1 := by
    calc
      _ ≤ (H*C)⁻¹*(H*C) :=
        mul_le_mul_of_nonneg_left hCHC (inv_nonneg.mpr hHC.le)
      _ = 1 := inv_mul_cancel₀ hHC.ne'
  have hnormalized : ContDiff ℝ ∞ (normalizedAngular (H*C) B) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (n+2) => (H*C)⁻¹)).smul hB
  refine ⟨hnormalized,?_,?_⟩
  · intro t ht w
    change ‖iteratedFDeriv ℝ t (fun z => (H*C)⁻¹ • B z) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hB.of_le (by simp)).contDiffAt,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hHC.le)]
    calc
      _ ≤ (H*C)⁻¹*(C*D^t) :=
        mul_le_mul_of_nonneg_left (hb t ht w) (inv_nonneg.mpr hHC.le)
      _ = ((H*C)⁻¹*C)*D^t := by ring
      _ ≤ 1*D^t := mul_le_mul_of_nonneg_right hfactor
        (pow_nonneg (zero_le_one.trans hD) t)
      _ = _ := one_mul _
  · have hraw : ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) => B w) (H*C) D := by
      refine ⟨hB.continuous.measurable.comp (continuous_subtype_val.comp continuous_snd).measurable,
        ?_,?_,?_⟩
      · intro x w
        have h := hb 0 (Nat.zero_le K) w
        simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at h
        exact h.trans hCHC
      · intro x e y
        exact hB.comp (rotatedChartCurve_contDiff e y)
      · intro e t ht x y hy u hu
        exact (hchart B hB C D hC.le hD hb e y hy u hu t ht).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH₀H hC.le)
            (pow_nonneg (zero_le_one.trans hD) t))
    have hn := hraw.normalized hHC le_rfl (zero_le_one.trans hD)
    have he : (fun (_ : Space (n+2)) (w : Sphere (n+2)) =>
        normalizedAngular (H*C) B w) =
        normalizedEndpoint (H*C) (fun (_ : Space (n+2)) (w : Sphere (n+2)) => B w) := by
      funext x w
      simp only [normalizedEndpoint,normalizedAngular,Complex.real_smul]
    rw [he]
    exact hn

/-- The initial multiplier needs exactly `p+K` derivatives for a new order-`p`
jet to remain in the recursive class with `K` derivatives. -/
theorem angular_jet_symbol (n K : ℕ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ (L : ℕ) (j : MaskJetIndex (n+2))
      (f : Space (n+2) → ℂ), ContDiff ℝ ∞ f → ∀ D : ℝ, 1 ≤ D →
      j.order+K ≤ L →
      (∀ t ≤ L, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ t f w‖ ≤ D^t) →
      ContDiff ℝ ∞ (normalizedAngular H (j.scaledValue D⁻¹ f)) ∧
      (∀ t ≤ K, ∀ w : Sphere (n+2),
        ‖iteratedFDeriv ℝ t (normalizedAngular H (j.scaledValue D⁻¹ f)) w‖ ≤ D^t) ∧
      ChartSymbolControl K
        (fun (_ : Space (n+2)) (w : Sphere (n+2)) =>
          normalizedAngular H (j.scaledValue D⁻¹ f) w) 1 D := by
  obtain ⟨H,hH,hbound⟩ := ambient_angular_normalization n K
  refine ⟨H,hH,?_⟩
  intro L j f hf D hD hLK hb
  have hjet : ∀ t ≤ K, ∀ w : Sphere (n+2),
      ‖iteratedFDeriv ℝ t (j.scaledValue D⁻¹ f) w‖ ≤ 1*D^t := by
    intro t ht w
    simpa only [one_mul] using j.angular_budget_shift f hf hD (by omega) hb
      t (by omega) w
  simpa only [mul_one] using hbound (j.scaledValue D⁻¹ f)
    (j.scaledValue_contDiff D⁻¹ f hf) 1 D zero_lt_one hD hjet

end Falconer

end OAI
