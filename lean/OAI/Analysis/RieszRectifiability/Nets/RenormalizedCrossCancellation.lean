import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ComplexHeightPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem mean_zero_subtracted_kernel_test_integral {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g ν)
    (hzero : (∫ x, g x ∂ν) = 0) (k : Ambient d → ℝ)
    (hk : Integrable (fun x => k x • g x) ν) (c : ℝ) :
    Integrable (fun x => (k x - c) • g x) ν ∧
      (∫ x, (k x - c) • g x ∂ν) = ∫ x, k x • g x ∂ν := by
  have hc : Integrable (fun x => c • g x) ν := hg.smul c
  have heq : (fun x => (k x - c) • g x) = fun x => k x • g x - c • g x := by
    funext x
    exact sub_smul (k x) c (g x)
  rw [heq]
  refine ⟨hk.sub hc, ?_⟩
  rw [integral_sub hk hc]
  have hz : (∫ x, c • g x ∂ν) = 0 := by
    calc
      _ = c • (∫ x, g x ∂ν) := integral_smul c g
      _ = 0 := by rw [hzero]; exact smul_zero c
  rw [hz, sub_zero]

theorem renormalized_complex_cross_integral_identity {d : ℕ} (m : ℕ)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d)
    (hg : Integrable g ν) (hzero : (∫ x, g x ∂ν) = 0)
    (hraw : ∀ᵐ y ∂η, Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν)
    (hD : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)) (ν.prod η))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a) (ν.prod η)) :
    Integrable (fun y => w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν)) η ∧
      (∫ q, complexRenormalizedNormalIntegrand m w g a q ∂ν.prod η) =
        (∫ x, w x • (∫ y, inverseDistancePow (m + 1) x y • g x ∂η) ∂ν) -
          ∫ y, w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) ∂η := by
  let D := fun q : Ambient d × Ambient d => w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)
  let F := fun q : Ambient d × Ambient d => w q.2 •
    ((inverseDistancePow (m + 1) q.1 q.2 - inverseDistancePow (m + 1) a q.2) • g q.1)
  have heq : complexRenormalizedNormalIntegrand m w g a = fun q => D q - F q := by
    funext q
    dsimp only [D, F, complexRenormalizedNormalIntegrand]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hDF : Integrable (fun q => D q - F q) (ν.prod η) := by
    rwa [← heq]
  have hF : Integrable F (ν.prod η) := by
    have hh := hD.sub hDF
    change Integrable (fun q => D q - (D q - F q)) (ν.prod η) at hh
    simpa only [sub_sub_cancel] using! hh
  have hc : (fun y => ∫ x, F (x, y) ∂ν) =ᵐ[η]
      fun y => w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) := by
    filter_upwards [hraw] with y hy
    have hz := (mean_zero_subtracted_kernel_test_integral ν g hg hzero
      (fun x => inverseDistancePow (m + 1) x y) hy (inverseDistancePow (m + 1) a y)).2
    calc
      _ = w y • (∫ x, (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y) • g x ∂ν) :=
        integral_smul (w y) _
      _ = _ := congrArg (fun z : ℂ => w y • z) hz
  have hFint : (∫ q, F q ∂ν.prod η) =
      ∫ y, w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) ∂η :=
    (integral_prod_symm F hF).trans (integral_congr_ae hc)
  have hDint : (∫ q, D q ∂ν.prod η) =
      ∫ x, w x • (∫ y, inverseDistancePow (m + 1) x y • g x ∂η) ∂ν := by
    refine (integral_prod D hD).trans (integral_congr_ae (Eventually.of_forall ?_))
    intro x
    exact integral_smul (w x) _
  refine ⟨hF.integral_prod_right.congr hc, ?_⟩
  rw [heq, integral_sub hD hF, hFint, hDint]

end

end RieszRectifiability

end OAI
