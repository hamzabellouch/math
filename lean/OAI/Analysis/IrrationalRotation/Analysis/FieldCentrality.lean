import OAI.Analysis.IrrationalRotation.Analysis.FiberCentrality
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

namespace OAI

namespace Invariant233.FiberCentrality

open MeasureTheory Filter
open scoped ENNReal

local notation "K" => lp (fun _ : ℤ => ℂ) 2

theorem ae_eq_scalar_of_ergodic_covariance
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → K →L[ℂ] K) (S : K →L[ℂ] K)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hscalar : ∀ᵐ x ∂μ, ∃ c : ℂ, A x = c • (1 : K →L[ℂ] K))
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : K →L[ℂ] K) := by
  let a : X → ℂ := fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0
  have hscalar' : ∀ᵐ x ∂μ, A x = a x • (1 : K →L[ℂ] K) := by
    filter_upwards [hscalar] with x hx
    obtain ⟨c, hc⟩ := hx
    have ha : a x = c := by
      dsimp [a]
      simp [hc]
    rw [ha]
    exact hc
  have hscalarσ : ∀ᵐ x ∂μ, A (σ x) = a (σ x) • (1 : K →L[ℂ] K) :=
    hσ.toMeasurePreserving.quasiMeasurePreserving.ae hscalar'
  have hSminus : S (lp.single 2 (-1 : ℤ) (1 : ℂ)) =
      lp.single 2 (0 : ℤ) (1 : ℂ) := by
    simpa using hS (-1)
  have hinv : a ∘ σ =ᵐ[μ] a := by
    filter_upwards [hscalar', hscalarσ, hcov] with x hx hσx hcovx
    have hv : S (A (σ x) (lp.single 2 (-1 : ℤ) (1 : ℂ))) =
        A x (S (lp.single 2 (-1 : ℤ) (1 : ℂ))) :=
      congrArg (fun L : K →L[ℂ] K => L (lp.single 2 (-1 : ℤ) (1 : ℂ))) hcovx
    rw [hσx, hx] at hv
    simp only [smul_apply, one_apply_eq_self,
      map_smul, hSminus] at hv
    have hv0 := congrArg (fun v : K => v (0 : ℤ)) hv
    simpa [a, Function.comp_def] using hv0
  obtain ⟨c, hc⟩ := hσ.ae_eq_const_of_ae_eq_comp₀ hm hinv
  refine ⟨c, ?_⟩
  filter_upwards [hscalar', hc] with x hx hcx
  exact hx.trans (congrArg (fun z : ℂ => z • (1 : K →L[ℂ] K)) hcx)

theorem ae_eq_scalar_of_diagonal_shift_and_ergodic_covariance
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A D : X → K →L[ℂ] K) (S : K →L[ℂ] K)
    (d : X → ℤ → ℂ)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hd : ∀ᵐ x ∂μ, Function.Injective (d x))
    (hD : ∀ᵐ x ∂μ, ∀ (v : K) (k : ℤ), D x v k = d x k * v k)
    (hAD : ∀ᵐ x ∂μ, A x * D x = D x * A x)
    (hAS : ∀ᵐ x ∂μ, A x * S = S * A x)
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : K →L[ℂ] K) := by
  apply ae_eq_scalar_of_ergodic_covariance μ σ hσ A S hS hm _ hcov
  filter_upwards [hd, hD, hAD, hAS] with x hdx hDx hADx hASx
  exact scalar_of_commute_diagonal_and_shift (A x) (D x) S (d x)
    hdx hDx hS hADx hASx

end Invariant233.FiberCentrality

end OAI
