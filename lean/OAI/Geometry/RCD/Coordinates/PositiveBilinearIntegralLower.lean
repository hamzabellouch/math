import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # An integrated lower bound for positive quadratic forms

Weak mixed-pairing convergence and a uniform norm bound suffice. Strong
convergence of vectors or convergence of pointwise energies is not needed.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Y]

theorem positive_bilinear_integral_lower
    (P : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ x, 0 ≤ P x x)
    (hsymm : ∀ x y, P x y = P y x) (ν : Measure Y)
    (u : ℕ → Y → E) (v : Y → E)
    (hu : ∀ k, AEStronglyMeasurable (u k) ν) (hv : AEStronglyMeasurable v ν)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k, ∀ᵐ t ∂ν, ‖u k t‖ ≤ C)
    (hvb : ∀ᵐ t ∂ν, ‖v t‖ ≤ C)
    (hp : ∀ᵐ t ∂ν, Tendsto (fun k => P (u k t) (v t)) atTop (𝓝 (P (v t) (v t))))
    (θ : Y → ℝ) (hθ : Integrable θ ν) (hθ0 : ∀ᵐ t ∂ν, 0 ≤ θ t)
    {A : ℝ} (he : Tendsto (fun k => ∫ t, θ t*P (u k t) (u k t) ∂ν) atTop (𝓝 A)) :
    (∫ t, θ t*P (v t) (v t) ∂ν) ≤ A := by
  let D := ‖P‖*C*C
  have hbound {f g : Y → E} (hf : ∀ᵐ t ∂ν, ‖f t‖ ≤ C)
      (hg : ∀ᵐ t ∂ν, ‖g t‖ ≤ C) : ∀ᵐ t ∂ν, ‖P (f t) (g t)‖ ≤ D := by
    filter_upwards [hf,hg] with t ht hs
    exact (P.le_opNorm₂ _ _).trans (by dsimp only [D]; gcongr)
  have hInt {f g : Y → E} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
      (hfb : ∀ᵐ t ∂ν, ‖f t‖ ≤ C) (hgb : ∀ᵐ t ∂ν, ‖g t‖ ≤ C) :
      Integrable (fun t => θ t*P (f t) (g t)) ν :=
    hθ.mul_bdd (P.aestronglyMeasurable_comp₂ hf hg) (hbound hfb hgb)
  have hmix : Tendsto (fun k => ∫ t, θ t*P (u k t) (v t) ∂ν) atTop
      (𝓝 (∫ t, θ t*P (v t) (v t) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => |θ t| *D)
    · intro k
      exact hθ.aestronglyMeasurable.mul (P.aestronglyMeasurable_comp₂ (hu k) hv)
    · exact hθ.abs.mul_const D
    · intro k
      filter_upwards [hbound (hb k) hvb] with t ht
      rw [norm_mul,Real.norm_eq_abs (θ t)]
      exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    · filter_upwards [hp] with t ht
      exact ht.const_mul (θ t)
  have hi (k : ℕ) :
      2*(∫ t, θ t*P (u k t) (v t) ∂ν)-(∫ t, θ t*P (v t) (v t) ∂ν) ≤
        ∫ t, θ t*P (u k t) (u k t) ∂ν := by
    rw [← integral_const_mul,← integral_sub ((hInt (hu k) hv (hb k) hvb).const_mul 2)
      (hInt hv hv hvb hvb)]
    apply integral_mono_ae ((hInt (hu k) hv (hb k) hvb).const_mul 2 |>.sub (hInt hv hv hvb hvb))
      (hInt (hu k) (hu k) (hb k) (hb k))
    filter_upwards [hθ0] with t ht
    have hn := hpos (u k t-v t)
    simp only [map_sub,sub_apply] at hn
    rw [hsymm (v t) (u k t)] at hn
    have hh := mul_nonneg ht hn
    change 2*(θ t*P (u k t) (v t))-θ t*P (v t) (v t) ≤ θ t*P (u k t) (u k t)
    nlinarith only [hh]
  have hh := le_of_tendsto_of_tendsto
    ((hmix.const_mul 2).sub_const (∫ t, θ t*P (v t) (v t) ∂ν)) he (Eventually.of_forall hi)
  linarith

end RegularPointCoordinates

end

end OAI
