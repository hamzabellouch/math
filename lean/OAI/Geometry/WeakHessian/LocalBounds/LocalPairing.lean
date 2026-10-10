import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerResolventDavies
import OAI.Geometry.WeakHessian.LocalBounds.AbsGammaLipschitz
import OAI.Geometry.WeakHessian.LocalBounds.WeightedPairing
import OAI.Geometry.WeakHessian.Sobolev.QuadraticGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile44
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.local_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A φ : X → ℝ}
    (hu : IsLaplacian m u A) (hφ : LocalSobolev m φ)
    (hAφ : Integrable (fun x => A x*φ x) m)
    (hγ : Integrable (gamma m u φ) m)
    (hDφ : Integrable (fun x => |φ x| *weakGradient m u x) m) :
    (∫ x,A x*φ x ∂m) = -(∫ x,gamma m u φ x ∂m) := by
  let : Nonempty X := ⟨o⟩
  have hχs (n : ℕ) := localSobolev_of_lipschitz hfin (radialCutoff_lipschitz o n)
  have hχB (n : ℕ) : ∀ᵐ x ∂m, |weakGradient m (radialCutoff o n) x| ≤ ((n:ℝ)+1)⁻¹ := by
    filter_upwards [weakGradient_nonneg (m := m) (radialCutoff o n),
      weakGradient_le_lipschitz hfin (radialCutoff_lipschitz o n)] with x hn hb
    rwa [abs_of_nonneg hn]
  have hcross (n : ℕ) : ∀ᵐ x ∂m, |φ x*gamma m u (radialCutoff o n) x| ≤
      ((n:ℝ)+1)⁻¹*(|φ x| *weakGradient m u x) := by
    filter_upwards [abs_gamma_lipschitz_le hfin hpar hu.1.2.1 (radialCutoff_lipschitz o n)] with x hx
    rw [abs_mul]
    simp only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hx
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (by ring)
  have hi (n : ℕ) : Integrable (fun x => φ x*gamma m u (radialCutoff o n) x) m :=
    (hDφ.const_mul _).mono' (hφ.1.aestronglyMeasurable.mul
      (gamma_aestronglyMeasurable hfin hu.1.2.1 (hχs n))) (hcross n)
  have he (n : ℕ) : (∫ x,A x*φ x*radialCutoff o n x ∂m) =
      -(∫ x,gamma m u φ x*radialCutoff o n x ∂m)-
      (∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) := by
    have H := hu.2.2 (fun x => φ x*radialCutoff o n x)
      (hφ.mul_lipschitz_compactSupport hfin (radialCutoff_lipschitz o n) (radialCutoff_compact o n))
    have hp := gamma_mul_left hfin hpar hφ (hχs n) hu.1.2.1
      (ae_of_all _ fun x => by rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x) (hχB n)
    have hg : gamma m u (fun x => φ x*radialCutoff o n x) =ᵐ[m]
        (fun x => φ x*gamma m u (radialCutoff o n) x+radialCutoff o n x*gamma m u φ x) := by
      filter_upwards [hp,gamma_comm (m := m) u (fun x => φ x*radialCutoff o n x),
        gamma_comm (m := m) (radialCutoff o n) u,gamma_comm (m := m) φ u] with x h1 h2 h3 h4
      rw [h2,h1,h3,h4]
    have hg2 : Integrable (fun x => radialCutoff o n x*gamma m u φ x) m :=
      hγ.bdd_mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x)
    rw [integral_congr_ae hg,integral_add (hi n) hg2] at H
    simp_rw [mul_assoc,mul_comm (radialCutoff o n _)] at H ⊢
    linarith
  have hn (n : ℕ) : ‖∫ x,φ x*gamma m u (radialCutoff o n) x ∂m‖ ≤
      ((n:ℝ)+1)⁻¹*(∫ x,|φ x| *weakGradient m u x ∂m) := by
    simpa only [integral_const_mul] using norm_integral_le_of_norm_le (hDφ.const_mul ((n:ℝ)+1)⁻¹) (hcross n)
  have hc0 : Tendsto (fun n => ∫ x,φ x*gamma m u (radialCutoff o n) x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm hn
    simpa only [one_div,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (∫ x,|φ x| *weakGradient m u x ∂m)
  have H := (integral_radialCutoff_tendsto o hγ).neg.sub hc0
  simp only [sub_zero] at H
  simp_rw [← he] at H
  exact tendsto_nhds_unique (integral_radialCutoff_tendsto o hAφ) H

lemma IsLaplacian.quadratic_weighted_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A : Lp ℝ 2 m}
    (hu : IsLaplacian m u A) {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {R : ℝ} (hR : 0 < R) {φ : X → ℝ} (hφ : QuadraticLipschitzBound o R φ)
    (hφW : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hDW : MemLp (fun x => (dist x o+R)*Real.exp (-V x)) 2 m) :
    (∫ x,A x*φ x ∂m) = -(∫ x,gamma m u φ x ∂m) := by
  have hD := hu.memLp_gradient_mul_exp hfin hpar hV hU hA
  have hφS := hφ.localSobolev hfin hR
  apply hu.local_pairing hfin hpar o hφS (weighted_pairing hA hφW).1
  · apply (weighted_pairing hD hDW).1.mono' (gamma_aestronglyMeasurable hfin hu.1.2.1 hφS)
    filter_upwards [abs_gamma_le hfin hpar hu.1.2.1 hφS,hφ.gradient_le hfin hR,
      weakGradient_nonneg (m := m) u] with x hx hy hn
    exact hx.trans (mul_le_mul_of_nonneg_left hy hn)
  · have ha : MemLp (fun x => |φ x| *Real.exp (-V x)) 2 m := by
      convert hφW.norm using 1
      funext x
      simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have H := (weighted_pairing hD ha).1
    simpa only [mul_comm] using H
end WeakHessian

end
end InlinedFile44

end OAI
