import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.InverseKernelMassBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis

lemma inverse_observation_geometry_tendsto {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*ell i)) l (𝓝 0) := by
  have he1 : 0 < (21/5:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have he2 : 0 < (401/100:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
      (2*E*c⁻¹^4)*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) l (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((ha0.rpow_const_nhds_zero he1).const_mul (c⁻¹^4)).add
        ((ha0.rpow_const_nhds_zero he2).const_mul (2*E*c⁻¹^4))
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have hli := helli.1
    positivity
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have he1' : (a i)^3*(a i)^(6/5:ℝ) = (a i)^(21/5:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    have he2' : (a i)^3*(a i)^(101/100:ℝ) = (a i)^(401/100:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    calc
      _ ≤ (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*(E*(a i)^(101/100:ℝ))) := by
        gcongr
        exact helli.2
      _ = ((a i)^3*(a i)^(6/5:ℝ))*(t i)⁻¹^4+
          (2*E)*((a i)^3*(a i)^(101/100:ℝ))*(t i)⁻¹^4 := by ring
      _ = (a i)^(21/5:ℝ)*(t i)⁻¹^4+(2*E)*((a i)^(401/100:ℝ)*(t i)⁻¹^4) := by
        rw [he1',he2']; ring
      _ ≤ c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
          (2*E)*(c⁻¹^4*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) :=
        add_le_add (rpow_inv_pow_bound hai hc hti 4)
          (mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 4) (by positivity))
      _ = _ := by ring

theorem inverse_observation_error_tendsto {ι : Type*} {l : Filter ι}
    {a t ell Q : ι → ℝ} {c E L q : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ))
    (hQ : Tendsto (fun i => (a i)^3*Q i) l (𝓝 q)) :
    Tendsto (fun i => (a i)^6*(Q i*(L*(t i)⁻¹^4*Real.sqrt 3*
      ((a i)^(6/5:ℝ)+2*ell i)))) l (𝓝 0) := by
  have hh := (hQ.mul (inverse_observation_geometry_tendsto hc hE ha ha0 ht hell)).const_mul (L*Real.sqrt 3)
  simp only [mul_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun i => by ring)

end CoulombAtom

end

end OAI
