import OAI.Geometry.RCD.Transport.RenyiFiniteAdditivity

namespace OAI

/-! # Exact extended Rényi additivity for finite length decompositions

This version works against the full sigma-finite reference measure. No
localization or finiteness of the reference volume is required.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem renyiIntegral_add_mutuallySingular (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (hs : ν₀ ⟂ₘ ν₁)
    {N : ℝ} (hN : 1<N) :
    renyiIntegral μ (ν₀+ν₁) N=renyiIntegral μ ν₀ N+renyiIntegral μ ν₁ N := by
  have hq : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN)
  have he : (fun x => (ν₀+ν₁).rnDeriv μ x^(1-1/N)) =ᵐ[μ]
      fun x => ν₀.rnDeriv μ x^(1-1/N)+ν₁.rnDeriv μ x^(1-1/N) := by
    filter_upwards [Measure.rnDeriv_add ν₀ ν₁ μ,rnDeriv_disjoint_ae μ ν₀ ν₁ hs] with x hx hd
    rw [hx]
    rcases hd with hd | hd
    · simp only [Pi.add_apply,hd,zero_add,ENNReal.zero_rpow_of_pos hq]
    · simp only [Pi.add_apply,hd,add_zero,ENNReal.zero_rpow_of_pos hq]
  exact (lintegral_congr_ae he).trans
    (lintegral_add_left ((ν₀.measurable_rnDeriv μ).pow_const _ ) _)

theorem renyiIntegral_finset_additive {ι : Type*} (μ : Measure X) [SigmaFinite μ]
    (ν : ι → Measure X) [∀ i, IsFiniteMeasure (ν i)] (s : Finset ι)
    (hs : ∀ i∈s, ∀ j∈s, i≠j → ν i ⟂ₘ ν j) {N : ℝ} (hN : 1<N) :
    renyiIntegral μ (∑ i∈s, ν i) N=∑ i∈s, renyiIntegral μ (ν i) N := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hq : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN)
    calc
      _ = ∫⁻ _ : X, (0:ℝ≥0∞) ∂μ := lintegral_congr_ae ((Measure.rnDeriv_zero μ).mono
        (fun x hx => by
          rw [hx]
          change (0:ℝ≥0∞)^(1-1/N)=0
          exact ENNReal.zero_rpow_of_pos hq))
      _ = 0 := lintegral_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsep : ν a ⟂ₘ ∑ i∈s, ν i := mutuallySingular_finset_sum_right ν (ν a) s
      (fun i hi => hs a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun he => ha (he ▸ hi)))
    rw [renyiIntegral_add_mutuallySingular μ (ν a) _ hsep hN,
      ih (fun i hi j hj hij => hs i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij),
      Finset.sum_insert ha]

theorem renyiIntegral_smul (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c≠∞) {N : ℝ} (hN : 1<N) :
    renyiIntegral μ (c • ν) N=c^(1-1/N)*renyiIntegral μ ν N := by
  have hq : 0≤1-1/N := sub_nonneg.mpr ((div_le_one (by linarith : 0<N)).mpr hN.le)
  have he : (fun x => (c • ν).rnDeriv μ x^(1-1/N)) =ᵐ[μ]
      fun x => c^(1-1/N)*ν.rnDeriv μ x^(1-1/N) := by
    filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ν μ hc] with x hx
    rw [hx]
    exact ENNReal.mul_rpow_of_nonneg c (ν.rnDeriv μ x) hq
  exact (lintegral_congr_ae he).trans
    (lintegral_const_mul _ ((ν.measurable_rnDeriv μ).pow_const _))

end RegularPointCoordinates

end

end OAI
