import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKAdaptiveContinuity

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlock_smallField_cost {N k : ℕ} (hN : 0 < N) (β : ℝ)
    {η : ℝ} (hη : 0 < η) :
    skBlockRoot N k β (fun _ => β*Real.sqrt η)/(N:ℝ)-
      skBlockRoot N k β (fun _ => 0)/(N:ℝ) ≤ β^2/2*((k+1:ℕ):ℝ)*η := by
  let v : ℝ → Fin (k+1) → ℝ := fun u _ => β*Real.sqrt (u*η)
  let f : ℝ → ℝ := fun u => skBlockRoot N k β (v u)/(N:ℝ)
  let d : ℝ → ℝ := fun u => β^2*η/2*∑ b : Fin (k+1), (1-
    ∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
        (blockMass (Fintype.card (Edge N)) N k)
        (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (v u))
        (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l) else 0)
  have hvcont : Continuous v := by
    apply continuous_pi
    intro b
    exact continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.mul continuous_const))
  have hf : Continuous f :=
    ((skBlockRoot_contDiff N k).continuous.comp (continuous_const.prodMk hvcont)).div_const _
  have hd : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d u) u := by
    intro u hu
    let vp : Fin (k+1) → ℝ := fun _ => β*(η/(2*Real.sqrt (u*η)))
    have hs : Real.sqrt (u*η) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu.1 hη)).ne'
    have hv : HasDerivAt v vp u := by
      apply hasDerivAt_pi.mpr
      intro b
      exact ((hasDerivAt_mul_const η (x := u)).sqrt (mul_pos hu.1 hη).ne').const_mul β
    have hvp (b : Fin (k+1)) : vp b*v u b = β^2*η/2 := by
      dsimp only [v,vp]
      calc
        _ = (β^2*η/2)*(Real.sqrt (u*η)/Real.sqrt (u*η)) := by ring
        _ = _ := by rw [div_self hs,mul_one]
    have H := skBlockPressure_hasDerivAt hN (fun _ => β) v (hasDerivAt_const u β) hv
    dsimp only at H
    apply H.congr_deriv
    simp only [mul_zero,zero_div,zero_mul,zero_add,hvp,← Finset.mul_sum]
    rfl
  have hb (u : ℝ) : d u ≤ β^2/2*((k+1:ℕ):ℝ)*η := by
    have hsum : (∑ b : Fin (k+1), (1-
        ∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
          hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
            (blockMass (Fintype.card (Edge N)) N k)
            (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (v u))
            (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l) else 0)) ≤
        ((k+1:ℕ):ℝ) := by
      calc
        _ ≤ ∑ _ : Fin (k+1), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro b _
          apply sub_le_self
          apply Finset.sum_nonneg
          intro l _
          split_ifs
          · exact mul_nonneg (by positivity) (hierarchyMeanOverlap_bounds _ _ _ _
              (fun i s => by cases s i <;> norm_num [spin]) _).1
          · exact le_rfl
        _ = _ := by simp
    calc
      d u ≤ β^2*η/2*((k+1:ℕ):ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have H : f 1-f 0 ≤ ∫ _ in (0:ℝ)..1, β^2/2*((k+1:ℕ):ℝ)*η := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num) hf.continuousOn
      (fun u hu => (hd u hu).hasDerivWithinAt) (continuousOn_const.integrableOn_Icc)
    exact fun u _ => hb u
  simpa [f,v] using H

theorem cumulativeGapMap_initial (k : ℕ) (η : ℝ) :
    cumulativeGapMap k (fun j => ((j.val:ℝ)+1)*η) = fun _ => η := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp only [cumulativeGapMap_succ,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring

theorem skAdaptivePressure_initial_cost {N k : ℕ} (hN : 0 < N) (β : ℝ)
    {η : ℝ} (hη : 0 < η) :
    skAdaptivePressure N k β (fun j => ((j.val:ℝ)+1)*η) 0 ≤
      skBlockRoot N k β (fun _ => 0)/(N:ℝ)+β^2/2*((k+1:ℕ):ℝ)*η := by
  have H := skBlock_smallField_cost (k := k) hN β hη
  simp only [skAdaptivePressure,sub_zero,Real.sqrt_one,mul_one,cumulativeGapMap_initial]
  linarith
end SK.Analytic

end
end

end

end OAI
