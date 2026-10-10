import Mathlib
import OAI.Probability.SKBarriers.Interpolation.SKAdaptiveContinuity

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlock_field_variance_mono {N k : ℕ} (hN : 0 < N) (B β : ℝ)
    (a b : Fin (k+1) → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (hab : ∀ j, a j ≤ b j) :
    skBlockRoot N k B (fun j => β*Real.sqrt (a j))/(N:ℝ) ≤
      skBlockRoot N k B (fun j => β*Real.sqrt (b j))/(N:ℝ) := by
  let V : ℝ → Fin (k+1) → ℝ := fun u j => (1-u)*a j+u*b j
  let v : ℝ → Fin (k+1) → ℝ := fun u j => β*Real.sqrt (V u j)
  let f : ℝ → ℝ := fun u => skBlockRoot N k B (v u)/(N:ℝ)
  let E : ℝ → Fin (k+1) → ℝ := fun u l =>
    hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
      (blockMass (Fintype.card (Edge N)) N k)
      (blockExponent (skInteraction N) (fun _ => B/Real.sqrt (N:ℝ)) (v u))
      (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l)
  let d : ℝ → ℝ := fun u => ∑ j, (β^2/2)*(b j-a j)*
    (1-∑ l : Fin (k+1), if j ≤ l then ((k+1:ℕ):ℝ)⁻¹*E u l else 0)
  have hvcont : Continuous v := by
    apply continuous_pi
    intro j
    exact continuous_const.mul (Real.continuous_sqrt.comp
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)))
  have hf : Continuous f :=
    ((skBlockRoot_contDiff N k).continuous.comp (continuous_const.prodMk hvcont)).div_const _
  have hd : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d u) u := by
    intro u hu
    have hV (j : Fin (k+1)) : 0 < V u j :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hu.2.le) (ha j)) (mul_pos hu.1 (hb j))
    let vp : Fin (k+1) → ℝ := fun j => β*((b j-a j)/(2*Real.sqrt (V u j)))
    have hv : HasDerivAt v vp u := by
      apply hasDerivAt_pi.mpr
      intro j
      have HV : HasDerivAt (fun t => V t j) (b j-a j) u := by
        have H := (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).mul_const (a j)).add
          ((hasDerivAt_id u).mul_const (b j))
        exact H.congr_deriv (by ring)
      exact (HV.sqrt (hV j).ne').const_mul β
    have hvp (j : Fin (k+1)) : vp j*v u j = (β^2/2)*(b j-a j) := by
      dsimp only [v,vp]
      calc
        _ = ((β^2/2)*(b j-a j))*(Real.sqrt (V u j)/Real.sqrt (V u j)) := by ring
        _ = _ := by rw [div_self (Real.sqrt_pos.mpr (hV j)).ne',mul_one]
    have H := skBlockPressure_hasDerivAt hN (fun _ => B) v (hasDerivAt_const u B) hv
    dsimp only at H
    apply H.congr_deriv
    simp only [mul_zero,zero_div,zero_mul,zero_add,hvp]
    rfl
  have hdpos (u : ℝ) : 0 ≤ d u := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hab j)))
    apply sub_nonneg.mpr
    calc
      _ ≤ ∑ _ : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs
        · exact mul_le_of_le_one_right (by positivity) (hierarchyMeanOverlap_bounds _ _ _ _
            (fun i s => by cases s i <;> norm_num [spin]) _).2
        · positivity
      _ = 1 := uniformAtom_sum k
  have H : f 0 ≤ f 1 := by
    apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1) hf.continuousOn
      (fun u hu => (hd u (by simpa only [interior_Icc] using hu)).hasDerivWithinAt)
      (fun u _ => hdpos u)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [f,v,V,sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] using H
end SK.Analytic

end
end

end

end OAI
