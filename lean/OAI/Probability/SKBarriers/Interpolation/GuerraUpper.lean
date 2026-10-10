import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEndpoint

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fixed_field_summation (k : ℕ) (Q r w : Fin (k+1) → ℝ) :
    (∑ b, cumulativeGapMap k Q b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      Q (Fin.last k)-∑ l, w l*Q l*r l := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,cumulativeGapMap_sum,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (b : Fin (k+1)) : cumulativeGapMap k Q b*(if b ≤ l then w l*r l else 0) =
      (if b ≤ l then cumulativeGapMap k Q b else 0)*(w l*r l) := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul,cumulativeGapMap_partial_sum]
  ring

theorem quenched_le_extendedQuantileParisi {N k : ℕ} (hN : 0 < N) (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hgap : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) ≤ extendedQuantileParisi k β Q := by
  let h : ℝ → ℝ := fun t => β*Real.sqrt t
  let v : ℝ → Fin (k+1) → ℝ := fun t j => β*Real.sqrt (1-t)*Real.sqrt (cumulativeGapMap k Q j)
  let f : ℝ → ℝ := fun t => skBlockRoot N k (h t) (v t)/(N:ℝ)
  let C : ℝ := (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)
  let U := fun t => blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
  let r := fun t j => hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun i s => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let s := fun t j => hierarchyReplicaSecond (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let d := fun t => (β^2/4)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j)-
    (β^2/2)*(Q (Fin.last k)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)
  have hcont : Continuous f := by
    have hv : Continuous v := by
      apply continuous_pi
      intro j
      exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).mul continuous_const
    exact ((skBlockRoot_contDiff N k).continuous.comp
      ((continuous_const.mul Real.continuous_sqrt).prodMk hv)).div_const _
  have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d t) t := by
    intro t ht
    let hp := β*(1/(2*Real.sqrt t))
    let vp := fun j => β*(-1/(2*Real.sqrt (1-t)))*Real.sqrt (cumulativeGapMap k Q j)
    have hh : HasDerivAt h hp t := (Real.hasDerivAt_sqrt ht.1.ne').const_mul β
    have hv : HasDerivAt v vp t := by
      apply hasDerivAt_pi.mpr
      intro j
      simpa only [v,vp,Pi.sub_apply,id_eq,zero_sub] using ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt
        (by linarith [ht.2] : 1-t ≠ 0)).const_mul β).mul_const (Real.sqrt (cumulativeGapMap k Q j))
    have hhp : h t*hp/2 = β^2/4 := by
      have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
      dsimp only [h,hp]
      field_simp
      ring
    have hvp (j : Fin (k+1)) : vp j*v t j = -(β^2/2)*cumulativeGapMap k Q j := by
      have hs : Real.sqrt (1-t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
      dsimp only [vp,v]
      calc
        _ = -(β^2/2)*(Real.sqrt (cumulativeGapMap k Q j))^2*
          (Real.sqrt (1-t)/Real.sqrt (1-t)) := by ring
        _ = _ := by rw [div_self hs,mul_one,Real.sq_sqrt (hgap j)]
    have H := skBlockPressure_hasDerivAt hN h v hh hv
    dsimp only at H
    apply H.congr_deriv
    rw [hhp]
    simp only [hvp]
    have hsum : (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) =
        -(β^2/2)*(Q (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q l*r t l) := by
      rw [← fixed_field_summation k Q (r t) (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    change (β^2/4)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t l)+
      (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) = d t
    rw [hsum]
    dsimp only [d]
    ring
  have hbound (t : ℝ) : d t ≤ C := by
    have hs (j : Fin (k+1)) : 2*Q j*r t j-(Q j)^2 ≤ s t j := by
      have H := (hierarchyOverlapError_bounds _ (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
        (fun s i => by cases s i <;> norm_num [spin])
        (blockLevel (Fintype.card (Edge N)) N k j)).1
      rw [hierarchyOverlapError_eq_second_sub_sq _ _ _ _
        (fun s i => by cases s i <;> norm_num [spin])] at H
      change 0 ≤ s t j-(r t j)^2 at H
      nlinarith [sq_nonneg (r t j-Q j)]
    have H : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2)) ≤
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hs j) (by positivity))
    have he (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2) =
        2*(((k+1:ℕ):ℝ)⁻¹*Q j*r t j)-((k+1:ℕ):ℝ)⁻¹*(Q j)^2 := by ring
    simp only [he,Finset.sum_sub_distrib] at H
    rw [← Finset.mul_sum (s := Finset.univ) (f := fun j : Fin (k+1) => ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)] at H
    have HB := mul_le_mul_of_nonneg_left H (show 0 ≤ β^2/4 by positivity)
    dsimp only [d,C]
    nlinarith
  have H : f 1-C ≤ f 0 := by
    have HM : AntitoneOn (fun t => f t-C*t) (Set.Icc (0:ℝ) 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
        (hcont.sub (continuous_const.mul continuous_id)).continuousOn
        (fun t ht => ((hd t (by simpa only [interior_Icc] using ht)).sub
          ((hasDerivAt_id t).const_mul C)).hasDerivWithinAt)
        (fun t _ => by simpa only [mul_one] using sub_nonpos.mpr (hbound t))
    simpa using HM (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  have hzero : f 0 = scalarHierarchy (k+1) (quantileMass k)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 := by
    simp only [f,h,v,Real.sqrt_zero,mul_zero,sub_zero,Real.sqrt_one,mul_one,
      skBlockRoot_zero_disorder_scalar hN]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')
  have hone : f 1 = (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
    simp only [f,h,v,Real.sqrt_one,mul_one,sub_self,Real.sqrt_zero,mul_zero,zero_mul,
      skBlockRoot_zero_fields_eq]
  rw [hzero,hone] at H
  change _ ≤ _+C
  linarith
end SK.Analytic

end
end

end

end OAI
