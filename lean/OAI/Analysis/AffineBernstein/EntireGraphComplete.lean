import Mathlib
import OAI.Analysis.AffineBernstein.UniformSphericalCap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGraphComplete
open Filter
open scoped Topology

lemma graphEDist_le_segment_fderiv_bound {n : ℕ} {O : Set (Space n)}
    (f : Space n → ℝ) (x y : Space n) {M : ℝ} (hM : 0 ≤ M)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x+t • (y-x) ∈ O)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x+t • (y-x))‖ ≤ M) :
    graphEDist O f x y ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
  let γ : ℝ → Space n := fun t => x+t • (y-x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hp : graphPathLength f γ ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((1+M)*‖y-x‖) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0:ℝ) 1) t = y-x from derivWithin_baseSegment x (y-x) ht]
        apply ENNReal.ofReal_le_ofReal
        have H := (fderiv ℝ f (γ t)).le_opNorm (y-x)
        have H' : |fderiv ℝ f (γ t) (y-x)| ≤ M*‖y-x‖ := by
          simpa only [Real.norm_eq_abs] using H.trans (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity,?_⟩
        have Hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (norm_nonneg _)) |>.mpr H'
        rw [sq_abs] at Hsq
        nlinarith [mul_nonneg hM (sq_nonneg ‖y-x‖)]
      _ = _ := by simp
  apply le_trans _ hp
  unfold graphEDist
  exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
    (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
      (iInf_le_of_le (by simp [γ]) le_rfl))))

/-- An entire C∞ graph is complete for the literal induced Euclidean path
metric, not merely for the ambient chord metric. Straight segments and a
local derivative bound produce intrinsic convergence of every Cauchy sequence. -/
lemma euclideanGraphComplete_entire {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) : EuclideanGraphComplete univ f := by
  intro x _ hc
  have hcx : CauchySeq x := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun i hi j hj => ?_⟩
    have H := (enorm_sub_le_graphEDist univ f (x i) (x j)).trans_lt (hN i hi j hj)
    rw [← ofReal_norm,ENNReal.ofReal_lt_ofReal_iff hε] at H
    simpa only [dist_eq_norm,norm_sub_rev] using H
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hcx
  have hdf : ContinuousAt (fderiv ℝ f) a :=
    ((hf.contDiffAt.fderiv_right (m := ∞) (by simp))).continuousAt
  obtain ⟨δ,hδ,hδb⟩ := Metric.continuousAt_iff.mp hdf 1 zero_lt_one
  let M : ℝ := ‖fderiv ℝ f a‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbd : ∀ z ∈ Metric.ball a δ, ‖fderiv ℝ f z‖ ≤ M := by
    intro z hz
    have H := hδb hz
    have HT := norm_le_norm_add_norm_sub (fderiv ℝ f a) (fderiv ℝ f z)
    rw [dist_eq_norm] at H
    rw [norm_sub_rev] at HT
    dsimp [M]
    linarith
  refine ⟨a,mem_univ a,?_⟩
  intro ε hε
  have hp : 0 < 1+M := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ha (min δ (ε/(1+M))) (lt_min hδ (div_pos hε hp))
  refine ⟨N,fun i hi => ?_⟩
  have Hi := hN i hi
  have hib : x i ∈ Metric.ball a δ := lt_of_lt_of_le Hi (min_le_left _ _)
  have hab : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hs : ∀ t ∈ Icc (0:ℝ) 1, x i+t • (a-x i) ∈ Metric.ball a δ := by
    intro t ht
    have H := (convex_ball a δ) hib hab (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
    convert H using 1
    module
  apply (graphEDist_le_segment_fderiv_bound f (x i) a hM (fun _ _ => mem_univ _) (fun t ht => hbd _ (hs t ht))).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have Hnorm : ‖a-x i‖ < ε/(1+M) := by
    simpa only [dist_eq_norm,norm_sub_rev] using lt_of_lt_of_le Hi (min_le_right _ _)
  simpa only [mul_comm] using (lt_div_iff₀ hp).mp Hnorm

end EntireGraphComplete


end
end AffineBernstein
end

end OAI
