import OAI.Geometry.EinsteinFour.FlowDifferentiability

namespace OAI

/-! The first-variation criterion also applies at negative times, by
reversing the actual autonomous equation. -/

namespace PositiveEinsteinFour.FlowCalculus

open Set
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_flow_endpoint_nonpos (f : E → E) (α : E × ℝ → E)
    (p : E) (S B : Set E) (hS : S ∈ 𝓝 p)
    (hB : Convex ℝ B) (hf : ∀ z ∈ B, DifferentiableAt ℝ f z)
    (K L : ℝ≥0) (T : ℝ) (hT : T ≤ 0)
    (hK : LipschitzOnWith K f B)
    (hL : LipschitzOnWith L (fderiv ℝ f) B)
    (hD : ∀ z ∈ B, ‖fderiv ℝ f z‖ ≤ K)
    (hα0 : ∀ q ∈ S, α (q, 0) = q)
    (hα : ∀ q ∈ S, ∀ t ∈ Icc T 0,
      HasDerivAt (fun s => α (q, s)) (f (α (q, t))) t)
    (hαB : ∀ q ∈ S, ∀ t ∈ Icc T 0, α (q, t) ∈ B)
    (V : ℝ → E →L[ℝ] E)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ E)
    (hV : ∀ t ∈ Icc T 0, HasDerivAt V
      ((fderiv ℝ f (α (p, t))).comp (V t)) t) :
    HasFDerivAt (fun q => α (q, T)) (V T) p := by
  have ht {t : ℝ} (ht : t ∈ Icc 0 (-T)) : -t ∈ Icc T 0 := by
    constructor <;> linarith [ht.1, ht.2]
  have hd (q : E) : fderiv ℝ (fun z => -f z) q = -fderiv ℝ f q := fderiv_fun_neg
  have hKn : LipschitzOnWith K (fun z => -f z) B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_neg_neg] using hK.dist_le_mul x hx y hy
  have hLn : LipschitzOnWith L (fderiv ℝ (fun z => -f z)) B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [hd, dist_neg_neg] using hL.dist_le_mul x hx y hy
  have hαr (q : E) (hq : q ∈ S) (t : ℝ) (ht' : t ∈ Icc 0 (-T)) :
      HasDerivAt (fun s => α (q, -s)) (-f (α (q, -t))) t := by
    simpa only [Function.comp_def, neg_one_smul] using
      (hα q hq (-t) (ht ht')).scomp t (hasDerivAt_id t).neg
  have hVr (t : ℝ) (ht' : t ∈ Icc 0 (-T)) :
      HasDerivAt (fun s => V (-s))
        ((fderiv ℝ (fun z => -f z) (α (p, -t))).comp (V (-t))) t := by
    simpa only [Function.comp_def, hd, ContinuousLinearMap.neg_comp, neg_one_smul] using
      (hV (-t) (ht ht')).scomp t (hasDerivAt_id t).neg
  have hr := hasFDerivAt_flow_endpoint (fun z => -f z)
    (fun qt => α (qt.1, -qt.2)) p S B hS hB
    (fun z hz => (hf z hz).neg) K L (-T) (neg_nonneg.mpr hT)
    hKn hLn
    (fun z hz => by simpa only [hd, norm_neg] using hD z hz)
    (by simpa only [neg_zero] using hα0) hαr
    (fun q hq t ht' => hαB q hq (-t) (ht ht'))
    (fun s => V (-s)) (by simpa only [neg_zero] using hV0) hVr
  simpa only [neg_neg] using hr

end
end PositiveEinsteinFour.FlowCalculus

end OAI
