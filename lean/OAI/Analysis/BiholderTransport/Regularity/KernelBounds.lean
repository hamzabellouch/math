import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.PartialDerivatives
import OAI.Analysis.BiholderTransport.LinearAlgebra.Calculus

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma kernel_rectangle_of_partial_lipschitz {C : E → E → ℝ} {S T : Set E}
    {K : ℝ≥0} (hT : Convex ℝ T)
    (hd : ∀ y∈S,∀ z∈T,DifferentiableAt ℝ (C y) z)
    (hLip : LipschitzOnWith K (fun q : E×E => fderiv ℝ (C q.1) q.2) (S×ˢT)) :
    ∀ y∈S,∀ y'∈S,∀ z∈T,∀ z'∈T,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖ := by
  intro y hy y' hy' z hz z' hz'
  have HH := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun q => C y' q-C y q)
    (f' := fun q => fderiv ℝ (C y') q-fderiv ℝ (C y) q)
    (fun q hq => ((hd y' hy' q hq).hasFDerivAt.sub (hd y hy q hq).hasFDerivAt).hasFDerivWithinAt)
    (C := (K:ℝ)*‖y'-y‖) (by
      intro q hq
      have H := hLip.dist_le_mul (y',q) ⟨hy',hq⟩ (y,q) ⟨hy,hq⟩
      simpa only [dist_eq_norm,Prod.dist_eq,dist_self,max_eq_left (dist_nonneg),←dist_eq_norm] using H)
    hT hz hz'
  rw [Real.norm_eq_abs] at HH
  convert HH using 1; ring_nf

lemma smooth_kernel_second_locally_bounded {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ q:E×E in 𝓝 (a,a),
      ‖fderiv ℝ (fderiv ℝ (C q.1)) q.2‖≤B := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hh : ContinuousAt (fun q:E×E => fderiv ℝ (fderiv ℝ (C q.1)) q.2) (a,a) :=
    (ContDiffAt.partial_snd_fderiv_two hc).continuousAt
  let B := ‖fderiv ℝ (fderiv ℝ (C a)) a‖+1
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  have HH := (Metric.tendsto_nhds (β := E×E)
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hh (1:ℝ) zero_lt_one
  filter_upwards [HH] with q hq
  have hd : ‖fderiv ℝ (fderiv ℝ (C q.1)) q.2-fderiv ℝ (fderiv ℝ (C a)) a‖<1 := by
    simpa only [dist_eq_norm] using hq
  have hn := norm_le_norm_sub_add (fderiv ℝ (fderiv ℝ (C q.1)) q.2)
    (fderiv ℝ (fderiv ℝ (C a)) a)
  dsimp only [B]
  linarith only [hd,hn]

lemma smooth_kernel_local_data {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ K : ℝ≥0, ∃ B : ℝ,0≤B ∧ ∃ r>0,
      (∀ y∈ball a r,∀ z∈ball a r,ContDiffAt ℝ 2 (C y) z) ∧
      (∀ y∈ball a r,∀ z∈ball a r,‖fderiv ℝ (fderiv ℝ (C y)) z‖≤B) ∧
      LipschitzOnWith K (fun q : E×E => fderiv ℝ (C q.1) q.2)
        (ball a r×ˢball a r) := by
  have hd := ContDiffAt.partial_snd_fderiv hc
  obtain ⟨K,U,hU,hK⟩ := (hd.of_le (by norm_num : (1:WithTop ℕ∞)≤∞)).exists_lipschitzOnWith
  obtain ⟨B,hB,hH⟩ := smooth_kernel_second_locally_bounded hc
  have hs : ∀ᶠ q:E×E in 𝓝 (a,a),ContDiffAt ℝ 2 (C q.1) q.2 := by
    filter_upwards [(hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by simp)] with q hq
    exact hq.comp (f := fun z:E => (q.1,z)) q.2 (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (hH.and hs))
  have H (y z:E) (hy:y∈ball a r) (hz:z∈ball a r) :=
    hrU (show (y,z)∈ball (a,a) r from by rw [←ball_prod_same]; exact ⟨hy,hz⟩)
  refine ⟨K,B,hB,r,hr,?_,?_,?_⟩
  · exact fun y hy z hz => (H y z hy hz).2.2
  · exact fun y hy z hz => (H y z hy hz).2.1
  · exact hK.mono (fun q hq => (H q.1 q.2 hq.1 hq.2).1)

lemma smooth_kernel_local_bounds {C : E → E → ℝ} {a:E}
    (hc : ContDiffAt ℝ ∞ (Function.uncurry C) (a,a)) :
    ∃ K B : ℝ,0≤K ∧ 0≤B ∧ ∃ r>0,
      (∀ y∈ball a r,∀ z∈ball a r,ContDiffAt ℝ 2 (C y) z) ∧
      (∀ y∈ball a r,∀ z∈ball a r,∀ z'∈ball a r,
        |C y z'-C y z-fderiv ℝ (C y) z (z'-z)|≤B*‖z'-z‖^2) ∧
      (∀ y∈ball a r,∀ y'∈ball a r,∀ z∈ball a r,∀ z'∈ball a r,
        |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖) := by
  obtain ⟨K,B,hB,r,hr,hs,hH,hK⟩ := smooth_kernel_local_data hc
  refine ⟨K,B,K.coe_nonneg,hB,r,hr,hs,?_,?_⟩
  · intro y hy z hz z' hz'
    exact first_order_remainder_le_of_hessian_bound (f := C y) (convex_ball a r) hB
      (hs y hy) (hH y hy) hz hz'
  · exact kernel_rectangle_of_partial_lipschitz (convex_ball a r)
      (fun y hy z hz => (hs y hy z hz).differentiableAt (by norm_num)) hK
end WeakMTWTransport

end

end OAI
