import Mathlib
import OAI.Analysis.AffineBernstein.PositiveDerivative
import OAI.Analysis.AffineBernstein.ConvexGradientBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section GraphPatchArea
variable {n : ℕ}

lemma jacobian_geometric_mean_image_bound {K : Set (Space n)} (hK : MeasurableSet K)
    {F G : Space n → Space n}
    {F' G' : Space n → Space n →L[ℝ] Space n}
    (hF : ∀ x ∈ K, HasFDerivWithinAt F (F' x) K x)
    (hG : ∀ x ∈ K, HasFDerivWithinAt G (G' x) K x)
    (hiF : Set.InjOn F K) (hiG : Set.InjOn G K)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {d : Space n → ℝ}
    (hd : ∀ x ∈ K, d x = |(G' x).det|^p * |(F' x).det|^(1-p))
    {BF BG : Set (Space n)} (hbF : F '' K ⊆ BF) (hbG : G '' K ⊆ BG) :
    (∫⁻ x in K, ENNReal.ofReal (d x)) ≤
      (volume BG)^p * (volume BF)^(1-p) := by
  have hmF := aemeasurable_ofReal_abs_det_fderivWithin volume hK hF
  have hmG := aemeasurable_ofReal_abs_det_fderivWithin volume hK hG
  have hh := lintegral_geometric_mean_le (volume.restrict K) hp hp1 hmG hmF
  have he : (∫⁻ x in K, ENNReal.ofReal (d x)) =
      ∫⁻ x in K, (ENNReal.ofReal |(G' x).det|)^p *
        (ENNReal.ofReal |(F' x).det|)^(1-p) := by
    apply setLIntegral_congr_fun hK
    intro x hx
    dsimp only
    rw [hd x hx,ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (sub_pos.mpr hp1).le]
  rw [he]
  apply hh.trans
  rw [lintegral_abs_det_fderiv_eq_addHaar_image volume hK hG hiG,
    lintegral_abs_det_fderiv_eq_addHaar_image volume hK hF hiF]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (measure_mono hbG) hp.le)
    (ENNReal.rpow_le_rpow (measure_mono hbF) (sub_pos.mpr hp1).le)

lemma det_fderiv_reciprocal_gradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) (hi : gradient u x i ≠ 0) :
    (fderiv ℝ (reciprocalChart i ∘ gradient u) x).det =
      -((gradient u x i)⁻¹)^(n+1) * (hessian u x).det := by
  have hr := (contDiffAt_reciprocalChart i hi).differentiableAt (by simp)
  have hg := (contDiffAt_gradient hu).differentiableAt (by simp)
  rw [(hr.hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
  change LinearMap.det ((fderiv ℝ (reciprocalChart i) (gradient u x)).toLinearMap.comp
    (fderiv ℝ (gradient u) x).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (fderiv ℝ (reciprocalChart i) (gradient u x)).det *
    (fderiv ℝ (gradient u) x).det = _
  rw [det_fderiv_reciprocalChart i hi,det_fderiv_gradient_eq_hessian hu]

lemma graph_area_jacobian_factor {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef)
    (i : Fin n) (hi : gradient u x i ≠ 0) :
    (hessian u x).det ^ (1/((n:ℝ)+2)) =
      |(fderiv ℝ (reciprocalChart i ∘ gradient u) x).det|^(1/((n:ℝ)+2)) *
      |(fderiv ℝ (graphProjection u i) x).det|^(1-1/((n:ℝ)+2)) := by
  rw [det_fderiv_reciprocal_gradient hu i hi,det_fderiv_graphProjection hu i,
    abs_mul,abs_neg,abs_pow,abs_inv,abs_of_pos hpos.det_pos]
  have ha : 0 < |gradient u x i| := abs_pos.mpr hi
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  rw [Real.mul_rpow (by positivity) hpos.det_pos.le]
  rw [← Real.rpow_natCast (|gradient u x i|⁻¹),
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ |gradient u x i|⁻¹),
    Real.inv_rpow ha.le]
  rw [mul_comm ((|gradient u x i| ^ ((n+1:ℕ) * (1/((n:ℝ)+2))))⁻¹),mul_assoc]
  have hexp : 1-1/((n:ℝ)+2) = (n+1:ℕ) * (1/((n:ℝ)+2)) := by
    push_cast
    field_simp
    ring
  rw [hexp,inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne',mul_one]

lemma graph_area_dominant_patch_bound {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hcu : ConvexOn ℝ Ω u)
    (i : Fin n) (hm : ∀ x ∈ K, 1 ≤ |gradient u x i| ∧ ∀ j, |gradient u x j| ≤ |gradient u x i|)
    (hs : (∀ x ∈ K, 0 < gradient u x i) ∨ (∀ x ∈ K, gradient u x i < 0))
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)) := by
  have hux (x) (hx : x ∈ Ω) := hu.contDiffAt (hΩ.mem_nhds hx)
  have hi (x) (hx : x ∈ K) : gradient u x i ≠ 0 := by
    have := (hm x hx).1
    intro he
    norm_num [he] at this
  apply jacobian_geometric_mean_image_bound hK
    (fun x hx => ((contDiffAt_graphProjection (hux x (hKΩ hx)) i).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => (((contDiffAt_reciprocalChart i (hi x hx)).comp x
      (contDiffAt_gradient (hux x (hKΩ hx)))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (graphProjection_injOn_signed hcu (fun x hx => (hux x hx).differentiableAt (by simp)) i hKΩ hs)
    ((reciprocalChart_injOn i).comp
      ((gradient_injOn_of_hessian_posDef hΩ hc hu hp).mono hKΩ) (fun x hx => hi x hx))
    (by positivity) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; rw [div_lt_one (by positivity)]; linarith)
    (fun x hx => graph_area_jacobian_factor (hux x (hKΩ hx)) (hp x (hKΩ hx)) i (hi x hx))
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    apply norm_le_card_of_coord_bound hR
    intro j
    by_cases hj : j=i
    · simpa [graphProjection,hj] using huR x hx
    · simpa [graphProjection,hj] using hxR x hx j
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    simpa using norm_le_card_of_coord_bound (by norm_num : (0:ℝ)≤1)
      (reciprocalChart_coord_le_one i (hm x hx).1 (hm x hx).2)

end GraphPatchArea

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
