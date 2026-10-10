import Mathlib
import OAI.Geometry.CubicTorus.Variation.ComponentDivergence

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_rescale (n : Cover) (g : Plane → ℝ) {q : ℝ} (hq : q ≠ 0) (y : Plane) :
    normalGraph n g (q • y) = q • normalGraph n (fun y ↦ q⁻¹*g (q • y)) y := by
  simp only [normalGraph,smul_add,smul_smul]
  change normalPlaneLinearIsometry n (q • y)+_ = q • normalPlaneLinearIsometry n y+_
  rw [map_smul]
  congr 1
  congr 1
  field_simp

lemma rescaled_lipschitz_graph {g : Plane → ℝ} (hg : LipschitzWith (1/4) g)
    {q : ℝ} (hq : 0 < q) : LipschitzWith (1/4) (fun y ↦ q⁻¹*g (q • y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hg.dist_le_mul (q • x) (q • y)
  rw [dist_smul₀,Real.norm_of_nonneg hq.le,Real.dist_eq] at hh
  rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hq)]
  have hi := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hq).le
  norm_num at hi ⊢
  convert hi using 1
  all_goals first | rfl | field_simp

theorem actual_boundary_rescaled_graph_packet {E : Set Torus} {c n : Cover}
    (hn : ‖n‖ = 1) {q e C K ρ : ℝ} (hq : 0 < q) (hCe : C*e ≤ 1/2)
    (hgraph : ActualBoundaryGraph E c n q)
    (hnormal : BoundaryNormalChart E c n (q/272) e C K ρ) :
    ∃ (b : Cover) (g : Plane → ℝ) (N : Plane → Cover),
      ‖b‖ < 1/(544*4096) ∧ LipschitzWith (1/4) g ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), |g y| ≤ 1/(544*512)) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) (1/(544*2048))) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), ‖N y‖ = 1 ∧ ‖n-N y‖ ≤ 1/2) ∧
      (∀ j : ℕ, ∀ x ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        ∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
          dist x y ≤ ρ^j/680 → dist (N x) (N y) ≤ K*e*(1/2:ℝ)^j) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (1/(544*2048)),
        HasFDerivAt g (normalGraphDerivative n (N y)) y) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        b+normalGraph n g y ∈ rescaledActualBoundary E c q) ∧
      (∀ x ∈ rescaledActualBoundary E c q ∩ Metric.ball b (1/(544*128)),
        normalGraph n g (normalPlaneCoordinates n (x-b)) = x-b) := by
  classical
  obtain ⟨a,ha,g,hg,hgc,hpoints,hcovers⟩ := hgraph
  obtain ⟨ν,hνc,hν,hνmod⟩ := hnormal
  let b := q⁻¹ • (a-c)
  let G : Plane → ℝ := fun y ↦ q⁻¹*g (q • y)
  let f : Plane → Cover := fun y ↦ a+normalGraph n g (q • y)
  let N : Plane → Cover := fun y ↦ ν (f y)
  have hb : ‖b‖ < 1/(544*4096) := by
    dsimp only [b]
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hq).le,← dist_eq_norm]
    exact (inv_mul_lt_iff₀ hq).mpr (by nlinarith)
  have hsmall (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      q • y ∈ Metric.ball (0 : Plane) ((q/544)/1024) := by
    simp only [Metric.mem_closedBall,dist_zero_right] at hy
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg hq.le]
    nlinarith
  have hf : Continuous f := continuous_const.add
    ((normalGraph_lipschitz hn hg).continuous.comp (continuous_const_smul q))
  have hfpoint (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      f y ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c ((q/272)/128) := by
    have hh := hpoints (q • y) (hsmall y hy)
    refine ⟨?_,?_⟩
    · simpa only [mem_preimage,f,quotientMap_add] using hh.1
    · change dist (a+normalGraph n g (q • y)) c < (q/272)/128
      have hd := dist_triangle (a+normalGraph n g (q • y)) a c
      rw [show dist (a+normalGraph n g (q • y)) a = ‖normalGraph n g (q • y)‖ by
        rw [dist_eq_norm,add_sub_cancel_left]] at hd
      nlinarith [hh.2]
  have hNG (y : Plane) : f y = c+q • (b+normalGraph n G y) := by
    rw [show f y = a+q • normalGraph n G y from congrArg (a+·) (normalGraph_rescale n g hq.ne' y)]
    simp only [smul_add,b,smul_smul,mul_inv_cancel₀ hq.ne',one_smul]
    abel
  have hder (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) (1/(544*2048))) :
      HasFDerivAt G (normalGraphDerivative n (N y)) y := by
    have hyc := Metric.ball_subset_closedBall hy
    have hνy := hν (f y) (hfpoint y hyc)
    have ht : ⟪ν (f y),n⟫ ≠ 0 := ne_of_gt
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (transverse_inner_lower hn (hνy.2.1.trans hCe)))
    have hflat : BoundaryFlatAt (frontier (openRepresentative E))
        (quotientMap a+quotientMap (normalGraph n g (q • y))) (ν (f y)) := by
      simpa only [f,quotientMap_add] using hνy.2.2
    have hd := (normalGraph_hasFDerivWithinAt_of_flat hn hg
      (fun x hx ↦ (hpoints x hx).1) hflat ht).hasFDerivAt (Metric.isOpen_ball.mem_nhds (hsmall y hyc))
    have hd' : HasFDerivAt G
        (q⁻¹ • (normalGraphDerivative n (N y)).comp (q • ContinuousLinearMap.id ℝ Plane)) y :=
      (hd.comp y ((hasFDerivAt_id y).const_smul q)).const_mul q⁻¹
    apply hd'.congr_fderiv
    ext v
    simp [hq.ne']
  refine ⟨b,G,N,hb,rescaled_lipschitz_graph hg hq,?_,hνc.comp hf.continuousOn hfpoint,?_,?_,hder,?_,?_⟩
  · intro y hy
    have hnorm := (abs_real_inner_le_norm n (normalGraph n g (q • y)))
    rw [hn,one_mul,normalGraph_inner hn] at hnorm
    have hh := hnorm.trans_lt (hpoints _ (hsmall y hy)).2
    dsimp only [G]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hq)]
    exact le_of_lt ((inv_mul_lt_iff₀ hq).mpr (by nlinarith))
  · intro y hy
    exact ⟨(hν _ (hfpoint y hy)).1,(hν _ (hfpoint y hy)).2.1.trans hCe⟩
  · intro j x hx y hy hxy
    apply hνmod j (f x) (hfpoint x hx) (f y) (hfpoint y hy)
    have hh := (normalGraph_lipschitz hn hg).dist_le_mul (q • x) (q • y)
    rw [dist_smul₀,Real.norm_of_nonneg hq.le] at hh
    change dist (a+normalGraph n g (q • x)) (a+normalGraph n g (q • y)) ≤ _
    rw [dist_add_left]
    norm_num at hh
    nlinarith [mul_le_mul_of_nonneg_left hxy hq.le]
  · intro y hy
    change quotientMap (c+q • (b+normalGraph n G y)) ∈ frontier (openRepresentative E)
    rw [← hNG]
    exact (hfpoint y hy).1
  · intro x hx
    have he : c+q • x-a = q • (x-b) := by
      simp only [smul_sub,b,smul_smul,mul_inv_cancel₀ hq.ne',one_smul]
      abel
    have hxa : c+q • x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩
        Metric.ball a ((q/544)/128) := by
      refine ⟨hx.1,?_⟩
      have hx' : ‖x-b‖ < 1/(544*128) := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hx.2
      simp only [Metric.mem_ball,dist_eq_norm]
      rw [he,norm_smul,Real.norm_of_nonneg hq.le]
      nlinarith
    have hh := hcovers (c+q • x) hxa
    rw [he] at hh
    have hcoord : normalPlaneCoordinates n (q • (x-b)) = q • normalPlaneCoordinates n (x-b) := by

      exact (normalPlaneCoordinates n).map_smul q (x-b)
    rw [hcoord,normalGraph_rescale n g hq.ne'] at hh
    exact (smul_right_injective Cover hq.ne') hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverEssentialBoundary (A : Set Cover) : Set Cover :=
  {x | ∀ t : ℝ, 0 < t → 0 < volume.real (A ∩ Metric.ball x t) ∧
    0 < volume.real (Aᶜ ∩ Metric.ball x t)}

lemma cover_integral_indicator_ball {A : Set Cover} (hA : MeasurableSet A) (x : Cover) (t : ℝ) :
    (∫ y in Metric.ball x t, A.indicator (fun _ ↦ (1:ℝ)) y) =
      volume.real (A ∩ Metric.ball x t) := by
  rw [integral_indicator hA,Measure.restrict_restrict hA,integral_const,smul_eq_mul,mul_one,
    Measure.real_def,Measure.restrict_apply_univ]
  rfl

lemma localL1_set_integral_tendsto {R : ℝ} (g : ℕ → Cover → ℝ)
    (hg : ∀ i, Measurable (g i)) (hgb : ∀ i x, |g i x| ≤ 1)
    {f : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i x-f x|) atTop (𝓝 0)) {s : Set Cover} (hs : MeasurableSet s)
    (hsub : s ⊆ Metric.closedBall (0 : Cover) R) :
    Tendsto (fun i ↦ ∫ x in s, g i x) atTop (𝓝 (∫ x in s, f x)) := by
  have h := localL1_integral_tendsto g hg hgb hf hfb hlim s
  simpa only [Measure.restrict_restrict hs,inter_eq_left.mpr hsub] using h

lemma integral_blowupCharacteristic_ball_center {E : Set Torus} (hE : MeasurableSet E)
    (c p : Cover) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (hc : Metric.ball (c+r • p) (r*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    torusVolume.real (E ∩ Metric.ball (quotientMap (c+r • p)) (r*t)) =
      r^3 * ∫ x in Metric.ball p t, blowupCharacteristic E c r x := by
  have hh := integral_blowupCharacteristic_ball hE (c+r • p) hr t hc
  have he := integral_ball_affine_scaling (blowupCharacteristic E c r) p (by norm_num : (0:ℝ)<1) t
  have ha (y : Cover) : blowupCharacteristic E c r (p+y) =
      blowupCharacteristic E (c+r • p) r y := by
    simpa only [one_smul,mul_one] using blowupCharacteristic_affine E c p y r 1
  simp only [one_mul,one_pow,one_smul] at he
  simp_rw [ha] at he
  rw [he]
  exact hh

theorem isMinimizerAt_rescaled_boundary_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    (x : ℕ → Cover) {p : Cover} (hp : ‖p‖ < 1/2) (hxp : Tendsto x atTop (𝓝 p))
    (hboundary : ∀ᶠ i in atTop, x i ∈ rescaledActualBoundary E (c i) (r i)) :
    p ∈ coverEssentialBoundary A := by
  obtain ⟨S,b,hS,hb,hden⟩ := isMinimizerAt_two_sided_density hV hE hmin
  have hconvC : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic Eᶜ (c i) (r i) x-Aᶜ.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0) := by
    simp_rw [complement_blowup_error]
    exact hconv
  have hdensity (t : ℝ) (ht : 0 < t) (hts : t ≤ 1/2) :
      b/8*t^3 ≤ volume.real (A ∩ Metric.ball p t) ∧
      b/8*t^3 ≤ volume.real (Aᶜ ∩ Metric.ball p t) := by
    have hsub : Metric.ball p t ⊆ Metric.closedBall (0 : Cover) 1 := by
      intro y hy
      have hy' : ‖y-p‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hh := norm_add_le (y-p) p
      rw [sub_add_cancel] at hh
      simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖y‖ ≤ 1)
    have hint := localL1_set_integral_tendsto
      (fun i ↦ blowupCharacteristic E (c i) (r i))
      (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
      (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
      (measurable_const.indicator hA) (cover_indicator_bound A) hconv Metric.isOpen_ball.measurableSet hsub
    have hintc := localL1_set_integral_tendsto
      (fun i ↦ blowupCharacteristic Eᶜ (c i) (r i))
      (fun i ↦ measurable_blowupCharacteristic hE.compl (c i) (r i))
      (fun i ↦ blowupCharacteristic_bound Eᶜ (c i) (r i))
      (measurable_const.indicator hA.compl) (cover_indicator_bound Aᶜ) hconvC Metric.isOpen_ball.measurableSet hsub
    rw [cover_integral_indicator_ball hA] at hint
    rw [cover_integral_indicator_ball hA.compl] at hintc
    have hsmall : ∀ᶠ i in atTop, r i < 1/16 ∧ r i*t/2 < S := by
      have hs : Tendsto (fun i ↦ r i*t/2) atTop (𝓝 0) := by
        simpa only [zero_mul,zero_div] using (hrlim.mul_const t).div_const 2
      exact (hrlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16))).and
        (hs.eventually (Iio_mem_nhds hS))
    have hnear := hxp.eventually (Metric.ball_mem_nhds p (half_pos ht))
    have hlower : ∀ᶠ i in atTop,
        b/8*t^3 ≤ ∫ y in Metric.ball p t, blowupCharacteristic E (c i) (r i) y ∧
        b/8*t^3 ≤ ∫ y in Metric.ball p t, blowupCharacteristic Eᶜ (c i) (r i) y := by
      filter_upwards [hc,hsmall,hnear,hboundary] with i hci hri hxi hbi
      have hz : quotientMap (c i+r i • x i) ∈ volumeSupport E ∩ volumeSupport Eᶜ := by
        rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact hbi
      have hd := hden _ hz (r i*t/2) (div_pos (mul_pos (hr i) ht) (by norm_num)) hri.2.le
      have hdist : dist (quotientMap (c i+r i • x i)) (quotientMap (c i+r i • p)) < r i*t/2 := by
        rw [dist_eq_norm,← quotientMap_sub]
        apply lt_of_le_of_lt (norm_quotientMap_le _)
        rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg (hr i).le]
        have hxi' : ‖x i-p‖ < t/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hxi
        nlinarith [hr i]
      have hball : Metric.ball (quotientMap (c i+r i • x i)) (r i*t/2) ⊆
          Metric.ball (quotientMap (c i+r i • p)) (r i*t) := by
        intro z hz'
        have hh := dist_triangle z (quotientMap (c i+r i • x i)) (quotientMap (c i+r i • p))
        have hh' : dist z (quotientMap (c i+r i • x i)) < r i*t/2 := hz'
        change dist z (quotientMap (c i+r i • p)) < r i*t
        linarith
      have hcenter : ‖c i+r i • p-cubeCenter‖ ≤ 1/8 := by
        have hh := norm_add_le (c i-cubeCenter) (r i • p)
        rw [show c i-cubeCenter+r i • p = c i+r i • p-cubeCenter by abel,
          norm_smul,Real.norm_of_nonneg (hr i).le] at hh
        nlinarith [hr i]
      let d : MovingCenter.InteriorCenter := ⟨c i+r i • p,hcenter⟩
      have hcball : Metric.ball (c i+r i • p) (r i*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
        Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d)
          (by nlinarith [hr i] : r i*t < 3/8))
      have h₁ := hd.1.trans (measureReal_mono (μ := torusVolume) (inter_subset_inter Subset.rfl hball))
      have h₂ := hd.2.trans (measureReal_mono (μ := torusVolume) (inter_subset_inter Subset.rfl hball))
      rw [integral_blowupCharacteristic_ball_center hE (c i) p (hr i) t hcball] at h₁
      rw [integral_blowupCharacteristic_ball_center hE.compl (c i) p (hr i) t hcball] at h₂
      have he : b*(r i*t/2)^3 = (r i)^3*(b/8*t^3) := by ring
      rw [he] at h₁ h₂
      exact ⟨(mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp h₁,
        (mul_le_mul_iff_right₀ (pow_pos (hr i) 3)).mp h₂⟩
    exact ⟨ge_of_tendsto hint (hlower.mono fun _ h ↦ h.1),
      ge_of_tendsto hintc (hlower.mono fun _ h ↦ h.2)⟩
  intro t ht
  let u := min t (1/2)
  have hu : 0 < u := lt_min ht (by norm_num)
  have hh := hdensity u hu (min_le_right _ _)
  have hpos : 0 < b/8*u^3 := by positivity
  have hmono (B : Set Cover) : volume.real (B ∩ Metric.ball p u) ≤ volume.real (B ∩ Metric.ball p t) :=
    measureReal_mono (inter_subset_inter Subset.rfl (Metric.ball_subset_ball (min_le_left _ _)))
  exact ⟨hpos.trans_le (hh.1.trans (hmono A)),hpos.trans_le (hh.2.trans (hmono Aᶜ))⟩

theorem isMinimizerAt_rescaled_frontier_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {p : Cover} (hp : ‖p‖ < 1/2) (hboundary : p ∈ coverEssentialBoundary A)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ x ∈ Metric.ball p ε, x ∈ rescaledActualBoundary E (c i) (r i) := by
  let t := min ε (1/2)
  have ht : 0 < t := lt_min hε (by norm_num)
  have ht1 : t ≤ 1/2 := min_le_right _ _
  have hsub : Metric.ball p t ⊆ Metric.closedBall (0 : Cover) 1 := by
    intro y hy
    have hy' : ‖y-p‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    have hh := norm_add_le (y-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖y‖ ≤ 1)
  have hint := localL1_set_integral_tendsto
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv Metric.isOpen_ball.measurableSet hsub
  have hconvc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic Eᶜ (c i) (r i) x-Aᶜ.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0) := by
    simp_rw [complement_blowup_error]
    exact hconv
  have hintc := localL1_set_integral_tendsto
    (fun i ↦ blowupCharacteristic Eᶜ (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE.compl (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound Eᶜ (c i) (r i))
    (measurable_const.indicator hA.compl) (cover_indicator_bound Aᶜ) hconvc Metric.isOpen_ball.measurableSet hsub
  rw [cover_integral_indicator_ball hA] at hint
  rw [cover_integral_indicator_ball hA.compl] at hintc
  filter_upwards [hc,hrlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16)),
    hint.eventually (lt_mem_nhds (hboundary t ht).1),
    hintc.eventually (lt_mem_nhds (hboundary t ht).2)] with i hci hri hip hic
  have hcenter : ‖c i+r i • p-cubeCenter‖ ≤ 1/8 := by
    have hh := norm_add_le (c i-cubeCenter) (r i • p)
    rw [show c i-cubeCenter+r i • p = c i+r i • p-cubeCenter by abel,
      norm_smul,Real.norm_of_nonneg (hr i).le] at hh
    nlinarith [hr i]
  let d : MovingCenter.InteriorCenter := ⟨c i+r i • p,hcenter⟩
  have hcball : Metric.ball (c i+r i • p) (r i*t) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d)
      (by nlinarith [hr i] : r i*t < 3/8))
  have hp₁ : 0 < torusVolume.real (E ∩ Metric.ball (quotientMap (c i+r i • p)) (r i*t)) := by
    rw [integral_blowupCharacteristic_ball_center hE (c i) p (hr i) t hcball]
    exact mul_pos (pow_pos (hr i) 3) hip
  have hp₂ : 0 < torusVolume.real (Eᶜ ∩ Metric.ball (quotientMap (c i+r i • p)) (r i*t)) := by
    rw [integral_blowupCharacteristic_ball_center hE.compl (c i) p (hr i) t hcball]
    exact mul_pos (pow_pos (hr i) 3) hic
  obtain ⟨a,ha,haf⟩ := isMinimizerAt_two_phase_frontier_in_ball hV hE hmin _ _ hp₁ hp₂
  let x := (r i)⁻¹ • (a-c i)
  have he : c i+r i • x=a := by simp [x,smul_smul,(hr i).ne']
  refine ⟨x,?_,?_⟩
  · have he' : x-p = (r i)⁻¹ • (a-(c i+r i • p)) := by
      simp only [x,smul_sub,smul_add,smul_smul,inv_mul_cancel₀ (hr i).ne',one_smul]
      abel
    rw [Metric.mem_ball,dist_eq_norm,he',norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hr i)).le]
    have ha' : ‖a-(c i+r i • p)‖ < r i*t := by simpa only [Metric.mem_ball,dist_eq_norm] using ha
    exact ((inv_mul_lt_iff₀ (hr i)).mpr ha').trans_le (min_le_left _ _)
  · change quotientMap (c i+r i • x) ∈ frontier (openRepresentative E)
    rw [he]
    exact haf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normal_graph_C1_subsequence {n : Cover} (hn : ‖n‖ = 1)
    (g : ℕ → Plane → ℝ) (ν : ℕ → Plane → Cover) {R M : ℝ}
    (hg : ∀ i, LipschitzWith (1/4) (g i))
    (hbounded : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → |g i x| ≤ M)
    (hνcont : ∀ i, ContinuousOn (ν i) (Metric.closedBall (0 : Plane) R))
    (hνunit : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → ‖ν i x‖ = 1)
    (hνclose : ∀ i x, x ∈ Metric.closedBall (0 : Plane) R → ‖n-ν i x‖ ≤ 1/2)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x, x ∈ Metric.closedBall (0 : Plane) R →
        ∀ y, y ∈ Metric.closedBall (0 : Plane) R → dist x y < η → dist (ν i x) (ν i y) < ε)
    (hder : ∀ i x, x ∈ Metric.ball (0 : Plane) R →
      HasFDerivAt (g i) (normalGraphDerivative n (ν i x)) x) :
    ∃ (G : Plane → ℝ) (N : Plane → Cover) (φ : ℕ → ℕ),
      StrictMono φ ∧ LipschitzWith (1/4) G ∧
      ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) R) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) R) ∧
      (∀ x ∈ Metric.closedBall (0 : Plane) R, ‖N x‖ = 1 ∧ ‖n-N x‖ ≤ 1/2) ∧
      TendstoUniformlyOn (fun i ↦ g (φ i)) G atTop (Metric.closedBall (0 : Plane) R) ∧
      TendstoUniformlyOn (fun i ↦ ν (φ i)) N atTop (Metric.closedBall (0 : Plane) R) ∧
      ∀ x ∈ Metric.ball (0 : Plane) R, HasFDerivAt G (normalGraphDerivative n (N x)) x := by
  classical
  let D := Metric.closedBall (0 : Plane) R
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F : ℕ → D → ℝ × Cover := fun i x ↦ (g i x,ν i x)
  have hc (i : ℕ) : Continuous (F i) :=
    ((hg i).continuous.comp continuous_subtype_val).prodMk
      (continuousOn_iff_continuous_domRestrict.mp (hνcont i))
  have hb (i : ℕ) (x : D) : dist (F i x) (0 : ℝ × Cover) ≤ max M 1 := by
    rw [Prod.dist_eq]
    apply max_le
    · exact le_trans (by simpa only [F,Prod.fst_zero,Real.dist_eq,sub_zero] using hbounded i x x.property) (le_max_left _ _)
    · exact le_trans (by simpa only [F,Prod.snd_zero,dist_zero_right,hνunit i x x.property] using (le_refl (1:ℝ))) (le_max_right _ _)
  have hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i (x y : D), dist x y < η → dist (F i x) (F i y) < ε := by
    intro ε hε
    obtain ⟨η,hη,hηm⟩ := hmod ε hε
    refine ⟨min ε η,lt_min hε hη,?_⟩
    intro i x y hxy
    rw [Prod.dist_eq]
    apply max_lt
    · have ht := (hg i).dist_le_mul x y
      have hsmall : dist (x : Plane) y < ε := hxy.trans_le (min_le_left _ _)
      change dist (g i x) (g i y) < ε
      norm_num at ht
      linarith [dist_nonneg (x := (x : Plane)) (y := (y : Plane))]
    · exact hηm i x x.property y y.property (hxy.trans_le (min_le_right _ _))
  obtain ⟨f,φ,hfc,hφ,hu⟩ := exists_uniform_subseq_of_bounded_modulus F hc 0 (max M 1) hb hm
  let G₀ : Plane → ℝ := fun x ↦ if hx : x ∈ D then (f ⟨x,hx⟩).1 else 0
  let N : Plane → Cover := fun x ↦ if hx : x ∈ D then (f ⟨x,hx⟩).2 else 0
  have hgu : TendstoUniformlyOn (fun i ↦ g (φ i)) G₀ atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with i hi
    intro x hx
    have hh := hi ⟨x,hx⟩
    rw [Prod.dist_eq] at hh
    simpa only [G₀,dite_eq_left hx,F] using (max_lt_iff.mp hh).1
  have hnu : TendstoUniformlyOn (fun i ↦ ν (φ i)) N atTop D := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with i hi
    intro x hx
    have hh := hi ⟨x,hx⟩
    rw [Prod.dist_eq] at hh
    simpa only [N,dite_eq_left hx,F] using (max_lt_iff.mp hh).2
  have hGlip : LipschitzOnWith (1/4) G₀ D := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    exact le_of_tendsto ((hgu.tendsto_at hx).dist (hgu.tendsto_at hy))
      (Eventually.of_forall fun i ↦ (hg (φ i)).dist_le_mul x y)
  obtain ⟨G,hG,hGeq⟩ := hGlip.extend_real
  have hGconv : TendstoUniformlyOn (fun i ↦ g (φ i)) G atTop D := by
    apply hgu.congr_right
    exact hGeq
  have hNc : ContinuousOn N D := hnu.continuousOn
    (Frequently.of_forall (fun i ↦ hνcont (φ i)))
  have hNunit (x : Plane) (hx : x ∈ D) : ‖N x‖ = 1 := by
    apply tendsto_nhds_unique (hnu.tendsto_at hx |>.norm)
    simpa only [hνunit _ x hx] using (tendsto_const_nhds (x := (1:ℝ)) :
      Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1))
  have hNclose (x : Plane) (hx : x ∈ D) : ‖n-N x‖ ≤ 1/2 := by
    exact le_of_tendsto ((tendsto_const_nhds.sub (hnu.tendsto_at hx)).norm)
      (Eventually.of_forall fun i ↦ hνclose (φ i) x hx)
  have hmN : MapsTo N D (Metric.closedBall n (1/2)) := by
    intro x hx
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hNclose x hx
  have hderconv : TendstoUniformlyOn (fun i x ↦ normalGraphDerivative n (ν (φ i) x))
      (fun x ↦ normalGraphDerivative n (N x)) atTop D := by
    apply UniformContinuousOn.comp_tendstoUniformlyOn_eventually _ hmN
      ((isCompact_closedBall n (1/2)).uniformContinuousOn_of_continuous
        (normalGraphDerivative_continuousOn hn)) hnu
    apply Eventually.of_forall
    intro i x hx
    simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hνclose (φ i) x hx
  have hderG (x : Plane) (hx : x ∈ Metric.ball (0 : Plane) R) :
      HasFDerivAt G (normalGraphDerivative n (N x)) x :=
    hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
      (hderconv.mono Metric.ball_subset_closedBall) (fun i x hx ↦ hder (φ i) x hx)
      (fun x hx ↦ hGconv.tendsto_at (Metric.ball_subset_closedBall hx)) hx
  refine ⟨G,N,φ,hφ,hG,?_,hNc,fun x hx ↦ ⟨hNunit x hx,hNclose x hx⟩,hGconv,hnu,hderG⟩
  rw [show (1 : WithTop ℕ∞) = 0+1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp,fun x ↦ normalGraphDerivative n (N x),?_,fun x hx ↦ (hderG x hx).hasFDerivWithinAt⟩
  apply contDiffOn_zero.mpr
  exact ((normalGraphDerivative_continuousOn hn).comp hNc hmN).mono Metric.ball_subset_closedBall

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_residual_lipschitz {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : LipschitzWith (1/4) g) (b : Cover) :
    LipschitzWith (9/4) (fun x ↦ normalGraph n g (normalPlaneCoordinates n (x-b))-(x-b)) := by
  have ht : LipschitzWith 1 (fun x : Cover ↦ x-b) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right,NNReal.coe_one,one_mul,le_refl]
  have hh := (((normalGraph_lipschitz hn hg).comp
    ((normalPlaneCoordinates_lipschitz n).comp ht)).sub ht)
  norm_num at hh
  simpa only [map_sub] using hh

lemma normalGraph_norm_le {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖normalGraph n g y‖ ≤ ‖y‖+|g y| := by
  have hh := norm_add_le (normalPlaneEmbedding n y) (g y • n)
  simpa only [normalGraph,normalPlaneEmbedding_norm,norm_smul,Real.norm_eq_abs,hn,mul_one] using hh

theorem rescaled_actual_graph_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {n : Cover} (hn : ‖n‖ = 1) (b : ℕ → Cover) (g : ℕ → Plane → ℝ)
    (hb : ∀ i, ‖b i‖ ≤ 1/(544*4096))
    (hg : ∀ i, LipschitzWith (1/4) (g i))
    (hgb : ∀ i y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) → |g i y| ≤ 1/(544*512))
    (hpoints : ∀ i y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
      b i+normalGraph n (g i) y ∈ rescaledActualBoundary E (c i) (r i))
    (hcovers : ∀ i x, x ∈ rescaledActualBoundary E (c i) (r i) ∩ Metric.ball (b i) (1/(544*128)) →
      normalGraph n (g i) (normalPlaneCoordinates n (x-b i))=x-b i)
    (b₀ : Cover) (G : Plane → ℝ) (hG : LipschitzWith (1/4) G)
    (hbconv : Tendsto b atTop (𝓝 b₀))
    (hgconv : TendstoUniformlyOn g G atTop (Metric.closedBall (0 : Plane) (1/(544*2048)))) :
    ‖b₀‖ ≤ 1/(544*4096) ∧
    (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
      b₀+normalGraph n G y ∈ coverEssentialBoundary A) ∧
    (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
      x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b₀))=x-b₀) := by
  have hb₀ : ‖b₀‖ ≤ 1/(544*4096) := le_of_tendsto hbconv.norm (Eventually.of_forall hb)
  have hGb (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      |G y| ≤ 1/(544*512) := le_of_tendsto (hgconv.tendsto_at hy |>.abs)
        (Eventually.of_forall fun i ↦ hgb i y hy)
  have hpt (y : Plane) (hy : y ∈ Metric.closedBall (0 : Plane) (1/(544*2048))) :
      b₀+normalGraph n G y ∈ coverEssentialBoundary A := by
    apply isMinimizerAt_rescaled_boundary_limit hV hE hmin c r hr hrlim hc hA hconv
      (fun i ↦ b i+normalGraph n (g i) y)
    · have hy' : ‖y‖ ≤ 1/(544*2048) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
      have hh := norm_add_le b₀ (normalGraph n G y)
      have hh' := normalGraph_norm_le hn G y
      have hgy := hGb y hy
      linarith
    · change Tendsto (fun i ↦ b i+(normalPlaneEmbedding n y+g i y • n)) atTop
        (𝓝 (b₀+(normalPlaneEmbedding n y+G y • n)))
      exact hbconv.add (tendsto_const_nhds.add ((hgconv.tendsto_at hy).smul tendsto_const_nhds))
    · exact Eventually.of_forall fun i ↦ hpoints i y hy
  refine ⟨hb₀,hpt,?_⟩
  intro x hx
  have hx' : ‖x‖ < 1/(544*8192) := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hcoords (z : Cover) (hz : ‖z‖ ≤ 1/(544*4096)) :
      normalPlaneCoordinates n (x-z) ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) := by
    have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (x-z) 0
    simp only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] at hh
    have hh' := norm_sub_le x z
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith :
      ‖normalPlaneCoordinates n (x-z)‖ ≤ 1/(544*2048))
  constructor
  · intro hxA
    let F : ℕ → Cover → Cover := fun i z ↦
      normalGraph n (g i) (normalPlaneCoordinates n (z-b i))-(z-b i)
    let F₀ : Cover := normalGraph n G (normalPlaneCoordinates n (x-b₀))-(x-b₀)
    have harg : Tendsto (fun i ↦ normalPlaneCoordinates n (x-b i)) atTop
        (𝓝 (normalPlaneCoordinates n (x-b₀))) :=
      (normalPlaneCoordinates n).continuous.tendsto _ |>.comp (tendsto_const_nhds.sub hbconv)
    have heval := hgconv.tendsto_comp hG.continuous.continuousAt.continuousWithinAt
      (tendsto_nhdsWithin_iff.mpr ⟨harg,Eventually.of_forall fun i ↦ hcoords (b i) (hb i)⟩)
    have hFlim : Tendsto (fun i ↦ F i x) atTop (𝓝 F₀) := by
      apply Filter.Tendsto.sub _ (tendsto_const_nhds.sub hbconv)
      exact ((normalPlaneLinearIsometry n).continuous.tendsto _ |>.comp harg).add
        (heval.smul tendsto_const_nhds)
    have hz : ‖F₀‖=0 := by
      apply le_antisymm _ (norm_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      let δ := min (1/(544*2048)) (ε/3)
      have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
      have hap := isMinimizerAt_rescaled_frontier_approximation hV hE hmin c r hr hrlim hc hA hconv
        (by linarith : ‖x‖<1/2) hxA δ hδ
      have hevent : ∀ᶠ i in atTop, ‖F i x‖ ≤ 0+ε := by
        filter_upwards [hap] with i hi
        obtain ⟨z,hzx,hzb⟩ := hi
        have hzx' : dist z x < δ := hzx
        have hzball : z ∈ Metric.ball (b i) (1/(544*128)) := by
          have hh := dist_triangle z x (b i)
          have hxb := norm_sub_le x (b i)
          rw [dist_eq_norm x (b i)] at hh
          have hδs : δ ≤ 1/(544*2048) := min_le_left _ _
          change dist z (b i) < 1/(544*128)
          have hbi := hb i
          linarith
        have hFz : F i z=0 := sub_eq_zero.mpr (hcovers i z ⟨hzb,hzball⟩)
        have hh := (normalGraph_residual_lipschitz hn (hg i) (b i)).dist_le_mul x z
        change dist (F i x) (F i z) ≤ _ at hh
        rw [hFz,dist_zero_right,dist_comm x z] at hh
        norm_num at hh
        have hδs : δ ≤ ε/3 := min_le_right _ _
        linarith
      exact le_of_tendsto hFlim.norm hevent
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro hxe
    have hh := hpt (normalPlaneCoordinates n (x-b₀)) (hcoords b₀ hb₀)
    rw [hxe,add_sub_cancel] at hh
    exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_strong_limit_C1_graph {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|) atTop (𝓝 0))
    {n : Cover} (hn : ‖n‖ = 1) {e C K ρ : ℝ} (hρ : 0 < ρ) (hCe : C*e ≤ 1/2)
    (hpack : ∀ i, ActualBoundaryGraph E (c i) n (r i) ∧
      BoundaryNormalChart E (c i) n (r i/272) e C K ρ) :
    ∃ (b : Cover) (G : Plane → ℝ) (N : Plane → Cover),
      ‖b‖ ≤ 1/(544*4096) ∧ LipschitzWith (1/4) G ∧
      ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) (1/(544*2048))) ∧
      ContinuousOn N (Metric.closedBall (0 : Plane) (1/(544*2048))) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)), ‖N y‖ = 1 ∧ ‖n-N y‖ ≤ 1/2) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (1/(544*2048)), HasFDerivAt G (normalGraphDerivative n (N y)) y) ∧
      (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
        b+normalGraph n G y ∈ coverEssentialBoundary A) ∧
      (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
        x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b))=x-b) := by
  classical
  choose b g ν hb hg hgb hνc hν hmod hder hpoints hcovers using
    fun i ↦ actual_boundary_rescaled_graph_packet hn (hr i) hCe (hpack i).1 (hpack i).2
  obtain ⟨b₀,hb₀,ψ,hψ,hbconv⟩ := (isCompact_closedBall (0 : Cover) (1/(544*4096))).tendsto_subseq
    (fun i ↦ by simpa only [Metric.mem_closedBall,dist_zero_right] using (hb i).le)
  have hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x, x ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
        ∀ y, y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)) →
          dist x y < η → dist (ν (ψ i) x) (ν (ψ i) y) < ε := by
    intro ε hε
    have hlim : Tendsto (fun j : ℕ ↦ K*e*(1/2:ℝ)^j) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)).const_mul (K*e)
    obtain ⟨j,hj⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
    refine ⟨ρ^j/680,by positivity,fun i x hx y hy hxy ↦ ?_⟩
    exact (hmod (ψ i) j x hx y hy hxy.le).trans_lt hj
  obtain ⟨G,N,φ,hφ,hG,hGc,hNc,hNu,hGconv,hNconv,hGder⟩ :=
    normal_graph_C1_subsequence hn (fun i ↦ g (ψ i)) (fun i ↦ ν (ψ i))
      (fun i ↦ hg (ψ i)) (fun i ↦ hgb (ψ i)) (fun i ↦ hνc (ψ i))
      (fun i x hx ↦ (hν (ψ i) x hx).1) (fun i x hx ↦ (hν (ψ i) x hx).2) hm
      (fun i ↦ hder (ψ i))
  let χ : ℕ → ℕ := ψ ∘ φ
  have hχ : Tendsto χ atTop atTop := hψ.tendsto_atTop.comp hφ.tendsto_atTop
  have hh := rescaled_actual_graph_limit hV hE hmin
    (fun i ↦ c (χ i)) (fun i ↦ r (χ i)) (fun i ↦ hr (χ i)) (hrlim.comp hχ)
    (hχ.eventually hc) hA (hconv.comp hχ) hn
    (fun i ↦ b (χ i)) (fun i ↦ g (χ i)) (fun i ↦ (hb (χ i)).le)
    (fun i ↦ hg (χ i)) (fun i ↦ hgb (χ i)) (fun i ↦ hpoints (χ i))
    (fun i ↦ hcovers (χ i)) b₀ G hG (hbconv.comp hφ.tendsto_atTop) hGconv
  exact ⟨b₀,G,N,hh.1,hG,hGc,hNc,hNu,hGder,hh.2.1,hh.2.2⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_real_affine_preimage_ball_center {A : Set Cover} (hA : MeasurableSet A)
    (p x : Cover) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    volume.real (((fun y ↦ p+s • y) ⁻¹' A) ∩ Metric.ball x t) =
      s⁻¹^3*volume.real (A ∩ Metric.ball (p+s • x) (s*t)) := by
  have hB : MeasurableSet ((fun y : Cover ↦ p+s • y) ⁻¹' A) := hA.preimage (by fun_prop)
  rw [← volume_real_translate_ball hB x t]
  have he : (fun y ↦ x+y) ⁻¹' ((fun y ↦ p+s • y) ⁻¹' A) =
      (fun y ↦ (p+s • x)+s • y) ⁻¹' A := by
    ext y
    simp only [mem_preimage,smul_add,add_assoc]
  rw [he,volume_real_affine_preimage_ball hA (p+s • x) hs t]

lemma coverEssentialBoundary_affine {A : Set Cover} (hA : MeasurableSet A)
    (p x : Cover) {s : ℝ} (hs : 0 < s) :
    x ∈ coverEssentialBoundary ((fun y ↦ p+s • y) ⁻¹' A) ↔
      p+s • x ∈ coverEssentialBoundary A := by
  have he (B : Set Cover) (hB : MeasurableSet B) (t : ℝ) :
      0 < volume.real (((fun y ↦ p+s • y) ⁻¹' B) ∩ Metric.ball x t) ↔
        0 < volume.real (B ∩ Metric.ball (p+s • x) (s*t)) := by
    rw [volume_real_affine_preimage_ball_center hB p x hs t]
    exact mul_pos_iff_of_pos_left (by positivity)
  constructor
  · intro hx t ht
    have hh := hx (t/s) (div_pos ht hs)
    have h₁ := (he A hA (t/s)).mp hh.1
    have h₂ := (he Aᶜ hA.compl (t/s)).mp hh.2
    have hst : s*(t/s)=t := by field_simp
    simpa only [hst] using (And.intro h₁ h₂)
  · intro hx t ht
    have hh := hx (s*t) (mul_pos hs ht)
    exact ⟨(he A hA t).mpr hh.1,(he Aᶜ hA.compl t).mpr hh.2⟩

def CoverC1BoundaryAt (A : Set Cover) (p : Cover) : Prop :=
  ∃ (n b : Cover) (s : ℝ) (G : Plane → ℝ), ‖n‖ = 1 ∧ 0 < s ∧
    ‖b‖ ≤ 1/(544*4096) ∧ LipschitzWith (1/4) G ∧
    ContDiffOn ℝ 1 G (Metric.ball (0 : Plane) (1/(544*2048))) ∧
    (∀ y ∈ Metric.closedBall (0 : Plane) (1/(544*2048)),
      p+s • (b+normalGraph n G y) ∈ coverEssentialBoundary A) ∧
    (∀ x ∈ Metric.ball (0 : Cover) (1/(544*8192)),
      p+s • x ∈ coverEssentialBoundary A ↔ normalGraph n G (normalPlaneCoordinates n (x-b))=x-b)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_primary_offvertex_fixed_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {σ : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ t : ℝ, 0 < t → 0 < volume.real (A ∩ Metric.ball p t) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p t)) :
    ∃ (n : Cover) (s e C K ρ : ℝ), ‖n‖ = 1 ∧ 0 < s ∧ s ≤ 1 ∧
      0 < e ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ C*e ≤ 1/2 ∧
      ∀ᶠ i in atTop,
        ActualBoundaryGraph E (cubeCenter+r i • p) n (r i*s) ∧
        BoundaryNormalChart E (cubeCenter+r i • p) n ((r i*s)/272) e C K ρ := by
  classical
  obtain ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,hpack⟩ :=
    actual_primary_fixed_scale_packets hV hE hmin hcenter hμ hH
  let e := min (δ/2) (1/(4*C))
  have he : 0 < e := by dsimp [e]; positivity
  have heδ : e ≤ δ := (min_le_left _ _).trans (by linarith)
  have hCe : C*e ≤ 1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (min_le_right (δ/2) (1/(4*C)))
    change e*(4*C) ≤ 1 at hh
    nlinarith
  let t : ℕ → ℝ := fun i ↦ ((i:ℝ)+1)⁻¹
  have ht : ∀ i, 0 < t i := by intro i; dsimp [t]; positivity
  have ht1 : ∀ i, t i ≤ 1 := by
    intro i
    dsimp [t]
    exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have htlim : Tendsto t atTop (𝓝 0) := by
    simpa only [t,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨B,φ,n,hB,hφ,hn,hBc,hhalf,_⟩ :=
    actual_secondary_halfspace hV hE hmin hμ hH r hr hrlim hA hconv hcone hstationary
      p hp hp0 hboundary t ht ht1 htlim
  obtain ⟨η,hη,hηpack⟩ := hpack n hn e he heδ
  have heq : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      B.indicator (fun _ ↦ (1:ℝ)) x=(coverHalfspace n).indicator (fun _ ↦ (1:ℝ)) x := by
    filter_upwards [hhalf] with x hx hxb
    change (if x ∈ B then (1:ℝ) else 0) = if x ∈ coverHalfspace n then 1 else 0
    rw [propext (hx hxb)]
  have hconvH := localL1_limit_congr_ae_ball heq hBc
  obtain ⟨i,hi⟩ := (hconvH.eventually (Iio_mem_nhds hη)).exists
  refine ⟨n,t (φ i),e,C,K,ρ,hn,ht _,ht1 _,he,hC,hK,hρ,hρs,hCe,?_⟩
  exact hηpack r hr hrlim A hA hconv p hp hboundary (t (φ i)) (ht _) (ht1 _) hi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_primary_offvertex_C1 {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {σ : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : p ∈ coverEssentialBoundary A) : CoverC1BoundaryAt A p := by
  obtain ⟨n,s,e,C,K,ρ,hn,hs,hs1,he,hC,hK,hρ,hρs,hCe,hpack⟩ :=
    actual_primary_offvertex_fixed_graphs hV hE hmin hcenter hμ hH r hr hrlim hA hconv
      hcone hstationary p hp hp0 hboundary
  let B : Set Cover := (fun x ↦ p+s • x) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hsub : Metric.closedBall p (s*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
    have hh := norm_add_le (x-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 2)
  have hconvB := localL1_affine_tendsto
    (fun i ↦ measurable_blowupCharacteristic hE cubeCenter (r i))
    (fun i ↦ blowupCharacteristic_bound E cubeCenter (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv p hs hsub
  simp only [blowupCharacteristic_affine] at hconvB
  have heq (x : Cover) : A.indicator (fun _ ↦ (1:ℝ)) (p+s • x)=B.indicator (fun _ ↦ (1:ℝ)) x := rfl
  simp only [heq] at hconvB
  obtain ⟨k,hk⟩ := eventually_atTop.mp hpack
  let c : ℕ → Cover := fun i ↦ cubeCenter+r (i+k) • p
  let q : ℕ → ℝ := fun i ↦ r (i+k)*s
  have hshift : Tendsto (fun i : ℕ ↦ i+k) atTop atTop := tendsto_add_atTop_nat k
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,Function.comp_apply,zero_mul] using (hrlim.comp hshift).mul_const s
  have hc : ∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16 := by
    filter_upwards [(hrlim.comp hshift).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/16))] with i hi
    change r (i+k) < 1/16 at hi
    simp only [c,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    nlinarith [hr (i+k)]
  obtain ⟨b,G,N,hb,hG,hGc,hNc,hNu,hGder,hpoints,hcovers⟩ :=
    actual_strong_limit_C1_graph hV hE hmin c q (fun i ↦ mul_pos (hr _) hs) hqlim hc hB
      (hconvB.comp hshift) hn hρ hCe (fun i ↦ hk (i+k) (by omega))
  refine ⟨n,b,s,G,hn,hs,hb,hG,hGc,?_,?_⟩
  · intro y hy
    exact (coverEssentialBoundary_affine hA p _ hs).mp (hpoints y hy)
  · intro x hx
    rw [← coverEssentialBoundary_affine hA p x hs]
    exact hcovers x hx

end CubicTorus
end
end
end

end OAI
