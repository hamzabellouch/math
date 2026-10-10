import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVStationaryDensity

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma euclideanNormalMeasure_ball (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r ρ R : ℝ} (hr : 0 < r) (hρ : ρ ≤ R) :
    (euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = r⁻¹^2*euclideanBallMass μ c (r*ρ) := by
  have hm : MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} :=
    Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have he : euclideanNormalMap c r ⁻¹' {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) ρ} ∩
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} =
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*ρ)} := by
    ext z
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,euclideanNormalMap_mem c hr ρ]
    exact ⟨And.left,fun hz ↦ ⟨hz,Metric.ball_subset_ball (mul_le_mul_of_nonneg_left hρ hr.le) hz⟩⟩
  unfold euclideanNormalMeasure
  rw [FiniteMeasure.toMeasure_smul]
  change ((_ : Measure BlowupNormalBundle) _).toReal = _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,FiniteMeasure.toMeasure_map,
    Measure.map_apply (continuous_euclideanNormalMap c r).measurable hm,
    FiniteMeasure.restrict_measure_eq,Measure.restrict_apply
      (hm.preimage (continuous_euclideanNormalMap c r).measurable),he]
  simp only [ENNReal.coe_toReal,Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma euclideanNormalMeasure_ball_tendsto {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ euclideanBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    Tendsto (fun i ↦ (euclideanNormalMeasure μ c (r i) R : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) ρ}) l (𝓝 (θ*ρ^2)) := by
  have ht : Tendsto (fun i ↦ r i*ρ) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hrlim.mul_const ρ,
      Eventually.of_forall fun i ↦ mul_pos (hr i) hρ⟩
  have hh := (hθ.comp ht).mul_const (ρ^2)
  convert hh using 1
  funext i
  rw [euclideanNormalMeasure_ball μ c (hr i) hρR]
  dsimp only [Function.comp_apply]
  field_simp [(hr i).ne',hρ.ne']

theorem euclidean_normal_limit_ball_mass {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {θ : ℝ}
    (hθ : Tendsto (fun t ↦ euclideanBallMass μ c t / t^2) (𝓝[>] 0) (𝓝 θ))
    {R : ℝ} {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ euclideanNormalMeasure μ c (r i) R) l (𝓝 ν))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2 := by
  apply le_antisymm
  · exact finiteMeasure_real_open_upper hν (Metric.isOpen_ball.preimage continuous_fst)
      (euclideanNormalMeasure_ball_tendsto c r hr hrlim hθ hρ hρR.le)
  · have hlow (s : ℝ) (hs : s ∈ Ioo 0 ρ) : θ*s^2 ≤
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} := by
      apply (finiteMeasure_real_closed_lower hν
        (Metric.isClosed_closedBall.preimage continuous_fst)
        (show {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) s} ⊆
          {z | z.1 ∈ Metric.closedBall (0 : Cover) s} from fun _ hz ↦ Metric.ball_subset_closedBall hz)
        (euclideanNormalMeasure_ball_tendsto c r hr hrlim hθ hs.1 (hs.2.trans hρR).le)).trans
      exact measureReal_mono (fun _ hz ↦ Metric.closedBall_subset_ball hs.2 hz)
    have hh : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[<] ρ) (𝓝 (θ*ρ^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hρ)] with s hs hs0
    exact hlow s ⟨hs0,hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem stationary_pair_secondary_cone {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0)) :
    ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ B ↔ x ∈ B) := by
  let R : ℝ := (1-‖p‖)/2
  have hR : 0 < R := by dsimp [R]; linarith
  have hc : Metric.closedBall p R ⊆ Metric.closedBall (0 : Cover) 1 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by dsimp [R] at hx'; linarith : ‖x‖ ≤ 1)
  obtain ⟨θ,hθ,hdensity⟩ := stationary_euclideanBallMass_density hstat p hR hc
  let K : ℝ := euclideanBallMass ν p R/R^2
  have hK : 0 ≤ K := div_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds (half_pos hR)))
  let q : ℕ → ℝ := fun i ↦ r (i+k)
  have hq (i) : 0 < q i := hr _
  have hqb (i) : q i*2 ≤ R := by have hh := hk (i+k) (by omega); dsimp [q]; linarith
  have hmass (i) : euclideanBallMass ν p (q i*2) ≤ (K*4)*(q i)^2 := by
    have hh := stationary_euclideanBallMass_upper hstat p hR hc
      (mul_pos (hq i) (by norm_num : (0 : ℝ) < 2)) (hqb i)
    convert hh using 1
    ring
  obtain ⟨σ,_,hsup,hcl⟩ := euclideanNormalMeasure_cluster p q hq (by positivity : 0 ≤ K*4) hmass
  obtain ⟨U,hU,hσ⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hqlim : Tendsto q (U : Filter ℕ) (𝓝 0) :=
    (hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hconv' : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (q i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        (U : Filter ℕ) (𝓝 0) := (hconv.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hm (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
      (σ : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) b} = θ*b^2 :=
    euclidean_normal_limit_ball_mass p q hq hqlim hdensity hσ hb (by linarith)
  have hσstat (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    stationary_euclidean_normal_limit hstat p hp q hq hqlim (by norm_num : (1 : ℝ) < 2) hσ hF hs
  have hσflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :=
    euclidean_normal_limit_flux hA hB hflux p hp q hq hqlim (by norm_num : (1 : ℝ) < 2) hσ hconv' hF hs
  have hrad := stationary_quadraticMass_radial_tangent hθ hm hσstat
  intro t ht
  exact radial_flux_cone_ae hB (fun ψ hψ hs ↦ limit_set_radial_flux hσflux hrad hψ hs) ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_smul {n : Cover} (hn : ‖n‖ = 1)
    (c : ℝ) (z : ℝ × Plane) :
    normalColumnChart 0 n (c • z) = c • normalColumnChart 0 n z := by
  rw [normalColumnChart_apply 0 hn,normalColumnChart_apply 0 hn]
  simp only [zero_add,Prod.smul_fst,Prod.smul_snd,smul_add,smul_smul]
  rw [show normalPlaneEmbedding n (c • z.2) = c • normalPlaneEmbedding n z.2 from
    (normalPlaneLinearIsometry n).map_smul c z.2]
  rfl

theorem conical_product_planar_cone {B : Set Cover} {C : Set Plane}
    {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ B ↔ x ∈ B))
    {t : ℝ} (ht : 1 ≤ t) :
    ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have htle : t⁻¹ ≤ 1 := (inv_le_one₀ ht0).mpr ht
  have hqm : Measure.QuasiMeasurePreserving (fun z : ℝ × Plane ↦ t⁻¹ • z) volume volume := by
    convert QuasiMeasurePreserving.prodMap
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero ht0.ne'))
        (Measure.quasiMeasurePreserving_smul (volume : Measure Plane) (inv_ne_zero ht0.ne')) using 1
    rfl
  have hscale := hqm.ae hprod
  have hconechart := (normalColumnChart_measurePreserving 0 n).quasiMeasurePreserving.ae (hcone t ht)
  have hh : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (t⁻¹ • z.2 ∈ C ↔ z.2 ∈ C) := by
    filter_upwards [hprod,hscale,hconechart] with z hz hzs hc hzt hzy
    have hnorm : ‖t⁻¹ • z.2‖ < 1/16 := by
      rw [norm_smul,Real.norm_of_nonneg htinv]
      exact (mul_le_of_le_one_left (norm_nonneg _) htle).trans_lt hzy
    have habs : |t⁻¹ * z.1| < 1/16 := by
      rw [abs_mul,abs_of_nonneg htinv]
      exact (mul_le_of_le_one_left (abs_nonneg _) htle).trans_lt hzt
    have hb : normalColumnChart 0 n z ∈ Metric.ball (0 : Cover) 1 := by
      rw [Metric.mem_ball,dist_zero_right,normalColumnChart_apply 0 hn,zero_add]
      have hh := norm_add_le (normalPlaneEmbedding n z.2) (z.1 • n)
      rw [normalPlaneEmbedding_norm,norm_smul,Real.norm_eq_abs,hn,mul_one] at hh
      linarith
    have he := hzs habs hnorm
    rw [normalColumnChart_smul hn] at he
    exact he.symm.trans ((hc hb).trans (hz hzt hzy))
  have hsplit := Measure.ae_ae_of_ae_prod hh
  have hpos : (volume : Measure ℝ) (Ioo (-(1/16 : ℝ)) (1/16)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hsplit)
  filter_upwards [hs] with y hy hyb
  exact hy (abs_lt.mpr hsI) (by simpa only [Metric.mem_ball,dist_zero_right] using hyb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma triangular_mul_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ ↦ (z.1,z.1*z.2)) volume volume := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ (z.1,z.1*z.2)) :=
    measurable_fst.prodMk (measurable_fst.mul measurable_snd)
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun S hS hS0 ↦ ?_)⟩
  rw [Measure.map_apply hm hS,Measure.volume_eq_prod,
    Measure.prod_apply (hm hS)]
  have hnull : ∀ᵐ x : ℝ ∂volume, (volume : Measure ℝ) (Prod.mk x ⁻¹' S) = 0 := by
    apply (lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)).mp
    simpa only [← Measure.prod_apply hS,← Measure.volume_eq_prod] using hS0
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  change (∫⁻ x : ℝ, (volume : Measure ℝ) ((fun y : ℝ ↦ (x,x*y)) ⁻¹' S)) = 0
  rw [lintegral_congr_ae (show (fun x : ℝ ↦ (volume : Measure ℝ)
      ((fun y : ℝ ↦ (x,x*y)) ⁻¹' S)) =ᵐ[volume] 0 from ?_)]
  · simp
  filter_upwards [hnull,hn] with x hx hx0
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hx0
  exact hq.preimage_null hx

def planarWedgeChart (z : ℝ × ℝ) : Plane :=
  planeProductCoordinates.symm (z.1,z.1*z.2)

lemma planarWedgeChart_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving planarWedgeChart volume volume :=
  (planeProductCoordinates_measurePreserving.symm
    planeProductCoordinates.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.comp
      triangular_mul_quasiMeasurePreserving

lemma planarWedgeChart_smul (s t c : ℝ) :
    c • planarWedgeChart (s,t) = planarWedgeChart (c*s,t) := by
  rw [planarWedgeChart,← planeProductCoordinates.symm.map_smul]
  congr 1
  ext <;> simp [mul_assoc]

lemma planar_cone_all_positive_scales {C : Set Plane}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {c : ℝ} (hc0 : 0 < c) :
    ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) →
      c • y ∈ Metric.ball (0 : Plane) (1/16) → (c • y ∈ C ↔ y ∈ C) := by
  rcases le_total c 1 with hle|hge
  · have h := hc c⁻¹ ((one_le_inv₀ hc0).mpr hle)
    simp only [inv_inv] at h
    exact h.mono (fun y hy hyb _ ↦ hy hyb)
  · have h := (Measure.quasiMeasurePreserving_smul (volume : Measure Plane) hc0.ne').ae
      (hc c hge)
    filter_upwards [h] with y hy _ hcy
    simpa only [inv_smul_smul₀ hc0.ne'] using (hy hcy).symm

theorem planar_cone_slope_section {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hchart : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo (-1 : ℝ) 1,
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16)) :
    ∃ D : Set ℝ, MeasurableSet D ∧ ∀ᵐ z : ℝ × ℝ ∂volume,
      z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D) := by
  have hwm : Measurable planarWedgeChart := planarWedgeChart_quasiMeasurePreserving.measurable
  have hm : MeasurableSet {z : Plane × ℝ | 0 < z.2 →
      z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      z.2 • z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      (z.2 • z.1 ∈ C ↔ z.1 ∈ C)} :=
    (measurableSet_lt measurable_const measurable_snd).imp
      ((Metric.isOpen_ball.measurableSet.preimage measurable_fst).imp
        ((Metric.isOpen_ball.measurableSet.preimage (measurable_snd.smul measurable_fst)).imp
          ((hC.preimage (measurable_snd.smul measurable_fst)).iff
            (hC.preimage measurable_fst))))
  have hx : ∀ᵐ y : Plane ∂volume, ∀ᵐ c : ℝ ∂volume,
      0 < c → y ∈ Metric.ball (0 : Plane) (1/16) →
      c • y ∈ Metric.ball (0 : Plane) (1/16) → (c • y ∈ C ↔ y ∈ C) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply ae_of_all
    intro c
    by_cases hc0 : 0 < c
    · exact (planar_cone_all_positive_scales hc hc0).mono (fun _ h _ ↦ h)
    · exact ae_of_all _ (fun _ h ↦ (hc0 h).elim)
  have hsplit := Measure.ae_ae_of_ae_prod (planarWedgeChart_quasiMeasurePreserving.ae hx)
  have hrel : ∀ᵐ s : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ∀ᵐ r : ℝ ∂volume,
      s ∈ Ioo a b → r ∈ Ioo a b → t ∈ Ioo (-1 : ℝ) 1 →
      (planarWedgeChart (r,t) ∈ C ↔ planarWedgeChart (s,t) ∈ C) := by
    filter_upwards [hsplit] with s hs
    filter_upwards [hs] with t ht
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
        (inv_ne_zero hs0.ne')
      filter_upwards [hq.ae ht] with r hr _ hrI htI
      simp only [smul_eq_mul] at hr
      have hcp : 0 < s⁻¹*r := mul_pos (inv_pos.mpr hs0) (ha.trans hrI.1)
      have he : (s⁻¹*r) • planarWedgeChart (s,t) = planarWedgeChart (r,t) := by
        rw [planarWedgeChart_smul]
        congr 1
        field_simp
      have hh := hr hcp (hchart s hsI t htI)
      rw [he] at hh
      exact hh (hchart r hrI t htI)
    · exact ae_of_all _ (fun _ hs' ↦ (hsI hs').elim)
  have hpos : (volume : Measure ℝ) (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hrel)
  let D : Set ℝ := {t | planarWedgeChart (s,t) ∈ C}
  have hD : MeasurableSet D := hC.preimage (hwm.comp (measurable_const.prodMk measurable_id))
  refine ⟨D,hD,?_⟩
  have hm' : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Ioo a b → z.1 ∈ Ioo (-1 : ℝ) 1 →
      (planarWedgeChart (z.2,z.1) ∈ C ↔ z.1 ∈ D)} :=
    (measurableSet_Ioo.preimage measurable_snd).imp
      ((measurableSet_Ioo.preimage measurable_fst).imp
        ((hC.preimage (hwm.comp measurable_swap)).iff (hD.preimage measurable_fst)))
  apply (Measure.ae_prod_iff_ae_ae (hm'.preimage measurable_swap)).mpr
  apply (Measure.ae_ae_comm hm').mp
  filter_upwards [hs] with t ht
  filter_upwards [ht] with r hr hrI htI
  exact hr hsI hrI htI

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def slopeScalarTest (χ ψ : ℝ → ℝ) (x : Plane) : ℝ :=
  χ (planeProductCoordinates x).1 *
    ψ ((planeProductCoordinates x).2 / (planeProductCoordinates x).1)

def slopeVerticalVector : Plane := planeProductCoordinates.symm (0,1)

lemma slopeScalarTest_contDiff {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) : ContDiff ℝ (⊤ : ℕ∞) (slopeScalarTest χ ψ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hP : ContDiff ℝ (⊤ : ℕ∞) planeProductCoordinates :=
    planeProductCoordinates.contDiff
  by_cases hx : (planeProductCoordinates x).1 = 0
  · have heχ : χ =ᶠ[𝓝 ((planeProductCoordinates x).1)] 0 := by
      rw [hx]
      exact notMem_tsupport_iff_eventuallyEq.mp hχ0
    have he : slopeScalarTest χ ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(hP.continuous.fst.tendsto x).eventually heχ] with y hy
      simp only [slopeScalarTest,hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (hχ.contDiffAt.comp x hP.fst.contDiffAt).mul
      (hψ.contDiffAt.comp x (hP.snd.contDiffAt.div hP.fst.contDiffAt hx))

lemma slopeScalarTest_vertical_derivative {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hχ0 : 0 ∉ tsupport χ) (x : Plane) :
    fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector =
      χ (planeProductCoordinates x).1 / (planeProductCoordinates x).1 *
        deriv ψ ((planeProductCoordinates x).2 / (planeProductCoordinates x).1) := by
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • slopeVerticalVector) slopeVerticalVector 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const slopeVerticalVector).const_add x
  have hd := ((hf.differentiable (by simp)) (x+(0 : ℝ) • slopeVerticalVector)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he (t : ℝ) : slopeScalarTest χ ψ (x+t • slopeVerticalVector) =
      χ (planeProductCoordinates x).1 *
        ψ (((planeProductCoordinates x).2+t)/(planeProductCoordinates x).1) := by
    simp [slopeScalarTest,slopeVerticalVector]
  have hline : HasDerivAt (fun t : ℝ ↦ ((planeProductCoordinates x).2+t) /
      (planeProductCoordinates x).1) ((planeProductCoordinates x).1)⁻¹ 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_add ((planeProductCoordinates x).2)).div_const
      ((planeProductCoordinates x).1) using 1 <;> first | rfl | simp only [one_div]
  have hψd := (((hψ.differentiable (by simp)) _).hasDerivAt.comp 0 hline).const_mul
    (χ (planeProductCoordinates x).1)
  have hd0 : HasDerivAt (fun t : ℝ ↦ slopeScalarTest χ ψ (x+t • slopeVerticalVector))
      (fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero] using hd
  simp_rw [he] at hd0
  have hh := hd0.unique hψd
  simpa only [zero_add,add_zero,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

lemma slopeScalarTest_tsupport_rectangle {χ ψ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-1 : ℝ) 1) :
    tsupport (slopeScalarTest χ ψ) ⊆
      planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-b) b) := by
  apply closure_minimal _ ((isClosed_Icc.prod isClosed_Icc).preimage
    planeProductCoordinates.continuous)
  intro x hx
  have hn : χ (planeProductCoordinates x).1 ≠ 0 ∧
      ψ ((planeProductCoordinates x).2/(planeProductCoordinates x).1) ≠ 0 :=
    mul_ne_zero_iff.mp hx
  have hs := hχ (subset_tsupport _ hn.1)
  have ht := hψ (subset_tsupport _ hn.2)
  have hs0 : 0 < (planeProductCoordinates x).1 := ha.trans_le hs.1
  have ht' : |(planeProductCoordinates x).2/(planeProductCoordinates x).1| ≤ 1 := abs_le.mpr ht
  rw [abs_div,abs_of_pos hs0,div_le_iff₀ hs0,one_mul] at ht'
  exact ⟨hs,abs_le.mp (ht'.trans hs.2)⟩

lemma slopeScalarTest_hasCompactSupport {χ ψ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-1 : ℝ) 1) : HasCompactSupport (slopeScalarTest χ ψ) :=
  (planeProductCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset isClosed_closure
      (slopeScalarTest_tsupport_rectangle ha hχ hψ)

theorem planar_slope_flux {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b : ℝ} (ha : 0 < a)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hsψ : tsupport ψ ⊆ Ioo (-1 : ℝ) 1) :
    (∫ x in C, fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector) =
      (∫ s : ℝ, χ s)*(∫ t in D, deriv ψ t) := by
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hfs := slopeScalarTest_hasCompactSupport ha
    (hsχ.trans Ioo_subset_Icc_self) (hsψ.trans Ioo_subset_Icc_self)
  let G : Plane → ℝ := C.indicator
    (fun x ↦ fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector)
  have hi : Integrable G volume :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfs.fderiv_apply ℝ slopeVerticalVector)).indicator hC
  have hL : MeasurePreserving planeProductCoordinates.symm :=
    planeProductCoordinates_measurePreserving.symm
      planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLi := (hL.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hsplit := Measure.ae_ae_of_ae_prod hprod
  have he : (fun s : ℝ ↦ ∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =ᵐ[volume]
      (fun s : ℝ ↦ χ s*(∫ t in D, deriv ψ t)) := by
    filter_upwards [hsplit] with s hs
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hscale : (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planarWedgeChart (s,t))) := by
        change (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planeProductCoordinates.symm (s,s*t)))
        rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ G (planeProductCoordinates.symm (s,y))) s,
          abs_of_pos (inv_pos.mpr hs0),smul_eq_mul]
        rw [mul_inv_cancel_left₀ hs0.ne']
      rw [hscale]
      have hinner : (fun t : ℝ ↦ G (planarWedgeChart (s,t))) =ᵐ[volume]
          (fun t : ℝ ↦ (χ s/s)*D.indicator (deriv ψ) t) := by
        filter_upwards [hs] with t ht
        have hd : fderiv ℝ (slopeScalarTest χ ψ) (planarWedgeChart (s,t))
            slopeVerticalVector = (χ s/s)*deriv ψ t := by
          rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
          simp [planarWedgeChart,mul_div_cancel_left₀ _ hs0.ne']
        by_cases htI : t ∈ Ioo (-1 : ℝ) 1
        · by_cases htD : t ∈ D
          · simp only [G,indicator_of_mem ((ht hsI htI).mpr htD),indicator_of_mem htD,hd]
          · simp only [G,indicator_of_notMem htD,mul_zero,
              indicator_of_notMem (mt (ht hsI htI).mp htD)]
        · have hz : deriv ψ t = 0 := deriv_of_notMem_tsupport (fun hh ↦ htI (hsψ hh))
          simp only [hz,mul_zero] at hd
          by_cases htD : t ∈ D <;> by_cases htC : planarWedgeChart (s,t) ∈ C <;>
            simp [G,htD,htC,hd,hz]
      rw [integral_congr_ae hinner,integral_const_mul,integral_indicator hD]
      field_simp
    · have hz : χ s = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hsI (hsχ hh))
      rw [hz,zero_mul]
      apply integral_eq_zero_of_ae
      apply ae_of_all
      intro y
      have hd : fderiv ℝ (slopeScalarTest χ ψ) (planeProductCoordinates.symm (s,y))
          slopeVerticalVector = 0 := by
        rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
        simp [hz]
      by_cases hy : planeProductCoordinates.symm (s,y) ∈ C <;> simp [G,hy,hd]
  rw [← integral_indicator hC]
  change (∫ x : Plane, G x) = _
  rw [← hL.integral_comp planeProductCoordinates.symm.toHomeomorph.measurableEmbedding G]
  rw [Measure.volume_eq_prod] at hLi ⊢
  change Integrable (fun z : ℝ × ℝ ↦ G (planeProductCoordinates.symm z)) (volume.prod volume) at hLi
  rw [integral_prod _ hLi,integral_congr_ae he,integral_mul_const]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planarAxialBump : ContDiffBump (0 : ℝ) where
  rIn := 1/64
  rOut := 1/32
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma planarAxialBump_support : tsupport (planarAxialBump : ℝ → ℝ) ⊆
    Icc (-(1/32 : ℝ)) (1/32) := by
  rw [planarAxialBump.tsupport_eq,Real.closedBall_eq_Icc]
  simp [planarAxialBump]

theorem planar_product_directional_bound {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {L : ℝ} (hL : 0 ≤ L)
    (hper : coverLocalPerimeter B (Metric.ball (0 : Cover) (1/8)) ≤ ENNReal.ofReal L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K := by
  let J : ℝ := ∫ t : ℝ, planarAxialBump t
  have hJ : 0 < J := planarAxialBump.integral_pos
  refine ⟨L/J,div_nonneg hL hJ.le,?_⟩
  have hbound (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hsφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32))
      (hbφ : ∀ y, |φ y| ≤ 1) (u : Plane) (hu : ‖u‖ = 1) :
      (∫ y in C, fderiv ℝ φ y u) ≤ L/J := by
    let F : Cover → Cover := fun z ↦ normalScalarTest 0 n planarAxialBump φ z • normalPlaneEmbedding n u
    have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
      (normalScalarTest_contDiff 0 n planarAxialBump.contDiff hφ).smul_const _
    have hFs : tsupport F ⊆ Metric.ball (0 : Cover) (1/8) := by
      have hh := normalScalarTest_tsupport_ball 0 hn (by norm_num : (0 : ℝ)<3/32)
        (χ := planarAxialBump) (φ := φ)
        (by convert planarAxialBump_support using 1; norm_num)
        (by convert hsφ using 1; norm_num)
      exact (tsupport_smul_subset_left (f := normalScalarTest 0 n planarAxialBump φ) (g := fun _ ↦ normalPlaneEmbedding n u)).trans (hh.trans (Metric.ball_subset_ball (by norm_num)))
    have hFb (x) : ‖F x‖ ≤ 1 := by
      rw [norm_smul, normalPlaneEmbedding_norm,hu,mul_one,Real.norm_eq_abs]
      change |planarAxialBump ⟪n,x-0⟫*φ (normalPlaneCoordinates n (x-0))| ≤ 1
      rw [abs_mul,abs_of_nonneg planarAxialBump.nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) planarAxialBump.le_one).trans (hbφ _)
    have hh := integral_divergence_le_coverLocalPerimeter hper hL hF
      ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure (hFs.trans Metric.ball_subset_closedBall)) hFs hFb
    rw [planar_product_flux hB hC hn hprod planarAxialBump.contDiff hφ
      planarAxialBump_support hsφ] at hh
    exact (le_div_iff₀ hJ).mpr (by simpa only [mul_comm,J] using hh)
  intro φ hφ hs hb u hu
  apply abs_le.mpr
  refine ⟨?_,hbound φ hφ hs hb u hu⟩
  have hh := hbound (-φ) hφ.neg (by simpa only [tsupport_neg] using hs)
    (by simpa only [Pi.neg_apply,abs_neg] using hb) u hu
  simpa only [fderiv_neg,Pi.neg_apply,neg_apply,integral_neg,neg_le] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slopeVerticalVector_norm : ‖slopeVerticalVector‖ = 1 := by
  simp [slopeVerticalVector,planeProductCoordinates]
  change ‖(Complex.I : ℂ)‖ = 1
  exact Complex.norm_I

lemma slopeScalarTest_bound {χ ψ : ℝ → ℝ}
    (hχ : ∀ t, |χ t| ≤ 1) (hψ : ∀ t, |ψ t| ≤ 1) (x : Plane) :
    |slopeScalarTest χ ψ x| ≤ 1 := by
  rw [slopeScalarTest,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hχ _)).trans (hψ _)

theorem planar_slope_directional_bound {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b : ℝ} (ha : 0 < a)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    (hrect : planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-b) b) ⊆
      Metric.closedBall (0 : Plane) (1/32))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hbχ : ∀ t, |χ t| ≤ 1)
    (hJ : 0 < ∫ t : ℝ, χ t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t in D, deriv ψ t| ≤ L := by
  refine ⟨K/(∫ t : ℝ, χ t),div_nonneg hK hJ.le,?_⟩
  intro ψ hψ hsψ hbψ
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hh := hbv (slopeScalarTest χ ψ) (slopeScalarTest_contDiff hχ hψ hχ0)
    ((slopeScalarTest_tsupport_rectangle ha (hsχ.trans Ioo_subset_Icc_self)
      (hsψ.trans Ioo_subset_Icc_self)).trans hrect)
    (slopeScalarTest_bound hbχ hbψ) slopeVerticalVector slopeVerticalVector_norm
  rw [planar_slope_flux hC hD ha hprod hχ hψ hsχ hsψ,abs_mul,abs_of_pos hJ] at hh
  exact (le_div_iff₀ hJ).mpr (by simpa only [mul_comm] using hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slope_rectangle_ball {a b : ℝ} (ha : 0 < a)
    (hb : ‖planeProductCoordinates.symm.toContinuousLinearMap‖*b ≤ (1/32 : ℝ)) :
    planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-b) b) ⊆
      Metric.closedBall (0 : Plane) (1/32) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  have hnorm : ‖planeProductCoordinates x‖ ≤ b := by
    rw [Prod.norm_def]
    exact max_le (Real.norm_eq_abs _ ▸ abs_le.mpr ⟨by linarith [hx.1.1,hx.1.2],hx.1.2⟩)
      (Real.norm_eq_abs _ ▸ abs_le.mpr hx.2)
  calc
    ‖x‖ = ‖planeProductCoordinates.symm (planeProductCoordinates x)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*‖planeProductCoordinates x‖ :=
      planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (planeProductCoordinates x)
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*b :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := hb

theorem planar_cone_angular_dual_bv {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K) :
    ∃ (a b L : ℝ) (D : Set ℝ), 0 < a ∧ a < b ∧ 0 ≤ L ∧ MeasurableSet D ∧
      (∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
        (planarWedgeChart z ∈ C ↔ z.2 ∈ D)) ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
        |∫ t in D, deriv ψ t| ≤ L := by
  let N : ℝ := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let b : ℝ := 1/(128*(N+1))
  have hN : 0 ≤ N := norm_nonneg _
  have hb : 0 < b := by dsimp [b]; positivity
  have hNb : N*b ≤ 1/32 := by
    dsimp [b]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have ha : 0 < b/4 := div_pos hb (by norm_num)
  have hab : b/4 < b := by linarith
  have hrect := slope_rectangle_ball ha hNb
  have hchart (s : ℝ) (hs : s ∈ Ioo (b/4) b) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16) := by
    apply (Metric.closedBall_subset_ball (by norm_num : (1/32 : ℝ)<1/16))
    apply hrect
    change (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).1 ∈ Icc (b/4) b ∧
      (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).2 ∈ Icc (-b) b
    rw [ContinuousLinearEquiv.apply_symm_apply]
    constructor
    · exact ⟨hs.1.le,hs.2.le⟩
    · have hs0 : 0 < s := ha.trans hs.1
      have hst : |s*t| ≤ b := by
        rw [abs_mul,abs_of_pos hs0]
        exact (mul_le_of_le_one_right hs0.le (abs_le.mpr ⟨ht.1.le,ht.2.le⟩)).trans hs.2.le
      exact abs_le.mp hst
  obtain ⟨D,hD,hprod⟩ := planar_cone_slope_section hC hc ha hab hchart
  let χ : ContDiffBump (b/2) := {
    rIn := b/16
    rOut := b/8
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsχ : tsupport (χ : ℝ → ℝ) ⊆ Ioo (b/4) b := by
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    change b/2-b/8 ≤ t ∧ t ≤ b/2+b/8 at ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨L,hL,hdual⟩ := planar_slope_directional_bound hC hD ha hprod hrect hK hbv
    χ.contDiff hsχ (fun t ↦ by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one) χ.integral_pos
  exact ⟨b/4,b,L,D,ha,hab,hL,hD,hprod,hdual⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def angularEssentialBoundary (D : Set ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → 0 < volume (D ∩ Metric.ball x δ) ∧
    0 < volume (Dᶜ ∩ Metric.ball x δ)}

lemma angular_essential_boundary_in_mixed_closure {D s : Set ℝ}
    (hfull : ∀ᵐ x : ℝ ∂volume, x ∈ Icc (-(1/2 : ℝ)) (1/2) → x ∈ s)
    {x : ℝ} (hx : x ∈ Icc (-(1/4 : ℝ)) (1/4)) (hb : x ∈ angularEssentialBoundary D) :
    x ∈ closure {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=0} ∩
      closure {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=1} := by
  have hphase (A : Set ℝ) (hA : ∀ δ : ℝ, 0 < δ → 0 < volume (A ∩ Metric.ball x δ)) :
      x ∈ closure (s ∩ A) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ : ℝ := min (ε/2) (1/4)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hsub (t : ℝ) (ht : t ∈ Metric.ball x δ) : t ∈ Icc (-(1/2 : ℝ)) (1/2) := by
      have hd : |t-x| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using ht
      have hbd : δ ≤ 1/4 := min_le_right _ _
      constructor <;> linarith [(abs_lt.mp hd).1,(abs_lt.mp hd).2,hx.1,hx.2]
    obtain ⟨t,ht,hst⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt (hA δ hδ))
      (ae_restrict_of_ae hfull)
    refine ⟨t,⟨hst (hsub t ht.2),ht.1⟩,?_⟩
    have hd : dist x t < δ := by simpa only [Metric.mem_ball,dist_comm] using ht.2
    exact hd.trans_le (le_trans (min_le_left _ _) (by linarith))
  constructor
  · have hh := hphase Dᶜ (fun δ hδ ↦ (hb δ hδ).2)
    apply closure_mono (show s ∩ Dᶜ ⊆ {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=0} from ?_) hh
    exact fun t ht ↦ ⟨ht.1,indicator_of_notMem ht.2 _⟩
  · have hh := hphase D (fun δ hδ ↦ (hb δ hδ).1)
    apply closure_mono (show s ∩ D ⊆ {t ∈ s | D.indicator (fun _ ↦ (1 : ℝ)) t=1} from ?_) hh
    exact fun t ht ↦ ⟨ht.1,indicator_of_mem ht.2 _⟩

theorem angular_dual_bv_finite_transitions {D : Set ℝ} (hD : MeasurableSet D) {L : ℝ}
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t in D, deriv ψ t| ≤ L) :
    (Icc (-(1/4 : ℝ)) (1/4) ∩ angularEssentialBoundary D).Finite := by
  let f : ℝ → ℝ := D.indicator (fun _ ↦ (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hD
  have hfb (t : ℝ) : f t=0 ∨ f t=1 := by
    by_cases ht : t ∈ D <;> simp [f,ht]
  have hf1 (t : ℝ) : |f t| ≤ 1 := by rcases hfb t with h|h <;> rw [h] <;> norm_num
  have hfdual (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hsψ : tsupport ψ ⊆ Ioo (-1 : ℝ) 1) (hbψ : ∀ t, |ψ t| ≤ 1) :
      |∫ t : ℝ, f t*deriv ψ t| ≤ L := by
    have he (t : ℝ) : f t*deriv ψ t = D.indicator (deriv ψ) t := by
      by_cases ht : t ∈ D <;> simp [f,ht]
    simp_rw [he]
    rw [integral_indicator hD]
    exact hdual ψ hψ hsψ hbψ
  obtain ⟨s,_,hfull,hbv⟩ := boundedVariationOn_good_set_of_dual_bound hf hf1 hfdual
  have hfin := binary_bv_finite_mixed_boundary hbv (fun t _ ↦ hfb t)
    (isCompact_Icc : IsCompact (Icc (-(1/4 : ℝ)) (1/4)))
  apply hfin.subset
  intro x hx
  exact ⟨hx.1,angular_essential_boundary_in_mixed_closure hfull hx.1 hx.2⟩

theorem planar_cone_finite_angular_transitions {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K) :
    ∃ (a b : ℝ) (D : Set ℝ), 0 < a ∧ a < b ∧ MeasurableSet D ∧
      (∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-1 : ℝ) 1 →
        (planarWedgeChart z ∈ C ↔ z.2 ∈ D)) ∧
      (Icc (-(1/4 : ℝ)) (1/4) ∩ angularEssentialBoundary D).Finite := by
  obtain ⟨a,b,L,D,ha,hab,_,hD,hprod,hdual⟩ := planar_cone_angular_dual_bv hC hc hK hbv
  exact ⟨a,b,D,ha,hab,hD,hprod,angular_dual_bv_finite_transitions hD hdual⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma angularEssentialBoundary_eq_support (D : Set ℝ) :
    angularEssentialBoundary D = (volume.restrict D).support ∩ (volume.restrict Dᶜ).support := by
  ext x
  rw [Set.mem_inter_iff,Metric.nhds_basis_ball.mem_measureSupport,
    Metric.nhds_basis_ball.mem_measureSupport]
  simp only [angularEssentialBoundary,Set.mem_ofPred_eq,Measure.restrict_apply Metric.isOpen_ball.measurableSet,
    inter_comm]
  simp only [forall_and]

theorem connected_angular_phase {D s : Set ℝ} (hD : MeasurableSet D)
    (hs : MeasurableSet s) (hc : IsPreconnected s)
    (hd : Disjoint s (angularEssentialBoundary D)) :
    volume (s ∩ D) = 0 ∨ volume (s ∩ Dᶜ) = 0 := by
  let U := (volume.restrict D).supportᶜ
  let W := (volume.restrict Dᶜ).supportᶜ
  have hUW : Disjoint U W := by
    have hsum : (volume.restrict D).support ∪ (volume.restrict Dᶜ).support = univ := by
      rw [← Measure.support_add,Measure.restrict_add_restrict_compl hD,Measure.support_eq_univ]
    rw [Set.disjoint_iff_inter_eq_empty]
    change (volume.restrict D).supportᶜ ∩ (volume.restrict Dᶜ).supportᶜ = ∅
    rw [← compl_union,hsum,compl_univ]
  have hsub : s ⊆ U ∪ W := by
    intro x hx
    have hx' : x ∉ angularEssentialBoundary D := fun hb ↦ Set.disjoint_left.mp hd hx hb
    rw [angularEssentialBoundary_eq_support] at hx'
    exact not_and_or.mp hx'
  have hnullD (h : s ⊆ U) : volume (s ∩ D) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  have hnullC (h : s ⊆ W) : volume (s ∩ Dᶜ) = 0 := by
    rw [← Measure.restrict_apply hs]
    exact measure_mono_null h Measure.measure_compl_support
  by_cases hU : (s ∩ U).Nonempty
  · exact Or.inl (hnullD (hc.subset_left_of_subset_union Measure.isOpen_compl_support
      Measure.isOpen_compl_support hUW hsub hU))
  · apply Or.inr
    apply hnullC
    intro x hx
    rcases hsub hx with hu|hw
    · exact (hU ⟨x,hx,hu⟩).elim
    · exact hw

lemma measure_inter_ball_zero_of_sides (A : Set ℝ) (x δ : ℝ)
    (hl : volume (Ioo (x-δ) x ∩ A) = 0) (hr : volume (Ioo x (x+δ) ∩ A) = 0) :
    volume (A ∩ Metric.ball x δ) = 0 := by
  have hp : volume ({x} ∩ A) = 0 := measure_mono_null inter_subset_left (measure_singleton x)
  apply measure_mono_null (t := (Ioo (x-δ) x ∩ A) ∪ ({x} ∩ A) ∪ (Ioo x (x+δ) ∩ A)) ?_
    (measure_union_null (measure_union_null hl hp) hr)
  intro y hy
  have hyb : |y-x| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using hy.2
  rcases lt_trichotomy y x with hh|hh|hh
  · exact Or.inl (Or.inl ⟨⟨by linarith [(abs_lt.mp hyb).1],hh⟩,hy.1⟩)
  · exact Or.inl (Or.inr ⟨hh,hy.1⟩)
  · exact Or.inr ⟨⟨hh,by linarith [(abs_lt.mp hyb).2]⟩,hy.1⟩

theorem finite_angular_transition_is_jump {D : Set ℝ} (hD : MeasurableSet D)
    {a b x : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hx : x ∈ Ioo a b) (hxb : x ∈ angularEssentialBoundary D) :
    ∃ δ : ℝ, 0 < δ ∧
      ((volume (Ioo (x-δ) x ∩ D) = 0 ∧ volume (Ioo x (x+δ) ∩ Dᶜ) = 0) ∨
       (volume (Ioo (x-δ) x ∩ Dᶜ) = 0 ∧ volume (Ioo x (x+δ) ∩ D) = 0)) := by
  let S := Icc a b ∩ angularEssentialBoundary D
  have hcl : IsClosed (S \ {x}) := (hfin.sdiff (t := {x})).isClosed
  have hop : IsOpen (Ioo a b \ (S \ {x})) := isOpen_Ioo.sdiff hcl
  have hxin : x ∈ Ioo a b \ (S \ {x}) := ⟨hx,by simp⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.isOpen_iff.mp hop x hxin
  have hiso (y : ℝ) (hy : y ∈ Metric.ball x δ) (he : y ∈ angularEssentialBoundary D) : y=x := by
    have hh := hd hy
    by_contra hne
    exact hh.2 ⟨⟨⟨hh.1.1.le,hh.1.2.le⟩,he⟩,hne⟩
  have hleft : Disjoint (Ioo (x-δ) x) (angularEssentialBoundary D) := by
    rw [Set.disjoint_left]
    intro y hy he
    have hyb : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hy.1,hy.2]
    exact (ne_of_lt hy.2) (hiso y hyb he)
  have hright : Disjoint (Ioo x (x+δ)) (angularEssentialBoundary D) := by
    rw [Set.disjoint_left]
    intro y hy he
    have hyb : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hy.1,hy.2]
    exact (ne_of_gt hy.1) (hiso y hyb he)
  have hl := connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hleft
  have hr := connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hright
  refine ⟨δ,hδ,?_⟩
  rcases hl with hl|hl <;> rcases hr with hr|hr
  · exact ((ne_of_gt (hxb δ hδ).1) (measure_inter_ball_zero_of_sides D x δ hl hr)).elim
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact ((ne_of_gt (hxb δ hδ).2) (measure_inter_ball_zero_of_sides Dᶜ x δ hl hr)).elim

end CubicTorus

end
end

end

end OAI
