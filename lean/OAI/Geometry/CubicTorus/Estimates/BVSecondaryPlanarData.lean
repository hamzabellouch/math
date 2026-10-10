import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVPlanarEssentialBoundary

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_secondary_planar_cone_data {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p δ))
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ (B : Set Cover) (C : Set Plane) (φ : ℕ → ℕ),
      MeasurableSet B ∧ MeasurableSet C ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∃ b : ℝ, 0 < b ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
        b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤ ENNReal.ofReal (M*b^2)) ∧
      (∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        B ∆ D ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
          coverLocalPerimeter D (Metric.closedBall (0 : Cover) b)) ∧
      (∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
        (normalColumnChart 0 (‖p‖⁻¹ • p) z ∈ B ↔ z.2 ∈ C)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) (1/16) →
        (t⁻¹ • y ∈ C ↔ y ∈ C)) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ (ψ : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        tsupport ψ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |ψ y| ≤ 1) →
        ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ ψ y u| ≤ K) := by
  obtain ⟨B,hB,φ,hφ,hBc,hper,hcomp,D,hD,hprod⟩ :=
    actual_cone_secondary_product_comparison hV hE hmin r hr hrlim hA hconv hcone
      p hp hp0 s hs hs1 hslim
  obtain ⟨C,hC,hprodC⟩ := line_product_euclidean hD hprod
  have hn : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]
  have hBc' := stationary_pair_secondary_cone hA hB
    (fun F hF hFs ↦ (hstationary F hF hFs).1)
    (fun F hF hFs ↦ (hstationary F hF hFs).2) p hp
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop)
    (by simpa only [add_comm] using hBc)
  obtain ⟨b,hb,hden⟩ := isMinimizerAt_secondary_two_sided_density hV hE hmin
  refine ⟨B,C,φ,hB,hC,hφ,hBc,⟨b,hb,?_⟩,hper,hcomp,hprodC,?_,?_⟩
  · exact hden r hr hrlim A hA hconv p hp hboundary
      (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop) B hB hBc
  · intro t ht
    exact conical_product_planar_cone hn hprodC hBc' ht
  · obtain ⟨M,hM,hMb⟩ := hper
    exact planar_product_directional_bound hB hC hn hprodC
      (mul_nonneg hM.le (sq_nonneg (1/8 : ℝ))) (hMb (1/8) (by norm_num) (by norm_num))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_product_ball_volume_le {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/16) :
    volume.real (B ∩ Metric.ball (0 : Cover) ρ) ≤
      (2*ρ)*volume.real (C ∩ Metric.ball (0 : Plane) ρ) := by
  have hm := (normalColumnChart_measurePreserving 0 n).measure_preimage
    (s := B ∩ Metric.ball (0 : Cover) ρ) (hB.inter measurableSet_ball).nullMeasurableSet
  have hsub : (normalColumnChart 0 n ⁻¹' (B ∩ Metric.ball (0 : Cover) ρ)) ≤ᵐ[volume]
      Ioo (-ρ) ρ ×ˢ (C ∩ Metric.ball (0 : Plane) ρ) := by
    filter_upwards [hprod] with z hz hzb
    have hnorm : ‖normalColumnChart 0 n z‖ < ρ := by
      simpa only [Metric.mem_ball,dist_zero_right] using hzb.2
    have hheight : |z.1| < ρ := by
      have hh := abs_real_inner_le_norm n (normalColumnChart 0 n z)
      rw [hn,one_mul] at hh
      have he := normalColumnChart_height 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    have hplane : ‖z.2‖ < ρ := by
      have hh := (normalPlaneCoordinates_lipschitz n).norm_sub_le (normalColumnChart 0 n z) 0
      simp only [map_zero,sub_zero,NNReal.coe_one,one_mul] at hh
      have he := normalColumnChart_projection 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    exact ⟨abs_lt.mp hheight,(hz (hheight.trans_le hρ1) (hplane.trans_le hρ1)).mp hzb.1,
      by simpa only [Metric.mem_ball,dist_zero_right] using hplane⟩
  have hle := measure_mono_ae hsub
  rw [hm,Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo] at hle
  have ht : volume (C ∩ Metric.ball (0 : Plane) ρ) ≠ ⊤ := by
    have hsplit := measure_inter_add_sdiff (μ := (volume : Measure Plane))
      (Metric.ball (0 : Plane) ρ) hC
    rw [inter_comm] at hsplit
    have hbound := (le_self_add : volume (C ∩ Metric.ball (0 : Plane) ρ) ≤
      volume (C ∩ Metric.ball (0 : Plane) ρ) + volume (Metric.ball (0 : Plane) ρ \ C))
    exact (hbound.trans_eq hsplit |>.trans_lt measure_ball_lt_top).ne
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht) hle
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith : 0 ≤ ρ + ρ),
    Measure.real_def,sub_neg_eq_add,two_mul] using hh

theorem planar_product_two_sided_density {B : Set Cover} {C : Set Plane}
    (hB : MeasurableSet B) (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {b : ℝ} (hb : 0 < b)
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/16) :
    (b/2)*ρ^2 ≤ volume.real (C ∩ Metric.ball (0 : Plane) ρ) ∧
    (b/2)*ρ^2 ≤ volume.real (Cᶜ ∩ Metric.ball (0 : Plane) ρ) := by
  have hpc : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ Bᶜ ↔ z.2 ∈ Cᶜ) := by
    filter_upwards [hprod] with z hz ht hy
    exact not_congr (hz ht hy)
  have hd := hden ρ hρ (by linarith)
  have h1 := hd.1.trans (planar_product_ball_volume_le hB hC hn hprod hρ hρ1)
  have h2 := hd.2.trans (planar_product_ball_volume_le hB.compl hC.compl hn hpc hρ hρ1)
  have hfactor : 0 < 2*ρ :=
    pos_of_mul_pos_left ((mul_pos hb (pow_pos hρ 3)).trans_le h1) measureReal_nonneg
  constructor
  · apply (mul_le_mul_iff_right₀ hfactor).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hfactor).mp
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem minimizing_planar_product_halfplane
    {B : Set Cover} {C : Set Plane} {n : Cover}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hn : ‖n‖ = 1)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x)
    {b : ℝ} (hb : 0 < b)
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)) :
    ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪m,y⟫) := by
  have hd := planar_product_two_sided_density hB hC hn hprod hb hden
    (by norm_num : (0 : ℝ) < 1/16) (le_refl (1/16 : ℝ))
  have hp : 0 < (b/2)*(1/16 : ℝ)^2 := by positivity
  apply planar_cone_halfplane_of_single_transition hC hc
  · intro R w hw
    exact minimizing_planar_chart_single_transition hB hC (by norm_num : (0 : ℝ)<1/16)
      hmin hprod hc hK hbv heq hflux R hw
  · have hh : 0 < (volume (C ∩ Metric.ball (0 : Plane) (1/16))).toReal := hp.trans_le hd.1
    exact inter_comm C _ ▸ ENNReal.toReal_pos_iff.mp hh |>.1
  · have hh : 0 < (volume (Cᶜ ∩ Metric.ball (0 : Plane) (1/16))).toReal := hp.trans_le hd.2
    exact inter_comm Cᶜ _ ▸ ENNReal.toReal_pos_iff.mp hh |>.1

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_transverse_inner {n : Cover} (hn : ‖n‖ = 1)
    (m : Plane) (z : ℝ × Plane) :
    ⟪normalPlaneEmbedding n m, normalColumnChart 0 n z⟫ = ⟪m,z.2⟫ := by
  rw [normalColumnChart_apply 0 hn,zero_add,inner_add_right,inner_smul_right,
    real_inner_comm n (normalPlaneEmbedding n m),normalPlaneEmbedding_inner hn,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map m z.2

theorem planar_halfspace_lift {B : Set Cover} {C : Set Plane} {n : Cover}
    (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {m : Plane} (hm : m ≠ 0)
    (hhalf : ∀ᵐ y : Plane ∂volume, y ∈ Metric.ball (0 : Plane) (1/16) →
      (y ∈ C ↔ 0 < ⟪m,y⟫)) :
    ∃ N : Cover, N ≠ 0 ∧ ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) (1/16) → (x ∈ B ↔ 0 < ⟪N,x⟫) := by
  have hm0 : normalPlaneEmbedding n m ≠ 0 := by
    intro hz
    have hh := normalPlaneEmbedding_norm n m
    rw [hz,norm_zero] at hh
    exact hm (norm_eq_zero.mp hh.symm)
  refine ⟨normalPlaneEmbedding n m,hm0,?_⟩
  have hy : ∀ᵐ z : ℝ × Plane ∂volume,
      z.2 ∈ Metric.ball (0 : Plane) (1/16) → (z.2 ∈ C ↔ 0 < ⟪m,z.2⟫) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))).ae hhalf
  have ha : ∀ᵐ z : ℝ × Plane ∂volume,
      normalColumnChart 0 n z ∈ Metric.ball (0 : Cover) (1/16) →
        (normalColumnChart 0 n z ∈ B ↔ 0 < ⟪normalPlaneEmbedding n m, normalColumnChart 0 n z⟫) := by
    filter_upwards [hprod,hy] with z hz hy hb
    have hnorm : ‖normalColumnChart 0 n z‖ < 1/16 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hb
    have ht : |z.1| < 1/16 := by
      have hh := abs_real_inner_le_norm n (normalColumnChart 0 n z)
      rw [hn,one_mul] at hh
      have he := normalColumnChart_height 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    have hp : ‖z.2‖ < 1/16 := by
      have hh := (normalPlaneCoordinates_lipschitz n).norm_sub_le (normalColumnChart 0 n z) 0
      simp only [map_zero,sub_zero,NNReal.coe_one,one_mul] at hh
      have he := normalColumnChart_projection 0 hn z.1 z.2
      simp only [sub_zero] at he
      rw [he] at hh
      exact hh.trans_lt hnorm
    rw [normalColumnChart_transverse_inner hn]
    exact (hz ht hp).trans (hy (by simpa only [Metric.mem_ball,dist_zero_right] using hp))
  simpa only [MeasurableEquiv.apply_symm_apply] using
    (normalColumnChart_measurePreserving 0 n).symm.quasiMeasurePreserving.ae ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma blowup_normal_closedBall_mass {ν : FiniteMeasure BlowupNormalBundle} {θ R : ℝ}
    (hm : ∀ s : ℝ, 0 < s → s < R →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) s} = θ*s^2)
    {b : ℝ} (hb : 0 < b) (hbR : b < R) :
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.closedBall (0 : Cover) b} = θ*b^2 := by
  apply le_antisymm
  · have ht : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[>] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbR)] with s hbs hsR
    rw [← hm s (hb.trans hbs) hsR]
    exact measureReal_mono (fun _ hz ↦ Metric.closedBall_subset_ball hbs hz)
  · rw [← hm b hb hbR]
    exact measureReal_mono (fun _ hz ↦ Metric.ball_subset_closedBall hz)

theorem isMinimizerAt_blowup_perimeter_eq {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hm : ∀ s : ℝ, 0 < s → s < 2 →
      (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) s} = θ*s^2)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2) := by
  have hb2 : b < 2 := by linarith
  have hp : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal (θ*b^2) := by
    have hh := coverLocalPerimeter_le_normal Metric.isClosed_closedBall.measurableSet
      (Metric.closedBall_subset_closedBall hb1) hflux
    have he := blowup_normal_closedBall_mass hm hb hb2
    rw [← he,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact hh
  have hfin : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp
  let L := (coverLocalPerimeter A (Metric.closedBall (0 : Cover) b)).toReal
  have hL : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hfin).ge
  have hlow : θ*b^2 ≤ L := by
    have ht : Tendsto (fun a : ℝ ↦ θ*a^2) (𝓝[<] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with a hab ha
    exact isMinimizerAt_blowup_competitor_bound hV hE hmin hμ hθ r hr hrlim hA hA hconv ha hab hb2.le
      ENNReal.toReal_nonneg hL (by simp)
  apply (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (mul_nonneg hθ0 (sq_nonneg b))]
  exact le_antisymm
    ((ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg hθ0 (sq_nonneg b))).mp hp) hlow

theorem isMinimizerAt_blowup_local_minimal {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {θ : ℝ} (hθ : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b ≤ R)
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2))
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) := by
  by_cases hfin : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) = ⊤
  · rw [hfin]
    exact le_top
  let L := (coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)).toReal
  have hL : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal hfin).ge
  have hlow : θ*b^2 ≤ L := by
    have ht : Tendsto (fun s : ℝ ↦ θ*s^2) (𝓝[<] b) (𝓝 (θ*b^2)) :=
      (continuous_const.mul (continuous_id.pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)] with s hsb has
    exact isMinimizerAt_blowup_competitor_bound hV hE hmin hμ hθ r hr hrlim hA hB hconv
      (ha.trans has) hsb hbR ENNReal.toReal_nonneg hL
      (hAB.trans (Metric.ball_subset_ball has.le))
  rw [heq]
  exact (ENNReal.ofReal_le_ofReal hlow).trans_eq (ENNReal.ofReal_toReal hfin)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowupNormal_inner_integrable (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) :
    Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) ν := by
  apply Integrable.of_bound (show AEStronglyMeasurable _ _ from
    (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable) 1
  exact ae_of_all _ fun z ↦ by
    simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n

lemma radial_normal_flux_tendsto (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ ↦ ∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫
      ∂(ν : Measure BlowupNormalBundle)) (𝓝[>] 0)
      (𝓝 (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
        ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : BlowupNormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall fun ε : ℝ ↦ (show Continuous (fun z : BlowupNormalBundle ↦
      radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫) from by
        exact ((radialDensityWeight_contDiff 0 b ε).continuous.comp continuous_fst).mul
          ((continuous_subtype_val.comp continuous_snd).inner continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun ε : ℝ ↦ ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦ by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
      exact (mul_le_mul (radialDensityWeight_le_one _ _ _ _)
        (show ‖⟪(z.2 : Cover),n⟫‖ ≤ 1 by
          simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (integrable_const 1)
    (ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦
      (radialDensityWeight_tendsto 0 z.1 hb).mul_const ⟪(z.2 : Cover),n⟫)
  convert ht using 1
  congr 1
  rw [← integral_indicator (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from
    Metric.isOpen_ball.measurableSet.preimage measurable_fst)]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    dsimp only
    by_cases hz : z.1 ∈ Metric.ball (0 : Cover) b
    · rw [Set.indicator_of_mem (show z ∈ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_mem hz,one_mul]
    · rw [Set.indicator_of_notMem (show z ∉ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_notMem hz,zero_mul]

lemma flat_set_limit_flux_on_ball {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
      ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = Real.pi*b^2 := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
    have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
    have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
      (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
        (radialDensityWeight_tsupport hb.le hε)
    have hh := hflux F hF (hFb.trans (Metric.closedBall_subset_closedBall hb1.le))
    simp only [F,inner_smul_right] at hh
    rw [hh,setIntegral_divergence_congr_local hA (measurableSet_coverHalfspace n) hAn
      (hFb.trans (Metric.closedBall_subset_ball hb1)),setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  exact tendsto_nhds_unique (radial_normal_flux_tendsto ν hn hb)
    ((integral_radialDensityWeight_plane_tendsto n hb).congr' (he.mono fun _ h ↦ h.symm))

lemma flat_set_limit_density {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {θ : ℝ} (hθ : 0 ≤ θ)
    (heq : coverLocalPerimeter A (Metric.closedBall (0 : Cover) (1/2)) =
      ENNReal.ofReal (θ*(1/2)^2)) : θ = Real.pi := by
  have hl : coverLocalPerimeter A (Metric.closedBall (0 : Cover) (1/2)) =
      coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) (1/2)) := by
    apply coverLocalPerimeter_congr_local hA (measurableSet_coverHalfspace n)
    filter_upwards [hAn] with x hx hxb
    exact hx (Metric.closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1) hxb)
  rw [hl,coverLocalPerimeter_halfspace hn (by norm_num)] at heq
  have hh := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)] at hh
  nlinarith

theorem flat_set_limit_normal {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hm : (ν : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n := by
  let B : Set BlowupNormalBundle := {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)}
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have hi := (blowupNormal_inner_integrable ν hn).integrableOn (s := B)
  have he := flat_set_limit_flux_on_ball hA hn hAn hflux
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hz : (∫ z in B, 1-⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    rw [integral_sub (integrable_const 1) hi,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    change (ν : Measure BlowupNormalBundle).real B-_ = 0
    rw [hm,he,sub_self]
  have hnneg : ∀ z : BlowupNormalBundle, 0 ≤ 1-⟪(z.2 : Cover),n⟫ := by
    intro z
    have hh := real_inner_le_norm (z.2 : Cover) n
    rw [z.2.property,hn,one_mul] at hh
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hnneg)
    ((integrable_const 1).sub hi)).mp hz
  have hae' := (ae_restrict_iff' hB).mp hae
  filter_upwards [hae'] with z hz hzb
  have hh := hz hzb
  change 1-⟪(z.2 : Cover),n⟫ = 0 at hh
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hs : ‖(z.2 : Cover)-n‖^2 = 0 := by rw [norm_sub_sq_real,z.2.property,hn]; nlinarith
  exact sq_eq_zero_iff.mp hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem conical_halfspace_extend {B : Set Cover}
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) 1 → (t⁻¹ • x ∈ B ↔ x ∈ B))
    {N : Cover} (hN : N ≠ 0)
    (hhalf : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) (1/16) →
      (x ∈ B ↔ 0 < ⟪N,x⟫)) :
    ∃ n : Cover, ‖n‖ = 1 ∧ ∀ᵐ x : Cover ∂volume,
      x ∈ Metric.ball (0 : Cover) 1 → (x ∈ B ↔ x ∈ coverHalfspace n) := by
  let n : Cover := -(‖N‖⁻¹ • N)
  have hn : ‖n‖ = 1 := by
    dsimp [n]
    rw [norm_neg,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg N)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hN)]
  refine ⟨n,hn,?_⟩
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Cover)
    (by norm_num : (32 : ℝ)⁻¹ ≠ 0)
  filter_upwards [hc 32 (by norm_num),hq.ae hhalf] with x hx hh hb
  have hxb : (32 : ℝ)⁻¹ • x ∈ Metric.ball (0 : Cover) (1/16) := by
    have hx : ‖x‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hb
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  have he := (hx hb).symm.trans (hh hxb)
  rw [inner_smul_right] at he
  have hi : (0 < (32 : ℝ)⁻¹ * ⟪N,x⟫) ↔ 0 < ⟪N,x⟫ := mul_pos_iff_of_pos_left (by norm_num)
  refine (he.trans hi).trans ?_
  change (0 < ⟪N,x⟫) ↔ ⟪-(‖N‖⁻¹ • N),x⟫ < 0
  rw [inner_neg_left,inner_smul_left,neg_lt_zero]
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hN))).symm

lemma coverLocalPerimeter_halfspace_ball {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm
  · exact (coverLocalPerimeter_mono _ Metric.ball_subset_closedBall).trans
      (coverLocalPerimeter_halfspace_le hn hb.le)
  · have ht : Tendsto (fun a : ℝ ↦ ENNReal.ofReal (Real.pi*a^2)) (𝓝[<] b)
        (𝓝 (ENNReal.ofReal (Real.pi*b^2))) := by
      exact (ENNReal.continuous_ofReal.comp
        (show Continuous (fun a : ℝ ↦ Real.pi*a^2) by fun_prop)).continuousAt.tendsto.mono_left inf_le_left
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with a ha ha0
    rw [← coverLocalPerimeter_halfspace hn ha0]
    exact coverLocalPerimeter_mono _ (Metric.closedBall_subset_ball ha)

lemma halfspace_model_perimeter_ball {B : Set Cover} (hB : MeasurableSet B)
    {n : Cover} (hn : ‖n‖ = 1)
    (hhalf : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ B ↔ x ∈ coverHalfspace n))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    coverLocalPerimeter B (Metric.ball (0 : Cover) a) = ENNReal.ofReal (Real.pi*a^2) := by
  have he : coverLocalPerimeter B (Metric.ball (0 : Cover) a) =
      coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) a) := by
    apply coverLocalPerimeter_congr_local hB (measurableSet_coverHalfspace n)
    filter_upwards [hhalf] with x hx hb
    exact hx (Metric.ball_subset_ball ha1.le hb)
  rw [he]
  exact coverLocalPerimeter_halfspace_ball hn ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_secondary_halfspace {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
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
    {ν : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p δ))
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ (B : Set Cover) (φ : ℕ → ℕ) (N : Cover),
      MeasurableSet B ∧ StrictMono φ ∧ ‖N‖ = 1 ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ B ↔ x ∈ coverHalfspace N)) ∧
      ∃ σ : FiniteMeasure BlowupNormalBundle,
        (∀ᵐ z ∂(σ : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
          (z.2 : Cover) = N) ∧
        ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
          tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
          (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
          (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in B, divergence F x := by
  obtain ⟨B,hB,φ,hφ,hBc,c,q,hc,hq,hqlim,hactual⟩ :=
    actual_tangent_secondary_representation hV hE hmin r hr hrlim hA hconv p hp s hs hs1 hslim
  let c' : ℕ → MovingCenter.InteriorCenter := fun i ↦ ⟨c i,hc i⟩
  have hn : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]
  have hline := radial_cone_secondary_unit_line hA hB hcone p hp hp0
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop) hBc
  obtain ⟨D,hD,hprodD⟩ := line_invariant_local_product hB hn hline
  obtain ⟨C,hC,hprod⟩ := line_product_euclidean hD hprodD
  have hBc' := stationary_pair_secondary_cone hA hB
    (fun F hF hFs ↦ (hstationary F hF hFs).1)
    (fun F hF hFs ↦ (hstationary F hF hFs).2) p hp
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop)
    (by simpa only [add_comm] using hBc)
  have hCc (t : ℝ) (ht : 1 ≤ t) := conical_product_planar_cone hn hprod hBc' ht
  obtain ⟨M,hM,hper⟩ := isMinimizerAt_moving_limit_perimeter hV hE hmin
  obtain ⟨K,hK,hbv⟩ := planar_product_directional_bound hB hC hn hprod
    (mul_nonneg hM.le (sq_nonneg (1/8 : ℝ)))
    (hper c' q hq hqlim B hB 1 hactual (1/8) (by norm_num) (by norm_num) (by norm_num))
  obtain ⟨b,hb,hden⟩ := isMinimizerAt_secondary_two_sided_density hV hE hmin
  have hBden := hden r hr hrlim A hA hconv p hp hboundary
    (fun i ↦ s (φ i)) (fun i ↦ hs _) (hslim.comp hφ.tendsto_atTop) B hB hBc
  obtain ⟨ν',k,U,hU,hν',hsup,hstat'⟩ :=
    isMinimizerAt_moving_paired_normal_limit hV hE hmin hμ hH c' q hq hqlim hB hactual
  have hactual' := (hactual.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hq' := (hqlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hFs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) := (hstat' F hF hFs).2
  have heq (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :=
    moving_blowup_perimeter_eq_normal_ball hV hE hmin hμ
      (fun i ↦ c' (i+k)) (fun i ↦ q (i+k)) (fun i ↦ hq _) hq' hB hactual' hν' hflux ha ha1
  have hcomp (D : Set Cover) (hD : MeasurableSet D) (a b : ℝ)
      (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hBD : B ∆ D ⊆ Metric.ball (0 : Cover) a) :=
    isMinimizerAt_moving_limit_comparison hV hE hmin c' q hq hqlim
      hB hD hactual ha hab hb1 hb1 hBD
  obtain ⟨m,hm,hhalf⟩ := minimizing_planar_product_halfplane hB hC hn hcomp hprod hCc
    hK hbv heq hflux hb hBden
  obtain ⟨N,hN,hNmodel⟩ := planar_halfspace_lift hn hprod hm hhalf
  obtain ⟨n,hn,hmodel⟩ := conical_halfspace_extend hBc' hN hNmodel
  have hmass : (ν' : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2 := by
    rw [Measure.real_def,← heq (1/2) (by norm_num) (by norm_num),
      halfspace_model_perimeter_ball hB hn hmodel (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
  exact ⟨B,φ,n,hB,hφ,hn,hBc,hmodel,ν',flat_set_limit_normal hB hn hmodel hmass hflux,hstat'⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_minimizing_cone_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ),
      MeasurableSet A ∧ 0 < θ ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) := by
  have hc := cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ) < 1/2)
  obtain ⟨θ',hθ'0,hdens⟩ := exists_density_of_cmc_monotone (by norm_num : (0 : ℝ) < 1/4)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (weakCMC_cellBallMass_monotone hμ hH cubeCenter hc)
  obtain ⟨A,ν,θ,φ,U,hA,hθ0,hφ,hU,hconv,hν,hm,hflux,hrad⟩ :=
    isMinimizerAt_paired_blowup hV hE hmin hμ hH cubeCenter
      (by norm_num : (0 : ℝ) < 1/4) hc r hr hrlim
  have hrl : Tendsto (fun i ↦ r (φ i)) atTop (𝓝 0) := hrlim.comp hφ.tendsto_atTop
  have heθ : θ'=θ := by
    have hh := blowup_limit_ball_mass cubeCenter (fun i ↦ r (φ i)) (fun i ↦ hr _)
      (hrl.mono_left hU) hdens hν (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    have hh' := hm 1 (by norm_num) (by norm_num)
    norm_num at hh hh'
    exact hh.symm.trans hh'
  subst θ'
  have hsp : Tendsto (fun t ↦
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) t)/t^2)
        (𝓝[>] 0) (𝓝 θ) := by
    apply hdens.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with t ht
    change cellBallMass μ cubeCenter t / t^2 = _
    rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter t
      ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ht.le)).trans hc)]
  have heq (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) := isMinimizerAt_blowup_perimeter_eq
    hV hE hmin hμ hθ0 hsp (fun i ↦ r (φ i)) (fun i ↦ hr _) hrl hA hconv hm
    (fun F hF hs ↦ (hflux F hF hs).2) hb hb1
  refine ⟨A,ν,θ,φ,hA,isMinimizerAt_density_pos hV hE hmin hμ hcenter hsp,hφ,hconv,heq,?_,?_,hflux⟩
  · intro B hB a b ha hab hb1 hAB
    exact isMinimizerAt_blowup_local_minimal hV hE hmin hμ hsp (fun i ↦ r (φ i))
      (fun i ↦ hr _) hrl hA hB hconv ha hab (by linarith : b ≤ 2)
      (heq b (ha.trans hab) hb1) hAB
  · intro t ht
    exact radial_flux_cone_ae hA (fun ψ hψ hs ↦
      limit_set_radial_flux (fun F hF hFs ↦ (hflux F hF hFs).2) hrad hψ hs) ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_primary_cone_flat_secondary {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (θ : ℝ) (φ : ℕ → ℕ),
      MeasurableSet A ∧ 0 < θ ∧ StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) = ENNReal.ofReal (θ*b^2)) ∧
      (∀ B : Set Cover, MeasurableSet B → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        A ∆ B ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter A (Metric.closedBall (0 : Cover) b) ≤
          coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)) ∧
      (∀ t : ℝ, 1 ≤ t → ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
        (t⁻¹ • x ∈ A ↔ x ∈ A)) ∧
      ∀ p : Cover, ‖p‖ < 1 → p ≠ 0 →
        (∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
          0 < volume.real (Aᶜ ∩ Metric.ball p δ)) →
        ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → (∀ i, s i ≤ 1) → Tendsto s atTop (𝓝 0) →
        ∃ (B : Set Cover) (ψ : ℕ → ℕ) (n : Cover),
          MeasurableSet B ∧ StrictMono ψ ∧ ‖n‖ = 1 ∧
          Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
            |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (ψ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
            atTop (𝓝 0) ∧
          ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
            (x ∈ B ↔ x ∈ coverHalfspace n) := by
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  obtain ⟨A,ν,θ,φ,hA,hθ,hφ,hconv,hper,hcomp,hcone,hstat⟩ :=
    isMinimizerAt_minimizing_cone_blowup hV hE hmin hμ hH hcenter r hr hrlim
  refine ⟨A,θ,φ,hA,hθ,hφ,hconv,hper,hcomp,hcone,?_⟩
  intro p hp hp0 hboundary s hs hs1 hslim
  obtain ⟨B,ψ,n,hB,hψ,hn,hBc,hmodel,_,_,_⟩ := actual_secondary_halfspace hV hE hmin hμ hH
    (fun i ↦ r (φ i)) (fun i ↦ hr _) (hrlim.comp hφ.tendsto_atTop)
    hA hconv hcone hstat p hp hp0 hboundary s hs hs1 hslim
  exact ⟨B,ψ,n,hB,hψ,hn,hBc,hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_tangent_secondary_centered_representation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∃ (c : ℕ → Cover) (q : ℕ → ℝ), (∀ i, ‖c i-cubeCenter‖ ≤ 1/8) ∧
        Tendsto c atTop (𝓝 cubeCenter) ∧ (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun i ↦ ((i : ℝ)+1)⁻¹
  have hepos (i) : 0 < e i := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hnex (i : ℕ) : ∃ n : ℕ, i ≤ n ∧ r n < 1/(8*(‖p‖+1)) ∧
      (∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r n) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) <
          (s i)^3*e i := by
    have hp0 : 0 < (1 : ℝ)/(8*(‖p‖+1)) := by positivity
    exact ((eventually_ge_atTop i).and ((hrlim.eventually (Iio_mem_nhds hp0)).and
      (hconv.eventually (Iio_mem_nhds (mul_pos (pow_pos (hs i) 3) (hepos i)))))).exists
  choose n hn hnr hne using hnex
  have hnlim : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (eventually_ge_atTop b).mono (fun i hi ↦ hi.trans (hn i))
  let c : ℕ → Cover := fun i ↦ cubeCenter+r (n i) • p
  let q : ℕ → ℝ := fun i ↦ r (n i)*s i
  have hq (i) : 0 < q i := mul_pos (hr _) (hs _)
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,mul_zero,Function.comp_apply] using (hrlim.comp hnlim).mul hslim
  have hclim : Tendsto c atTop (𝓝 cubeCenter) := by
    simpa only [c,zero_smul,add_zero,Function.comp_apply] using
      tendsto_const_nhds.add ((hrlim.comp hnlim).smul_const p)
  have hcp (i) : ‖c i-cubeCenter‖ ≤ 1/8 := by
    simp only [c,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := (lt_div_iff₀ (by positivity : 0 < 8*(‖p‖+1))).mp (hnr i)
    nlinarith [hr (n i),norm_nonneg p]
  have hc (i) : Metric.ball (c i) (1/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply Set.Subset.trans _ (cubeCenter_closedBall_interior (by norm_num : (1/4 : ℝ)<1/2))
    intro x hx
    have hxp : ‖x-c i‖ < 1/8 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hh := norm_add_le (x-c i) (c i-cubeCenter)
    rw [sub_add_sub_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_eq_norm] using (by linarith [hcp i] : ‖x-cubeCenter‖ ≤ 1/4)
  obtain ⟨B,hB,φ,hφ,hBconv,_⟩ := isMinimizerAt_moving_blowup_limit hV hE hmin c
    (by norm_num : (0 : ℝ)<1/8) hc q hq hqlim (by norm_num : (0 : ℝ)<1)
  have herror (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-blowupCharacteristic E (c i) (q i) x|) ≤ e i := by
    have hsub : Metric.closedBall p (s i*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
      intro x hx
      have hh : ‖x-p‖ ≤ s i := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
      have hnn := norm_add_le (x-p) p
      rw [sub_add_cancel] at hnn
      simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith [hs1 i] : ‖x‖ ≤ 2)
    have hi : IntegrableOn (fun x ↦ |blowupCharacteristic E cubeCenter (r (n i)) x-
        A.indicator (fun _ ↦ (1 : ℝ)) x|) (Metric.closedBall (0 : Cover) 2) :=
      ((integrable_bounded_one (measurable_blowupCharacteristic hE _ _) (blowupCharacteristic_bound E _ _)).sub
        (integrable_bounded_one (measurable_const.indicator hA) (cover_indicator_bound A))).abs
    have hb := (local_affine_integral_le p (hs i) hi (fun _ ↦ abs_nonneg _) hsub).trans
      (mul_le_mul_of_nonneg_left (hne i).le (pow_nonneg (inv_nonneg.mpr (hs i).le) 3))
    have heq : (s i)⁻¹^3*((s i)^3*e i)=e i := by field_simp [(hs i).ne']
    rw [heq] at hb
    simpa only [blowupCharacteristic_affine,c,q,abs_sub_comm] using hb
  refine ⟨B,hB,φ,hφ,?_, (fun i ↦ c (φ i)), (fun i ↦ q (φ i)),
    (fun i ↦ hcp (φ i)), hclim.comp hφ.tendsto_atTop, (fun i ↦ hq (φ i)), hqlim.comp hφ.tendsto_atTop, hBconv⟩
  have hbound (i) : (∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) ≤
      e (φ i)+(∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E (c (φ i)) (q (φ i)) x-B.indicator (fun _ ↦ (1 : ℝ)) x|) := by
    exact (localL1_triangle ((measurable_const.indicator hA).comp (by fun_prop))
      (measurable_blowupCharacteristic hE (c (φ i)) (q (φ i))) (measurable_const.indicator hB)
      (fun _ ↦ cover_indicator_bound A _) (blowupCharacteristic_bound E (c (φ i)) (q (φ i))) (cover_indicator_bound B)).trans
      (add_le_add (herror (φ i)) le_rfl)
  exact squeeze_zero (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _)) hbound
    (by simpa using (helim.comp hφ.tendsto_atTop).add hBconv)

end CubicTorus

end
end

end

end OAI
