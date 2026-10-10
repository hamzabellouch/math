import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVSecondaryPlanarData

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_normal_modulus {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ C K ρ : ℝ, 0 < r₀ ∧ 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c₀ : Cover), ‖c₀-cubeCenter‖ ≤ 1/16 → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 →
        0 < r → r ≤ r₀ → 0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ ν : Cover → Cover,
        ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)) ∧
        (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ‖ν a‖ = 1 ∧ ‖n₀-ν a‖ ≤ C*e ∧
          BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
        ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
            dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i := by
  classical
  obtain ⟨R₀,ρ,C,hR₀,hρ,hρs,hC,hiter⟩ := isMinimizerAt_uniform_tilt_iteration hV hE hmin hcenter
  obtain ⟨U,A,hU,hA,hupper⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨L,c,hL,hc,hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  obtain ⟨D,d,hD,hd,hdensity⟩ := isMinimizerAt_two_sided_density hV hE hmin
  let r₀ := min R₀ (min (U/2) (min L (1/8)))
  let M := 2+128*A*C^2
  have hM : 0 < M := by dsimp [M]; positivity
  let K := 4*Real.sqrt M/Real.sqrt c
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨r₀,4*C,K,ρ,by dsimp [r₀]; positivity,by positivity,hK,hρ,hρs,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δ₀,hδ₀,hiteration⟩ := hiter μ hμ N hN hp hu
  refine ⟨δ₀/2,by positivity,?_⟩
  intro c₀ hc₀ n₀ r e hn₀ hr hrr he heδ hratio htilt
  have hrR : r ≤ R₀ := hrr.trans (min_le_left _ _)
  have hrU : r ≤ U/2 := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrL : r ≤ L := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrs : r ≤ 1/8 := hrr.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heδ₀ : 2*e ≤ δ₀ := by linarith
  have hratio' : (r/2)/(2*e)^2 ≤ δ₀ := by
    have heq : (r/2)/(2*e)^2 = (r/e^2)/8 := by ring
    rw [heq]
    linarith
  let S := quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128)
  have hdata : ∀ a : Cover, ∃ ν : Cover, a ∈ S → ‖ν‖ = 1 ∧ ‖n₀-ν‖ ≤ 4*C*e ∧
      BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) ν ∧
      ∀ i : ℕ, (∫ z in Metric.closedBall (quotientMap a) (2*(ρ^i*(r/2))), ‖N z-ν‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*(r/2))^2*
          (Real.sqrt M*((1/2:ℝ)^i*(2*e)))^2 := by
    intro a
    by_cases ha : a ∈ S
    swap
    · exact ⟨n₀,fun h ↦ (ha h).elim⟩
    have hac : ‖a-c₀‖ < r/128 := by simpa only [Metric.mem_ball,dist_eq_norm] using ha.2
    let a' : InteriorCenter := ⟨a,by
      have hh := norm_sub_le_norm_sub_add_norm_sub a c₀ cubeCenter
      linarith⟩
    have hsub : Metric.closedBall (quotientMap a) (17*(r/2)) ⊆
        Metric.closedBall (quotientMap c₀) (17*r) := by
      intro z hz
      have hz' : dist z (quotientMap a) ≤ 17*(r/2) := hz
      have hdist : dist (quotientMap a) (quotientMap c₀) ≤ r/128 := by
        rw [dist_eq_norm, ← quotientMap_sub]
        exact (norm_quotientMap_le _).trans hac.le
      change dist z (quotientMap c₀) ≤ 17*r
      linarith [dist_triangle z (quotientMap a) (quotientMap c₀)]
    have ht' : (∫ z in Metric.closedBall (quotientMap a) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
      (setIntegral_mono_set (polar_tilt_integrable hN hu n₀).integrableOn
      (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE).trans htilt
    have ht'' : (∫ z in Metric.closedBall (quotientMap (a' : Cover)) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r/2)^2*(2*e)^2 := by
      convert ht' using 1; ring
    obtain ⟨n,ν,hnzero,hn,hν,hnt,ht,hclose⟩ := hiteration a' ha.1 n₀ (r/2) (2*e) hn₀
      (by positivity) (by linarith) (by positivity) heδ₀ hratio' ht''
    have hmass : ∀ s : ℝ, 0 < s → s ≤ r/2 →
        (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall (quotientMap a) s) ≤ (4*A)*s^2 := by
      intro s hs hsr
      have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : s < 2*s))).trans
        (hupper μ hμ (quotientMap a) (2*s) (by positivity) (by linarith))
      nlinarith only [hh]
    have hosc := iterated_tilt_limit_oscillation_tendsto hN hu (quotientMap a) hρ
      (by linarith : ρ < 1) (by positivity : 0 < r/2) (by positivity : 0 ≤ 2*e)
      (by positivity : 0 ≤ 4*A) hC.le n hν hmass ht hclose
    have hd' : ∀ a ∈ frontier (openRepresentative E), ∀ t : ℝ, 0 < t → t ≤ D →
        d*t^3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
        d*t^3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t) := by
      rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
      exact hdensity
    refine ⟨ν,fun _ ↦ ⟨hν,?_,normal_oscillation_implies_boundary_flatness hE hμ hN hp hu hD hd hd' ha.1 hν hosc,?_⟩⟩
    · have hh := hclose 0
      rw [hnzero,pow_zero,mul_one] at hh
      nlinarith only [hh]
    · intro i
      have hi : 0 < ρ^i*(r/2) := by positivity
      have hir : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
        (pow_le_one₀ hρ.le (by linarith))
      have hm : (spatialNormalMeasure μ : Measure Torus).real
          (Metric.closedBall (quotientMap a) (2*(ρ^i*(r/2)))) ≤ 16*A*(ρ^i*(r/2))^2 := by
        have hh := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : 2*(ρ^i*(r/2)) < 4*(ρ^i*(r/2))))).trans
          (hupper μ hμ (quotientMap a) (4*(ρ^i*(r/2))) (by positivity) (by linarith))
        nlinarith only [hh]
      have hci : ‖n i-ν‖ ≤ 2*C*((1/2:ℝ)^i*(2*e)) := by
        convert hclose i using 1; ring
      have hh := polar_tilt_limit_two_radius hN hu (quotientMap a) hi hA.le (n i) ν hm (ht i) hci
      rw [mul_pow (Real.sqrt M),Real.sq_sqrt hM.le]
      dsimp [M] at *
      nlinarith only [hh]
  choose ν hν using hdata
  refine ⟨ν,?_,fun a ha ↦ ⟨(hν a ha).1,(hν a ha).2.1,(hν a ha).2.2.1⟩,?_⟩
  · apply continuousOn_of_uniform_normal_tilt hN hu S ν hc
      (fun i ↦ ρ^i*(r/2)) (fun i ↦ Real.sqrt M*((1/2:ℝ)^i*(2*e)))
      (fun i ↦ by positivity) (fun i ↦ by positivity)
    · have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (1/2:ℝ) < 1)).mul_const (2*e)).const_mul (Real.sqrt M)
      simpa only [zero_mul,mul_zero] using hh
    · intro a ha i
      apply hlower μ hμ (quotientMap a)
      · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact ha.1
      · positivity
      · have hh : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
          (pow_le_one₀ hρ.le (by linarith))
        linarith
    · exact fun a ha i ↦ (hν a ha).2.2.2 i
  · intro i a ha b hb hab
    have hri : 0 < ρ^i*(r/2) := by positivity
    have hris : ρ^i*(r/2) ≤ r/2 := mul_le_of_le_one_left (by positivity)
      (pow_le_one₀ hρ.le (by linarith))
    have hmass : c*(ρ^i*(r/2))^2 ≤
        (spatialNormalMeasure μ : Measure Torus).real
          (Metric.ball (quotientMap a) (ρ^i*(r/2))) := by
      apply hlower μ hμ (quotientMap a)
      · rw [← isMinimizerAt_frontier_openRepresentative hV hE hmin]
        exact ha.1
      · exact hri
      · linarith
    have hdist : dist (quotientMap a) (quotientMap b) ≤ ρ^i*(r/2) := by
      rw [dist_eq_norm,← quotientMap_sub]
      exact (norm_quotientMap_le _).trans (by simpa only [dist_eq_norm] using hab)
    have hh := polar_normal_nearby_centers hN hu (quotientMap a) (quotientMap b)
      hc hri (by positivity : 0 ≤ Real.sqrt M*((1/2 : ℝ)^i*(2*e)))
      hmass hdist (ν a) (ν b) ((hν a ha).2.2.2 i) ((hν b hb).2.2.2 i)
    rw [dist_eq_norm]
    convert hh using 1
    dsimp [K]
    ring

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

def blowupTilt (n : Cover) (z : BlowupNormalBundle) : ℝ :=
  radialHeightCutoff 0 (1/8) z.1 * ‖(z.2 : Cover)-n‖^2

lemma continuous_blowupTilt (n : Cover) : Continuous (blowupTilt n) := by
  exact ((radialDensityWeight_contDiff 0 (2*(1/8)) (3*(1/8)^2)).continuous.comp
    continuous_fst).mul (((continuous_subtype_val.comp continuous_snd).sub continuous_const).norm.pow 2)

lemma blowupTilt_nonneg (n : Cover) (z : BlowupNormalBundle) : 0 ≤ blowupTilt n z :=
  mul_nonneg (radialDensityWeight_nonneg _ _ _ _) (sq_nonneg _)

lemma blowupTilt_zero (n : Cover) (z : BlowupNormalBundle)
    (hz : z.1 ∉ Metric.ball (0 : Cover) (1/4)) : blowupTilt n z = 0 := by
  have hx : (1/4 : ℝ) ≤ ‖z.1‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hz
  have hh := radialDensityWeight_zero (a := (0 : Cover)) (r := (2*(1/8):ℝ))
    (ε := (3*(1/8)^2 : ℝ)) (x := z.1) (by norm_num) (by norm_num) (by norm_num; linarith)
  dsimp only [blowupTilt,radialHeightCutoff]
  rw [hh,zero_mul]

lemma blowupTilt_hasCompactSupport (n : Cover) : HasCompactSupport (blowupTilt n) := by
  apply ((isCompact_closedBall (0 : Cover) (1/4)).prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
  intro z hz
  refine ⟨?_,mem_univ _⟩
  by_contra h
  exact hz (blowupTilt_zero n z (fun hh ↦ h (Metric.ball_subset_closedBall hh)))

lemma flat_normal_tilt_limit {μ : FiniteMeasure NormalBundle} (c : Cover)
    (r : ℕ → ℝ) {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ c (r i) 2) l (𝓝 ν))
    {n : Cover}
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n) :
    Tendsto (fun i ↦ ∫ z, blowupTilt n z
      ∂(blowupNormalMeasure μ c (r i) 2 : Measure BlowupNormalBundle)) l (𝓝 0) := by
  have hh := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
    (ofCompactSupport _ (continuous_blowupTilt n) (blowupTilt_hasCompactSupport n))
  have he : (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hflat] with z hz
    change blowupTilt n z = 0
    by_cases hb : z.1 ∈ Metric.ball (0 : Cover) (1/4)
    · have hn := hz (Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1/2) hb)
      simp only [blowupTilt,hn,sub_self,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · exact blowupTilt_zero n z hb
  change Tendsto (fun i ↦ ∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c (r i) 2 : Measure BlowupNormalBundle)) l
    (𝓝 (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle))) at hh
  rwa [he] at hh

lemma spatial_tilt_le_blowupTilt {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c n : Cover) {r : ℝ} (hr : 0 < r)
    (hc : Metric.ball c (r/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    (∫ x in Metric.closedBall (quotientMap c) (r/16), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      r^2*(∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c r 2 : Measure BlowupNormalBundle)) := by
  have hi : Integrable (fun z : NormalBundle ↦ blowupTilt n (blowupNormalMap c r z))
      (μ : Measure NormalBundle) :=
    ((continuous_blowupTilt n).comp (continuous_blowupNormalMap c r)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : (∫ x in Metric.closedBall (quotientMap c) (r/16), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ z, blowupTilt n (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
    calc
      _ ≤ ∫ x in Metric.ball (quotientMap c) (r/8), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus) :=
        setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
          (ae_of_all _ fun _ ↦ sq_nonneg _) (Metric.closedBall_subset_ball (by linarith)).eventuallyLE
      _ = ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r/8)}, ‖(z.2 : Cover)-n‖^2
          ∂(μ : Measure NormalBundle) := integral_polar_tilt_ball hN hp c n (r/8) hc
      _ = ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r/8)},
          blowupTilt n (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
        apply setIntegral_congr_fun (Metric.isOpen_ball.measurableSet.preimage
          (continuous_subtype_val.comp continuous_fst).measurable)
        intro z hz
        have hzm : (blowupNormalMap c r z).1 ∈ Metric.closedBall (0 : Cover) (1/8) := by
          apply Metric.ball_subset_closedBall
          rw [blowupNormalMap_mem c hr]
          change (z.1 : Cover) ∈ Metric.ball c (r*(1/8))
          change (z.1 : Cover) ∈ Metric.ball c (r/8) at hz
          simpa only [div_eq_mul_inv,one_div,one_mul] using hz
        dsimp only
        change ‖(z.2 : Cover)-n‖^2 = radialHeightCutoff 0 (1/8) (blowupNormalMap c r z).1 * ‖(z.2 : Cover)-n‖^2
        rw [radialHeightCutoff_one (by norm_num : (0 : ℝ) < 1/8) hzm,one_mul]
      _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun z ↦ blowupTilt_nonneg n _)
  rw [integral_blowup_test μ c hr (continuous_blowupTilt n) (fun z hz ↦
    blowupTilt_zero n z (fun hh ↦ hz (Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 2) hh)))]
  convert hb using 1
  field_simp [hr.ne']

theorem isMinimizerAt_c1_of_flat_normal_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {l : Filter ℕ} [NeBot l]
    (hrlim : Tendsto r l (𝓝 0)) {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ cubeCenter (r i) 2) l (𝓝 ν))
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n) :
    C1RegularPoint (openRepresentative E) (quotientMap cubeCenter) := by
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨R,hR,htheorem⟩ := MovingCenter.isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨δ,hδ,hregular⟩ := htheorem μ hμ N hN hp hu
  let e := δ/2
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : 0 < min (272*R) (min (272*(1/8)) (min (272*δ*e^2) 1)) := by positivity
  have hs := hrlim.eventually (Iio_mem_nhds hsmall)
  have ht := (flat_normal_tilt_limit cubeCenter r hlim hflat).eventually
    (Iio_mem_nhds (show 0 < e^2/272^2 by positivity))
  obtain ⟨i,hri,hti⟩ := (hs.and ht).exists
  have hrpos := hr i
  have hrR : r i/272 ≤ R := by have hh := hri.trans_le (min_le_left _ _); linarith
  have hrs : r i/272 ≤ 1/8 := by
    have hh := hri.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hratio : (r i/272)/e^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hri.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hchart : Metric.ball cubeCenter (r i/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} := by
    apply Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior _)
    have hh := hri.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  have htilt := spatial_tilt_le_blowupTilt hN hp hu cubeCenter n (hr i) hchart
  have hbound : (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*(r i/272)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i/272)^2*e^2 := by
    rw [show 17*(r i/272)=r i/16 by ring]
    calc
      _ ≤ _ := htilt
      _ ≤ (r i)^2*(e^2/272^2) := mul_le_mul_of_nonneg_left hti.le (sq_nonneg _)
      _ = _ := by ring
  obtain ⟨g,hg,hgC,hi,hb⟩ := hregular cubeCenter (by simp) hcenter n (r i/272) e hn
    (by positivity) hrR he (by dsimp [e]; linarith) hratio hbound
  have hpatch := c1Patch_of_exact_graph cubeCenter hn (by positivity : 0 < r i/272) hrs hgC hi hb
  exact ⟨quotientMap cubeCenter,n,g,(r i/272)/1024,(r i/272)/1024,hpatch,
    Metric.mem_ball_self (by positivity)⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def BoundaryNormalChart (E : Set Torus) (c n : Cover) (r e C K ρ : ℝ) : Prop :=
  ∃ ν : Cover → Cover,
    ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128)) ∧
    (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
      ‖ν a‖ = 1 ∧ ‖n-ν a‖ ≤ C*e ∧
      BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
    ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
      ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c (r/128),
        dist a b ≤ ρ^i*(r/2) → dist (ν a) (ν b) ≤ K*e*(1/2 : ℝ)^i

lemma flat_moving_normal_tilt_limit {μ : FiniteMeasure NormalBundle} (c : ℕ → Cover)
    (r : ℕ → ℝ) {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    {n : Cover}
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n) :
    Tendsto (fun i ↦ ∫ z, blowupTilt n z
      ∂(blowupNormalMeasure μ (c i) (r i) 2 : Measure BlowupNormalBundle)) l (𝓝 0) := by
  have hh := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
    (ofCompactSupport _ (continuous_blowupTilt n) (blowupTilt_hasCompactSupport n))
  have he : (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hflat] with z hz
    change blowupTilt n z = 0
    by_cases hb : z.1 ∈ Metric.ball (0 : Cover) (1/4)
    · have hn := hz (Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1/2) hb)
      simp only [blowupTilt,hn,sub_self,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · exact blowupTilt_zero n z hb
  change Tendsto (fun i ↦ ∫ z, blowupTilt n z ∂(blowupNormalMeasure μ (c i) (r i) 2 : Measure BlowupNormalBundle)) l
    (𝓝 (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle))) at hh
  rwa [he] at hh

theorem isMinimizerAt_flat_moving_normal_charts {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {l : Filter ℕ} [NeBot l]
    (hrlim : Tendsto r l (𝓝 0)) (hc : ∀ᶠ i in l, ‖c i-cubeCenter‖ ≤ 1/16)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n) :
    ∃ C K ρ δ : ℝ, 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < δ ∧
      ∀ e : ℝ, 0 < e → e ≤ δ → ∀ᶠ i in l,
        BoundaryNormalChart E (c i) n (r i/272) e C K ρ := by
  obtain ⟨R,C,K,ρ,hR,hC,hK,hρ,hρs,hmod⟩ :=
    MovingCenter.isMinimizerAt_moving_normal_modulus hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hcharts⟩ := hmod μ hμ N hN hp hu
  refine ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,?_⟩
  intro e he heδ
  have hsmall : 0 < min (272*R) (min (272*δ*e^2) 1) := by positivity
  have hs := hrlim.eventually (Iio_mem_nhds hsmall)
  have ht := (flat_moving_normal_tilt_limit c r hlim hflat).eventually
    (Iio_mem_nhds (show 0 < e^2/272^2 by positivity))
  filter_upwards [hc,hs,ht] with i hci hri hti
  have hrR : r i/272 ≤ R := by have hh := hri.trans_le (min_le_left _ _); linarith
  have hratio : (r i/272)/e^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hri.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hr1 : r i < 1 := hri.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let d : MovingCenter.InteriorCenter := ⟨c i,by linarith⟩
  have hchart : Metric.ball (c i) (r i/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d) (by linarith))
  have htilt := spatial_tilt_le_blowupTilt hN hp hu (c i) n (hr i) hchart
  have hbound : (∫ x in Metric.closedBall (quotientMap (c i)) (17*(r i/272)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i/272)^2*e^2 := by
    rw [show 17*(r i/272)=r i/16 by ring]
    calc
      _ ≤ _ := htilt
      _ ≤ (r i)^2*(e^2/272^2) := mul_le_mul_of_nonneg_left hti.le (sq_nonneg _)
      _ = _ := by ring
  exact hcharts (c i) hci n (r i/272) e hn (div_pos (hr i) (by norm_num)) hrR he heδ hratio hbound

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma preconnected_crosses_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsPreconnected S) (hU : IsOpen U)
    (h₁ : (S ∩ U).Nonempty) (h₂ : (S ∩ Uᶜ).Nonempty) :
    (S ∩ frontier U).Nonempty := by
  classical
  by_contra h
  have hd : Disjoint (frontier U) S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    exact h ⟨x,hxs,hx⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hc := isClopen_preimage_val hU hd
  obtain ⟨x,hxS,hxU⟩ := h₁
  have he : (Subtype.val ⁻¹' U : Set S) = univ := hc.eq_univ ⟨⟨x,hxS⟩,hxU⟩
  obtain ⟨y,hyS,hyU⟩ := h₂
  have hy : (⟨y,hyS⟩ : S) ∈ Subtype.val ⁻¹' U := by rw [he]; trivial
  exact hyU hy

lemma isMinimizerAt_two_phase_frontier_in_ball {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : Cover) (r : ℝ)
    (h₁ : 0 < torusVolume.real (E ∩ Metric.ball (quotientMap c) r))
    (h₂ : 0 < torusVolume.real (Eᶜ ∩ Metric.ball (quotientMap c) r)) :
    ∃ a ∈ Metric.ball c r, quotientMap a ∈ frontier (openRepresentative E) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hp₁ : 0 < torusVolume.real (openRepresentative E ∩ Metric.ball (quotientMap c) r) := by
    convert h₁ using 1
    exact congrArg ENNReal.toReal (measure_congr (hae.inter EventuallyEq.rfl))
  have hp₂ : 0 < torusVolume.real ((openRepresentative E)ᶜ ∩ Metric.ball (quotientMap c) r) := by
    convert h₂ using 1
    exact congrArg ENNReal.toReal (measure_congr (hae.compl.inter EventuallyEq.rfl))
  have hcon : IsPreconnected (Metric.ball (quotientMap c) r) := by
    rw [← quotientMap_image_ball c r]
    exact (convex_ball c r).isPreconnected.image _ continuous_quotientMap.continuousOn
  obtain ⟨b,hbb,hb⟩ := preconnected_crosses_frontier hcon (isOpen_openRepresentative E)
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₁.ne')
    (by simpa only [inter_comm] using nonempty_of_measureReal_ne_zero hp₂.ne')
  rw [← quotientMap_image_ball c r] at hbb
  obtain ⟨a,ha,rfl⟩ := hbb
  exact ⟨a,ha,hb⟩

theorem isMinimizerAt_moving_frontier_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0)) {R : ℝ} {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hpos : 0 < volume.real (A ∩ Metric.ball (0 : Cover) ρ) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball (0 : Cover) ρ)) :
    ∀ᶠ i in atTop, ∃ a ∈ Metric.ball (c i : Cover) (r i*ρ),
      quotientMap a ∈ frontier (openRepresentative E) := by
  have hint := localL1_ball_integral_tendsto hρR
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv
  have hconvc : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic Eᶜ (c i) (r i) x-Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
    simp_rw [complement_blowup_error]
    exact hconv
  have hintc := localL1_ball_integral_tendsto hρR
    (fun i ↦ blowupCharacteristic Eᶜ (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE.compl (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound Eᶜ (c i) (r i))
    (measurable_const.indicator hA.compl) (cover_indicator_bound Aᶜ) hconvc
  rw [integral_indicator_ball_real A hA ρ] at hint
  rw [integral_indicator_ball_real Aᶜ hA.compl ρ] at hintc
  have hsmall : ∀ᶠ i in atTop, r i*ρ < 3/8 :=
    (hrlim.eventually (gt_mem_nhds (div_pos (by norm_num : (0 : ℝ) < 3/8) hρ))).mono
      fun index hindex ↦ (lt_div_iff₀ hρ).mp hindex
  filter_upwards [hsmall,hint.eventually (lt_mem_nhds hpos.1),
    hintc.eventually (lt_mem_nhds hpos.2)] with i hi hip hic
  have hc : Metric.ball (c i : Cover) (r i*ρ) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior hi)
  apply isMinimizerAt_two_phase_frontier_in_ball hV hE hmin
  · rw [integral_blowupCharacteristic_ball hE (c i) (hr i) ρ hc]
    exact mul_pos (pow_pos (hr i) 3) hip
  · rw [integral_blowupCharacteristic_ball hE.compl (c i) (hr i) ρ hc]
    exact mul_pos (pow_pos (hr i) 3) hic

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_flat_moving_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0)) (hc : ∀ᶠ i in atTop, ‖(c i : Cover)-cubeCenter‖ ≤ 1/32)
    {ν : FiniteMeasure BlowupNormalBundle} {l : Filter ℕ} [NeBot l] (hl : l ≤ atTop)
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    {n : Cover} (hn : ‖n‖ = 1)
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n)
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    (hphases : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      0 < volume.real (A ∩ Metric.ball (0 : Cover) ρ) ∧
        0 < volume.real (Aᶜ ∩ Metric.ball (0 : Cover) ρ)) :
    ∀ᶠ i in l, ∃ a : Cover, dist a (c i : Cover) < r i/(544*4096) ∧
      ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
        ContDiffOn ℝ 1 g (Metric.ball 0 ((r i/544)/1024)) ∧
        (∀ y ∈ Metric.ball (0 : Plane) ((r i/544)/1024),
          quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
          ‖normalGraph n g y‖ < (r i/544)/512) ∧
        (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((r i/544)/128),
          normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a) := by
  obtain ⟨R,hR,hgraphs⟩ := MovingCenter.isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hgraph⟩ := hgraphs μ hμ N hN hp hu
  let e := δ/2
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : 0 < min (544*R) (min (544*δ*e^2) (1/32)) := by positivity
  have hs := hrlim.eventually (Iio_mem_nhds hsmall)
  have ht := (flat_moving_normal_tilt_limit (fun i ↦ (c i : Cover)) r hlim hflat).eventually
    (Iio_mem_nhds (show 0 < e^2/544^2 by positivity))
  have hpoints := isMinimizerAt_moving_frontier_approximation hV hE hmin c r hr hrlim hA hconv
    (by norm_num : (0:ℝ) < 1/(544*4096)) (by norm_num : (1:ℝ)/(544*4096) ≤ 1)
    (hphases _ (by norm_num) (by norm_num))
  filter_upwards [hc.filter_mono hl,hs.filter_mono hl,ht,hpoints.filter_mono hl] with i hci hri hti hpoint
  obtain ⟨a,ha,hbase⟩ := hpoint
  have had : dist a (c i : Cover) < r i/(544*4096) := by
    simpa only [Metric.mem_ball,div_eq_mul_inv,one_mul] using ha
  have hrR : r i/544 ≤ R := by have hh := hri.trans_le (min_le_left _ _); linarith
  have hrsmall : r i < 1/32 := hri.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hratio : (r i/544)/e^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hri.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hnear : ‖a-cubeCenter‖ ≤ 1/16 := by
    have hh := dist_triangle a (c i : Cover) cubeCenter
    simp only [dist_eq_norm] at hh had
    linarith
  have hchart : Metric.ball (c i : Cover) (r i/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (by linarith : r i/8 < 3/8))
  have htilt := spatial_tilt_le_blowupTilt hN hp hu (c i) n (hr i) hchart
  have hadq : dist (quotientMap a) (quotientMap (c i)) < r i/(544*4096) := by
    rw [dist_eq_norm,← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [dist_eq_norm] using had)
  have hsub : Metric.closedBall (quotientMap a) (17*(r i/544)) ⊆
      Metric.closedBall (quotientMap (c i)) (r i/16) := by
    intro x hx
    have hx' : dist x (quotientMap a) ≤ 17*(r i/544) := hx
    have hh := dist_triangle x (quotientMap a) (quotientMap (c i))
    change dist x (quotientMap (c i)) ≤ r i/16
    linarith [hr i]
  have hbound : (∫ x in Metric.closedBall (quotientMap a) (17*(r i/544)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i/544)^2*e^2 := by
    calc
      _ ≤ (∫ x in Metric.closedBall (quotientMap (c i)) (r i/16), ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) := setIntegral_mono_set
          (polar_tilt_integrable hN hu n).integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub.eventuallyLE
      _ ≤ _ := htilt
      _ ≤ (r i)^2*(e^2/544^2) := mul_le_mul_of_nonneg_left hti.le (sq_nonneg _)
      _ = _ := by ring
  exact ⟨a,had,hgraph a hnear hbase n (r i/544) e hn (div_pos (hr i) (by norm_num))
    hrR he (by dsimp [e]; linarith) hratio hbound⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_secondary_graph_approximants {V : ℝ} (hV : V ∈ Ioo 0 1)
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
    {ν : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : ∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
      0 < volume.real (Aᶜ ∩ Metric.ball p δ))
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ (B : Set Cover) (φ : ℕ → ℕ) (n : Cover),
      MeasurableSet B ∧ StrictMono φ ∧ ‖n‖ = 1 ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ B ↔ x ∈ coverHalfspace n)) ∧
      ∃ (c : ℕ → MovingCenter.InteriorCenter) (q : ℕ → ℝ) (U : Ultrafilter ℕ),
        (U : Filter ℕ) ≤ atTop ∧ (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ (c i : Cover)) atTop (𝓝 cubeCenter) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) ∧
        ∀ᶠ i in (U : Filter ℕ), ∃ a : Cover, dist a (c i : Cover) < q i/(544*4096) ∧
          ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
            ContDiffOn ℝ 1 g (Metric.ball 0 ((q i/544)/1024)) ∧
            (∀ y ∈ Metric.ball (0 : Plane) ((q i/544)/1024),
              quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
              ‖normalGraph n g y‖ < (q i/544)/512) ∧
            (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((q i/544)/128),
              normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a) := by
  obtain ⟨B,hB,φ,hφ,hBc,c,q,hc,hclim,hq,hqlim,hactual⟩ :=
    actual_tangent_secondary_centered_representation hV hE hmin r hr hrlim hA hconv p hp s hs hs1 hslim
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
  have hcsmall : ∀ᶠ i in atTop, ‖(c' (i+k) : Cover)-cubeCenter‖ ≤ 1/32 := by
    have hh : Tendsto (fun i ↦ ‖(c' (i+k) : Cover)-cubeCenter‖) atTop (𝓝 0) := by
      simpa using ((hclim.comp (tendsto_add_atTop_nat k)).sub (tendsto_const_nhds (x := cubeCenter))).norm
    exact (hh.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/32))).mono (fun _ hi ↦ hi.le)
  have hgraphs := isMinimizerAt_flat_moving_graphs hV hE hmin hcenter hμ
    (fun i ↦ c' (i+k)) (fun i ↦ q (i+k)) (fun i ↦ hq _)
    (hqlim.comp (tendsto_add_atTop_nat k)) hcsmall hU hν' hn
    (flat_set_limit_normal hB hn hmodel hmass hflux) hB
    (hactual.comp (tendsto_add_atTop_nat k))
    (fun ρ hρ hρ1 ↦ ⟨(mul_pos hb (pow_pos hρ 3)).trans_le (hBden ρ hρ hρ1).1,
      (mul_pos hb (pow_pos hρ 3)).trans_le (hBden ρ hρ hρ1).2⟩)
  exact ⟨B,φ,n,hB,hφ,hn,hBc,hmodel,(fun i ↦ c' (i+k)),(fun i ↦ q (i+k)),U,hU,
    (fun i ↦ hq _),hqlim.comp (tendsto_add_atTop_nat k),
    hclim.comp (tendsto_add_atTop_nat k),hactual.comp (tendsto_add_atTop_nat k),hgraphs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_primary_cone_secondary_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
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
    ∃ (B : Set Cover) (φ : ℕ → ℕ) (n : Cover),
      MeasurableSet B ∧ StrictMono φ ∧ ‖n‖ = 1 ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
        (x ∈ B ↔ x ∈ coverHalfspace n)) ∧
      ∃ (c : ℕ → MovingCenter.InteriorCenter) (q : ℕ → ℝ) (U : Ultrafilter ℕ),
        (U : Filter ℕ) ≤ atTop ∧ (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ (c i : Cover)) atTop (𝓝 cubeCenter) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) ∧
        ∀ᶠ i in (U : Filter ℕ), ∃ a : Cover, dist a (c i : Cover) < q i/(544*4096) ∧
          ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
            ContDiffOn ℝ 1 g (Metric.ball 0 ((q i/544)/1024)) ∧
            (∀ y ∈ Metric.ball (0 : Plane) ((q i/544)/1024),
              quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
              ‖normalGraph n g y‖ < (q i/544)/512) ∧
            (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((q i/544)/128),
              normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a) := by
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hcenter hμ
  obtain ⟨A,ν,θ,φ,hA,hθ,hφ,hconv,hper,hcomp,hcone,hstat⟩ :=
    isMinimizerAt_minimizing_cone_blowup hV hE hmin hμ hH hcenter r hr hrlim
  refine ⟨A,θ,φ,hA,hθ,hφ,hconv,hper,hcomp,hcone,?_⟩
  intro p hp hp0 hboundary s hs hs1 hslim
  exact actual_secondary_graph_approximants hV hE hmin hcenter hμ hH
    (fun i ↦ r (φ i)) (fun i ↦ hr _) (hrlim.comp hφ.tendsto_atTop)
    hA hconv hcone hstat p hp hp0 hboundary s hs hs1 hslim

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_rescaled_normal_equicontinuity {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (c n : ℕ → Cover) (r e : ℕ → ℝ),
        (∀ j, ‖c j-cubeCenter‖ ≤ 1/16 ∧ ‖n j‖ = 1 ∧
          0 < r j ∧ r j ≤ r₀ ∧ 0 < e j ∧ e j ≤ δ ∧ r j/(e j)^2 ≤ δ ∧
          (∫ x in Metric.closedBall (quotientMap (c j)) (17*r j), ‖N x-n j‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r j)^2*(e j)^2) →
        let S := fun j ↦ (fun x : Cover ↦ c j+r j • x) ⁻¹'
          (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball (c j) (r j/128))
        ∃ ν : ℕ → Cover → Cover,
          (∀ j, ContinuousOn (ν j) (S j)) ∧
          (∀ j x, x ∈ S j → ‖ν j x‖ = 1 ∧ ‖n j-ν j x‖ ≤ C*e j ∧
            BoundaryFlatAt (frontier (openRepresentative E))
              (quotientMap (c j+r j • x)) (ν j x)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
            ∀ j x, x ∈ S j → ∀ y, y ∈ S j → dist x y < η →
              dist (ν j x) (ν j y) < ε := by
  classical
  obtain ⟨r₀,C,K,ρ,hr₀,hC,hK,hρ,hρs,hmod⟩ :=
    isMinimizerAt_moving_normal_modulus hV hE hmin hcenter
  refine ⟨r₀,C,hr₀,hC,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨δ,hδ,hcharts⟩ := hmod μ hμ N hN hp hu
  refine ⟨δ,hδ,?_⟩
  intro c n r e hdata
  dsimp only
  have hchart : ∀ j : ℕ, ∃ ν : Cover → Cover,
      ContinuousOn ν (quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball (c j) (r j/128)) ∧
      (∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball (c j) (r j/128),
        ‖ν a‖ = 1 ∧ ‖n j-ν a‖ ≤ C*e j ∧
        BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a)) ∧
      ∀ i : ℕ, ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball (c j) (r j/128),
        ∀ b ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball (c j) (r j/128),
          dist a b ≤ ρ^i*(r j/2) → dist (ν a) (ν b) ≤ K*e j*(1/2 : ℝ)^i := by
    intro j
    obtain ⟨hc,hn,hr,hrr,he,heδ,hratio,ht⟩ := hdata j
    exact hcharts (c j) hc (n j) (r j) (e j) hn hr hrr he heδ hratio ht
  choose ν hν using hchart
  refine ⟨fun j x ↦ ν j (c j+r j • x),?_,?_,?_⟩
  · intro j
    have hc : Continuous (fun x : Cover ↦ c j+r j • x) := by fun_prop
    exact (hν j).1.comp hc.continuousOn (fun _ hx ↦ hx)
  · intro j x hx
    exact (hν j).2.1 _ hx
  · intro ε hε
    have ht : Tendsto (fun i : ℕ ↦ K*δ*(1/2 : ℝ)^i) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (1/2:ℝ) < 1)).const_mul (K*δ)
    obtain ⟨i,hi⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
    refine ⟨ρ^i/2,by positivity,?_⟩
    intro j x hx y hy hxy
    have hr : 0 < r j := (hdata j).2.2.1
    have hdist : dist (c j+r j • x) (c j+r j • y) ≤ ρ^i*(r j/2) := by
      rw [dist_eq_norm]
      have hab : (c j+r j • x)-(c j+r j • y) = r j • (x-y) := by module
      rw [hab,norm_smul,Real.norm_of_nonneg hr.le,← dist_eq_norm]
      calc
        r j*dist x y ≤ r j*(ρ^i/2) := mul_le_mul_of_nonneg_left hxy.le hr.le
        _ = ρ^i*(r j/2) := by ring
    have hh := (hν j).2.2 i _ hx _ hy hdist
    exact (hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdata j).2.2.2.2.2.1 hK.le) (by positivity))).trans_lt hi

end CubicTorus.MovingCenter

end
end

end

end OAI
