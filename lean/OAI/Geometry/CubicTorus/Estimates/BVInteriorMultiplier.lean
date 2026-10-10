import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVGraphNormalization

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_actual_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
        quotientMap cubeCenter ∈ frontier (openRepresentative E) →
      ∀ (n : ℕ → Cover) (r e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto e atTop (𝓝 0) → Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        bundleOrientedExcess μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hdec⟩ := isMinimizerAt_trapped_sequential_decay hV hE hmin
  obtain ⟨r₁,hr₁,htrap⟩ := isMinimizerAt_trapping_subsequence hV hE hmin
  refine ⟨min r₀ r₁,R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu hc n r e hn hr hrr he hes helim hrel ht θ ε hθ hθR hε
  obtain ⟨ψ,α,hψ,hαlim,hα,hcap⟩ := htrap μ hμ N hN hp hu (quotientMap cubeCenter) hc
    n r e hn hr (fun i ↦ (hrr i).trans (min_le_right _ _)) (fun i ↦ (he i).le) helim ht
  obtain ⟨χ,p,hχ,hsmall⟩ := hdec μ hμ H hH N hN hp hu (n ∘ ψ) (r ∘ ψ) α (e ∘ ψ)
    (fun i ↦ hn (ψ i)) (fun i ↦ hr (ψ i)) (fun i ↦ (hrr (ψ i)).trans (min_le_left _ _))
    (fun i ↦ (hα i).1.le) (fun i ↦ (hα i).2) (fun i ↦ he (ψ i)) (fun i ↦ hes (ψ i))
    hαlim (helim.comp hψ.tendsto_atTop) (hrel.comp hψ.tendsto_atTop) hcap
    (fun i ↦ ht (ψ i)) θ ε hθ hθR hε
  exact ⟨ψ ∘ χ,p,hψ.comp hχ,hsmall⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma spatial_tilt_closedBall_le_oriented {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {s r : ℝ} (hsr : s < r) (hr : r < 1/4) :
    (∫ x in Metric.closedBall (quotientMap cubeCenter) s, ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*bundleOrientedExcess μ n r := by
  have hi : Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsub : {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball cubeCenter r} ⊆ {z | radialSquared z.1 < r^2} := by
    intro z hz
    have hh : ‖(z.1 : Cover)-cubeCenter‖ < r := by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hz
    change radialSquared z.1 < r^2
    rw [(radialSquared_eventuallyEq_norm_sq (hh.trans hr)).eq_of_nhds]
    nlinarith [norm_nonneg ((z.1 : Cover)-cubeCenter)]
  calc
    _ ≤ ∫ x in Metric.ball (quotientMap cubeCenter) r, ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus) :=
      setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
        (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.closedBall_subset_ball hsr).eventuallyLE
    _ = ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball cubeCenter r}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) := integral_polar_tilt_ball hN hp _ _ _
      (Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior (by linarith)))
    _ ≤ ∫ z in {z : NormalBundle | radialSquared z.1 < r^2}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) :=
      setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE
    _ = 2*bundleOrientedExcess μ n r := by
      unfold bundleOrientedExcess
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ by
        dsimp only
        rw [norm_sub_sq_real,z.2.property,hn]
        ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_epsilon_improvement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
        quotientMap cubeCenter ∈ frontier (openRepresentative E) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap cubeCenter) (r*θ/2), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*r^2*e^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hseq⟩ := isMinimizerAt_actual_sequential_decay hV hE hmin
  refine ⟨min r₀ (1/4),R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu hc θ ε hθ hθR hε
  by_contra! hbad
  let d (i : ℕ) : ℝ := min (1/((i:ℝ)+1)) (1/2)
  have hdpos (i) : 0 < d i := by dsimp [d]; positivity
  have hds (i) : d i ≤ 1/2 := min_le_right _ _
  have hdlim : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ (hdpos i).le) (Eventually.of_forall fun i ↦ min_le_left _ _)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (i) := hbad (d i) (hdpos i)
  choose n r e hn hr hrr he hed hrel ht hno using hex
  have helim : Tendsto e atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ (he i).le) (Eventually.of_forall hed) hdlim
  have hrellim : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (hr i).le (sq_nonneg _)) (Eventually.of_forall hrel) hdlim
  obtain ⟨ψ,p,hψ,hdec⟩ := hseq μ hμ H hH N hN hp hu hc n r e hn hr
    (fun i ↦ (hrr i).trans (min_le_left _ _)) he (fun i ↦ (hed i).trans (hds i)) helim hrellim ht θ ε hθ hθR hε
  obtain ⟨i,hi⟩ := hdec.exists
  let ν := graphSlopeNormal (n (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)
  have hν : ‖ν‖ = 1 := graphSlopeNormal_unit (hn _) _
  have hrθ : r (ψ i)*θ < 1/4 := by
    have hrs := (hrr (ψ i)).trans (min_le_right _ _)
    have hθs : θ < 1 := by linarith
    exact (mul_lt_of_lt_one_right (hr _) hθs).trans_le hrs
  have hs := spatial_tilt_closedBall_le_oriented hN hp hu hν (by have hh := hr (ψ i); nlinarith : r (ψ i)*θ/2 < r (ψ i)*θ) hrθ
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2))
  have hnob := hno (ψ i) ν hν
  have heq : 2*((r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε)) = 2*(r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by ring
  rw [heq] at hh
  exact (not_lt_of_ge hh) hnob

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma choose_excess_scale {R K : ℝ} (hR : 0 < R) (hRs : R ≤ 1/8) (hK : 0 ≤ K) :
    ∃ θ ρ ε : ℝ, 0 < θ ∧ 2*θ ≤ R ∧ ρ = θ/34 ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      0 < ε ∧ 2*(K*θ^4+ε) ≤ ρ^2/4 := by
  let θ := min (R/2) (1/(1000000*(K+1)))
  have ht : 0 < θ := by dsimp [θ]; positivity
  have htR : 2*θ ≤ R := by have := min_le_left (R/2) (1/(1000000*(K+1))); dsimp [θ]; linarith
  have hts : θ ≤ 1 := by linarith
  have htK : θ*(K+1) ≤ 1/1000000 := by
    have hh := min_le_right (R/2) (1/(1000000*(K+1)))
    have := (le_div_iff₀ (show 0 < 1000000*(K+1) by positivity)).mp hh
    dsimp [θ]
    nlinarith
  have hKt : K*θ ≤ 1/1000000 := by nlinarith
  have hKtt : K*θ^2 ≤ 1/1000000 := by nlinarith [mul_le_mul_of_nonneg_left hts (mul_nonneg hK ht.le)]
  have hK4 : K*θ^4 ≤ (θ/34)^2/64 := by
    have hh := mul_le_mul_of_nonneg_right hKtt (sq_nonneg θ)
    nlinarith [sq_nonneg θ]
  refine ⟨θ,θ/34,(θ/34)^2/64,ht,htR,rfl,by positivity,by linarith,by positivity,?_⟩
  nlinarith [sq_nonneg (θ/34)]

theorem isMinimizerAt_excess_contraction {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ ρ : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
        quotientMap cubeCenter ∈ frontier (openRepresentative E) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*(ρ*r)), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ*r)^2*(e/2)^2 := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,himp⟩ := isMinimizerAt_epsilon_improvement hV hE hmin
  obtain ⟨θ,ρ,ε,hθ,hθR,hρeq,hρ,hρs,hε,hsmall⟩ := choose_excess_scale hR hRs hK
  refine ⟨r₀,ρ,hr₀,hρ,hρs,?_⟩
  intro μ hμ H hH N hN hp hu hc
  obtain ⟨δ,hδ,hstep⟩ := himp μ hμ H hH N hN hp hu hc θ ε hθ hθR hε
  refine ⟨δ,hδ,?_⟩
  intro n r e hn hr hrr he heδ hrel ht
  obtain ⟨ν,hν,hνt⟩ := hstep n r e hn hr hrr he heδ hrel ht
  refine ⟨ν,hν,?_⟩
  have heq : 17*(ρ*r) = r*θ/2 := by rw [hρeq]; ring
  rw [heq]
  apply hνt.trans
  have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg r) (sq_nonneg e))
  nlinarith only [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_tilt_difference {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n ν : Cover) (S : Set Torus) :
    (spatialNormalMeasure μ : Measure Torus).real S * ‖n-ν‖^2 ≤
      2*(∫ x in S, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) +
      2*(∫ x in S, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) := by
  have hn := (polar_tilt_integrable hN hu n).integrableOn (s := S)
  have hν := (polar_tilt_integrable hN hu ν).integrableOn (s := S)
  have hh : (∫ _ in S, ‖n-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      ∫ x in S, 2*‖N x-n‖^2+2*‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus) := by
    apply integral_mono (integrable_const _) ((hn.const_mul 2).add (hν.const_mul 2))
    intro x
    have hb : ‖n-ν‖ ≤ ‖N x-n‖+‖N x-ν‖ := by
      have hh := norm_add_le (n-N x) (N x-ν)
      rwa [sub_add_sub_cancel,norm_sub_rev n (N x)] at hh
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖N x-n‖-‖N x-ν‖),norm_nonneg (n-ν),norm_nonneg (N x-n),norm_nonneg (N x-ν)]
  simpa only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,
    integral_add (hn.const_mul 2) (hν.const_mul 2),integral_const_mul] using hh

lemma polar_normal_step_bound {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {c ρ r e : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρs : ρ ≤ 1)
    (hr : 0 < r) (he : 0 ≤ e) (n ν : Cover)
    (hm : c*(ρ*r)^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a (ρ*r)))
    (hn : (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (hν : (∫ x in Metric.closedBall a (17*(ρ*r)), ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ*r)^2*(e/2)^2) :
    ‖n-ν‖ ≤ (2/(Real.sqrt c*ρ))*e := by
  have hsub : Metric.closedBall a (17*(ρ*r)) ⊆ Metric.closedBall a (17*r) :=
    Metric.closedBall_subset_closedBall (by nlinarith)
  have hnt : (∫ x in Metric.closedBall a (17*(ρ*r)), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsub.eventuallyLE).trans hn
  have hm' : c*(ρ*r)^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a (17*(ρ*r))) :=
    hm.trans (measureReal_mono (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by nlinarith [mul_pos hρ hr] : ρ*r ≤ 17*(ρ*r)))))
  have hd := (mul_le_mul_of_nonneg_right hm' (sq_nonneg ‖n-ν‖)).trans
    (polar_tilt_difference hN hu n ν (Metric.closedBall a (17*(ρ*r))))
  have ha : c*ρ^2*‖n-ν‖^2 ≤ 4*e^2 := by
    have hpow : (ρ*r)^2*(e/2)^2 ≤ r^2*e^2 := by
      have hh := mul_le_mul_of_nonneg_right hρs (hr.le)
      have hrr : 0 ≤ ρ*r := mul_nonneg hρ.le hr.le
      nlinarith [sq_nonneg (r-ρ*r),sq_nonneg (r+ρ*r),mul_nonneg (sq_nonneg r) (sq_nonneg e),
        mul_nonneg (show 0 ≤ r^2-(ρ*r)^2 by nlinarith) (sq_nonneg e)]
    have hh : (c*ρ^2*‖n-ν‖^2)*r^2 ≤ (4*e^2)*r^2 := by nlinarith only [hd,hnt,hν,hpow]
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp hh
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs2 := Real.sq_sqrt hc.le
  have heq : (2 / (Real.sqrt c*ρ))*e = (2*e)/(Real.sqrt c*ρ) := by ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos hs hρ)).mpr
  have heqsq : (‖n-ν‖*(Real.sqrt c*ρ))^2 = c*ρ^2*‖n-ν‖^2 := by
    rw [mul_pow,mul_pow,hs2]
    ring
  have haa : (‖n-ν‖*(Real.sqrt c*ρ))^2 ≤ (2*e)^2 := by rw [heqsq]; nlinarith only [ha]
  nlinarith [mul_nonneg (norm_nonneg (n-ν)) (mul_pos hs hρ).le]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma dependent_sequence {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
    {x₀ : α} (h₀ : P 0 x₀)
    (hstep : ∀ i x, P i x → ∃ y, P (i+1) y ∧ Q i x y) :
    ∃ f : ℕ → α, f 0 = x₀ ∧ ∀ i, P i (f i) ∧ Q i (f i) (f (i+1)) := by
  classical
  let step (i : ℕ) (x : {x // P i x}) : {x // P (i+1) x} :=
    ⟨Classical.choose (hstep i x x.property), (Classical.choose_spec (hstep i x x.property)).1⟩
  let f (i : ℕ) : {x // P i x} := Nat.rec (motive := fun i ↦ {x // P i x}) ⟨x₀,h₀⟩ step i
  refine ⟨fun i ↦ (f i).val,rfl,?_⟩
  intro i
  exact ⟨(f i).property,(Classical.choose_spec (hstep i (f i) (f i).property)).2⟩

lemma geometric_error_ratio {ρ r e : ℝ} (hρ : 0 < ρ) (hρs : ρ ≤ 1/16)
    (hr : 0 < r) (he : 0 < e) (i : ℕ) :
    (ρ^i*r)/(((1/2:ℝ)^i*e)^2) ≤ r/e^2 := by
  have hscalar : (ρ^i*r)/(((1/2:ℝ)^i*e)^2) = (4*ρ)^i*(r/e^2) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm i 2, pow_mul,
      show (1/2:ℝ)^2 = 1/4 by norm_num]
    calc
      _ = (ρ^i/(1/4:ℝ)^i)*(r/e^2) := by ring
      _ = (ρ/(1/4:ℝ))^i*(r/e^2) := by rw [← div_pow ρ (1/4:ℝ) i]
      _ = _ := by congr 2; ring
  rw [hscalar]
  have hh : (4*ρ)^i ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right hh (div_nonneg hr.le (sq_pos_of_pos he).le)).trans_eq (one_mul _)

lemma excess_normal_iteration (T : Cover → ℝ → ℝ) {r₀ ρ δ C : ℝ}
    (hρ : 0 < ρ) (hρs : ρ ≤ 1/16)
    (hstep : ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
      0 < e → e ≤ δ → r/e^2 ≤ δ → T n r ≤ r^2*e^2 →
      ∃ ν : Cover, ‖ν‖ = 1 ∧ T ν (ρ*r) ≤ (ρ*r)^2*(e/2)^2 ∧ ‖n-ν‖ ≤ C*e)
    {n₀ : Cover} {r e : ℝ} (hn₀ : ‖n₀‖ = 1) (hr : 0 < r) (hrr : r ≤ r₀)
    (he : 0 < e) (heδ : e ≤ δ) (hrel : r/e^2 ≤ δ) (ht : T n₀ r ≤ r^2*e^2) :
    ∃ (n : ℕ → Cover) (ν : Cover), n 0 = n₀ ∧ (∀ i, ‖n i‖ = 1) ∧ ‖ν‖ = 1 ∧
      Tendsto n atTop (𝓝 ν) ∧
      (∀ i, T (n i) (ρ^i*r) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2) ∧
      (∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) := by
  let ri (i : ℕ) := ρ^i*r
  let ei (i : ℕ) := (1/2:ℝ)^i*e
  have hri (i) : 0 < ri i := by dsimp [ri]; positivity
  have hri_le (i) : ri i ≤ r₀ := by
    apply le_trans _ hrr
    have hh : ρ^i ≤ 1 := pow_le_one₀ hρ.le (by linarith)
    exact (mul_le_mul_of_nonneg_right hh hr.le).trans_eq (one_mul _)
  have hei (i) : 0 < ei i := by dsimp [ei]; positivity
  have hei_le (i) : ei i ≤ δ := by
    apply le_trans _ heδ
    have hh : (1/2:ℝ)^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (mul_le_mul_of_nonneg_right hh he.le).trans_eq (one_mul _)
  have hi_rel (i) : ri i/(ei i)^2 ≤ δ := (geometric_error_ratio hρ hρs hr he i).trans hrel
  have hris (i) : ri (i+1) = ρ*ri i := by dsimp [ri]; rw [pow_succ]; ring
  have heis (i) : ei (i+1) = ei i/2 := by dsimp [ei]; rw [pow_succ]; ring
  let P (i : ℕ) (n : Cover) := ‖n‖ = 1 ∧ T n (ri i) ≤ (ri i)^2*(ei i)^2
  let Q (i : ℕ) (n ν : Cover) := ‖n-ν‖ ≤ C*ei i
  have hP₀ : P 0 n₀ := by simpa [P,ri,ei] using And.intro hn₀ ht
  have hPs : ∀ i n, P i n → ∃ ν, P (i+1) ν ∧ Q i n ν := by
    intro i n hn
    obtain ⟨ν,hν,hνt,hchange⟩ := hstep n (ri i) (ei i) hn.1 (hri i) (hri_le i)
      (hei i) (hei_le i) (hi_rel i) hn.2
    exact ⟨ν,⟨hν,by simpa only [hris,heis] using hνt⟩,hchange⟩
  obtain ⟨n,hn0,hn⟩ := dependent_sequence P Q hP₀ hPs
  have hbound (i) : dist (n i) (n (i+1)) ≤ (C*e)*(1/2:ℝ)^i := by
    rw [dist_eq_norm]
    convert (hn i).2 using 1
    dsimp [Q,ei]
    ring
  obtain ⟨ν,hνlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (C*e) (by norm_num) hbound)
  have hν : ‖ν‖ = 1 := by
    have hlim := hνlim.norm
    exact tendsto_nhds_unique hlim (by simpa only [(hn _).1.1] using (tendsto_const_nhds (x := (1:ℝ))))
  refine ⟨n,ν,hn0,fun i ↦ (hn i).1.1,hν,hνlim,fun i ↦ (hn i).1.2,?_⟩
  intro i
  have hh := dist_le_of_le_geometric_of_tendsto (1/2) (C*e) (by norm_num) hbound hνlim i
  rw [dist_eq_norm] at hh
  convert hh using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def interiorWallWeight (x : Cover) : ℝ := ∏ i : Fin 3, wallCutoff i x

lemma interiorWallWeight_smooth : ContDiff ℝ (⊤ : ℕ∞) interiorWallWeight := by
  unfold interiorWallWeight
  apply contDiff_prod
  intro i hi
  exact wallCutoff_contDiff i

lemma interiorWallWeight_nonneg (x : Cover) : 0 ≤ interiorWallWeight x := by
  apply Finset.prod_nonneg
  intro i hi
  dsimp [wallCutoff]
  exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by norm_num)

lemma interiorWallWeight_periodic (n : Fin 3 → ℤ) (x : Cover) :
    interiorWallWeight (x+latticeVector n) = interiorWallWeight x := by
  simp only [interiorWallWeight,wallCutoff_periodic]

lemma interiorWallWeight_face (i : Fin 3) (x : Cover) (hx : x i = 0 ∨ x i = 1) :
    interiorWallWeight x = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (wallCutoff_face i x hx)

lemma interiorWallWeight_center : interiorWallWeight cubeCenter = 1 := by
  have hi (i : Fin 3) : wallCutoff i cubeCenter = 1 := by
    dsimp [wallCutoff,cubeCenter]
    rw [show 2*Real.pi*(1/2) = Real.pi by ring, Real.cos_pi]
    norm_num
  simp [interiorWallWeight,hi]

theorem isMinimizerAt_exists_interior_positive_flux {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ D : WallVariation, 0 < directionalFlux E D.coordinate D.function := by
  obtain ⟨R,c,hR,hcpos,hl⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  have hc' := hc
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at hc'
  have hwnear : ∀ᶠ x in 𝓝 cubeCenter, (1:ℝ)/2 < interiorWallWeight x :=
    (interiorWallWeight_smooth.continuous.continuousAt.tendsto).eventually
      (Ioi_mem_nhds (by rw [interiorWallWeight_center]; norm_num))
  obtain ⟨s,hs,hsw⟩ := Metric.eventually_nhds_iff.mp hwnear
  let r := min (min s R) (1/4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r ≤ s := (min_le_left _ _).trans (min_le_left _ _)
  have hrR : r ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hr4 : r ≤ 1/4 := min_le_right _ _
  let W : C(NormalBundle,ℝ) := ⟨fun z ↦ interiorWallWeight z.1,
    interiorWallWeight_smooth.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hi : Integrable W (μ : Measure NormalBundle) := W.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hIpos : 0 < ∫ z, W z ∂(μ : Measure NormalBundle) := by
    let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball cubeCenter r}
    have hm : 0 < (μ : Measure NormalBundle).real S := by
      change 0 < cellBallMass μ cubeCenter r
      rw [cellBallMass_eq_spatialNormalMeasure μ cubeCenter r
        (Metric.ball_subset_closedBall.trans (cubeCenter_closedBall_interior (by linarith)))]
      exact (mul_pos hcpos (sq_pos_of_pos hr)).trans_le (hl μ hμ _ hc' r hr hrR)
    have hlow : (μ : Measure NormalBundle).real S*(1/2) ≤ ∫ z in S, W z ∂(μ : Measure NormalBundle) := by
      calc
        _ = ∫ _ in S, (1/2:ℝ) ∂(μ : Measure NormalBundle) := by simp
        _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn
          (measurableSet_cellBall _ _) (by
            intro z hz
            exact (hsw ((show dist (z.1 : Cover) cubeCenter < r from hz).trans_le hrs)).le)
    have hglobal : (∫ z in S, W z ∂(μ : Measure NormalBundle)) ≤ ∫ z, W z ∂(μ : Measure NormalBundle) :=
      setIntegral_le_integral hi (Eventually.of_forall fun z ↦ interiorWallWeight_nonneg z.1)
    exact (mul_pos hm (by norm_num)).trans_le (hlow.trans hglobal)
  have hex : ∃ F : Cover → Cover, ∃ hF : AdmissibleField F,
      0 < ∫ z, W z*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    by_contra! hb
    exact (not_le_of_gt hIpos) (normalMeasure_weighted_saturation hμ W hb)
  obtain ⟨F,hF,hflux⟩ := hex
  change 0 < ∫ z, interiorWallWeight z.1*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) at hflux
  rw [normalMeasure_weighted_flux hμ interiorWallWeight_smooth interiorWallWeight_periodic hF] at hflux
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ interiorWallWeight x • F x) := interiorWallWeight_smooth.smul hF.1
  rw [flux_sum_components E hG] at hflux
  have hex : ∃ i : Fin 3, 0 < directionalFlux E i (fun x ↦ (interiorWallWeight x • F x) i) := by
    by_contra! hn
    exact (not_le_of_gt hflux) (Finset.sum_nonpos fun i hi ↦ hn i)
  obtain ⟨i,hi⟩ := hex
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (interiorWallWeight x • F x) i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hG
  obtain ⟨D,hDi,hDf⟩ := exists_wallVariation_of_function i hf
    (by intro n x; rw [interiorWallWeight_periodic,hF.2.1])
    (by intro x hx; rw [interiorWallWeight_face i x hx]; simp)
  exact ⟨D,by simpa only [hDi,hDf] using hi⟩

theorem isMinimizerAt_centered_multiplier {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ, ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function := by
  obtain ⟨D,hD⟩ := isMinimizerAt_exists_interior_positive_flux hV hE hmin hc hμ
  exact isMinimizerAt_exists_coordinate_multiplier hmin hE hμ D hD.ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_tilt_iteration {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ ρ C : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ (n : ℕ → Cover) (ν : Cover), n 0 = n₀ ∧ (∀ i, ‖n i‖ = 1) ∧ ‖ν‖ = 1 ∧
        Tendsto n atTop (𝓝 ν) ∧
        (∀ i, (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*(ρ^i*r)), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2) ∧
        (∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) := by
  obtain ⟨R₀,ρ,hR₀,hρ,hρs,hstep⟩ := isMinimizerAt_excess_contraction hV hE hmin
  obtain ⟨R,c,hR,hcpos,hd⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C := 2/(Real.sqrt c*ρ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min R₀ R,ρ,C,lt_min hR₀ hR,hρ,hρs,hC,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hc hμ
  obtain ⟨δ,hδ,hdec⟩ := hstep μ hμ H hH N hN hp hu hc
  refine ⟨δ,hδ,?_⟩
  intro n₀ r e hn₀ hr hrr he heδ hrel ht
  let T (n : Cover) (r : ℝ) := ∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r),
    ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)
  apply excess_normal_iteration T hρ hρs _ hn₀ hr hrr he heδ hrel ht
  intro n s d hn hs hsR hdpos hdδ hsd hT
  obtain ⟨ν,hν,hνT⟩ := hdec n s d hn hs (hsR.trans (min_le_left _ _)) hdpos hdδ hsd hT
  refine ⟨ν,hν,hνT,?_⟩
  have hc' := hc
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at hc'
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsR : ρ*s ≤ R := (mul_le_of_le_one_left hs.le hρ1).trans (hsR.trans (min_le_right _ _))
  exact polar_normal_step_bound hN hu (quotientMap cubeCenter) hcpos hρ hρ1 hs hdpos.le n ν
    (hd μ hμ _ hc' (ρ*s) (mul_pos hρ hs) hρsR) hT hνT

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

def InteriorCenter := {a : Cover // ‖a-cubeCenter‖ ≤ 1/8}

instance : Coe InteriorCenter Cover := ⟨Subtype.val⟩

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

def cubeBall (c : InteriorCenter) (r : ℝ) : Set Torus := representative ⁻¹' Metric.ball (c : Cover) r

lemma measurableSet_cubeBall (r : ℝ) : MeasurableSet ((cubeBall c) r) :=
  Metric.isOpen_ball.measurableSet.preimage measurable_representative

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 3 / 8) :
    Metric.ball (c : Cover) r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - (c : Cover)‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans_lt hx'
  change ‖x i - (c : Cover) i‖ < r at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

lemma cubeBall_lift {r : ℝ} (hr : r ≤ 3 / 8) :
    fundamentalCube ∩ quotientMap ⁻¹' (cubeBall c) r = Metric.ball (c : Cover) r := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    change representative (quotientMap x) ∈ Metric.ball (c : Cover) r at hball
    rwa [representative_quotientMap_of_mem hx] at hball
  · intro hx
    have hm := coverBall_subset_cube hr hx
    refine ⟨hm, ?_⟩
    change representative (quotientMap x) ∈ Metric.ball (c : Cover) r
    rwa [representative_quotientMap_of_mem hm]

lemma volume_cubeBall {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 3 / 8) :
    torusVolume ((cubeBall c) r) = ENNReal.ofReal (r ^ 3 * (Real.pi * 4 / 3)) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeBall r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeBall r)), inter_comm,
    cubeBall_lift hr1, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ r^3), ENNReal.ofReal_pow hr0]

def radialBump (c : InteriorCenter) : ContDiffBump (c : Cover) where
  rIn := 1 / 4
  rOut := 1 / 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def radialCore (c : InteriorCenter) (x : Cover) : ℝ := (radialBump c) x * (1 - ‖x - (c : Cover)‖ ^ 2)

def radialSquared (c : InteriorCenter) (x : Cover) : ℝ := 1 - latticePeriodize (radialCore c) x

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) (radialCore c) := by
  exact (radialBump c).contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport (radialCore c) :=
  (radialBump c).hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport (radialCore c) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport ((radialBump c) : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [(radialBump c).tsupport_eq] at hs
  have hnorm : ‖x - (c : Cover)‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - (c : Cover)) i).trans hnorm
  change ‖x i - (c : Cover) i‖ ≤ 1 / 3 at hb
  have hc := coords c i
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) (radialSquared c) :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    (radialSquared c) (x + latticeVector n) = (radialSquared c) x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    (radialSquared c) x = 1 - (radialBump c) x * (1 - ‖x - (c : Cover)‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_eventuallyEq_norm_sq {x : Cover} (hx : ‖x - (c : Cover)‖ < 1 / 4) :
    (radialSquared c) =ᶠ[𝓝 x] (fun y ↦ ‖y - (c : Cover)‖ ^ 2) := by
  have hc : x ∈ fundamentalCube := coverBall_subset_cube (by norm_num : (1 / 4 : ℝ) ≤ 3 / 8)
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
  have he := latticePeriodize_eventuallyEq (radialCore_compactSupport (c := c)) radialCore_tsupport
    (fun i ↦ ⟨(hc i).1, (hc i).2.le⟩)
  have hb := (radialBump c).eventuallyEq_one_of_mem_ball
    (show x ∈ Metric.ball (c : Cover) (radialBump c).rIn by
      simpa only [Metric.mem_ball, dist_eq_norm, radialBump] using hx)
  filter_upwards [he, hb] with y hy hby
  simp only [radialSquared, hy, radialCore, hby, Pi.one_apply, one_mul, sub_sub_cancel]

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    (radialSquared c) x < t ↔ ‖x - (c : Cover)‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - (c : Cover))
  have hb0 : 0 ≤ (radialBump c) x := (radialBump c).nonneg
  have hb1 : (radialBump c) x ≤ 1 := (radialBump c).le_one
  have he (h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16) : (radialBump c) x = 1 := by
    apply (radialBump c).one_of_mem_closedBall
    change dist x (c : Cover) ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - (c : Cover)‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - (c : Cover)‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion (radialSquared c) (r ^ 2) = (cubeBall c) r := by
  ext z
  change (radialSquared c) (representative z) < r ^ 2 ↔
    dist (representative z) (c : Cover) < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

lemma norm_gradient_radialSquared_of_mem_cube {x : Cover} (hx : x ∈ fundamentalCube)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (hxt : (radialSquared c) x < r ^ 2) :
    ‖gradient (radialSquared c) x‖ ≤ 2 * r := by
  have hnormsq := (radialSquared_sublevel_iff hx (by nlinarith)).1 hxt
  have hnorm : ‖x - (c : Cover)‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr).mp hnormsq
  rw [norm_gradient_eq_norm_fderiv,
    (radialSquared_eventuallyEq_norm_sq (hnorm.trans_le hsmall)).fderiv_eq]
  have he : (fun y : Cover ↦ ‖y - (c : Cover)‖ ^ 2) =
      (fun y : Cover ↦ ‖y + -(c : Cover)‖ ^ 2) := by simp only [sub_eq_add_neg]
  rw [he]
  have hf : fderiv ℝ (fun y : Cover ↦ ‖y + -(c : Cover)‖ ^ 2) x =
      fderiv ℝ (fun y : Cover ↦ ‖y‖ ^ 2) (x + -(c : Cover)) := by
    convert! fderiv_comp_add_right (𝕜 := ℝ) (f := fun y : Cover ↦ ‖y‖ ^ 2) (x := x) (-(c : Cover)) using 1
  rw [hf, fderiv_norm_sq_apply, two_smul]
  calc
    _ ≤ ‖innerSL ℝ (x + -(c : Cover))‖ + ‖innerSL ℝ (x + -(c : Cover))‖ := norm_add_le _ _
    _ = 2 * ‖x - (c : Cover)‖ := by rw [innerSL_apply_norm]; simp only [sub_eq_add_neg]; ring
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm.le (by norm_num)

lemma norm_gradient_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) (x : Cover)
    (hxt : (radialSquared c) x < r ^ 2) : ‖gradient (radialSquared c) x‖ ≤ 2 * r := by
  have he := periodic_representative (radialSquared_periodic (c := c)) x
  have hg := periodic_representative (f := gradient (radialSquared c))
    (fun n y ↦ gradient_periodic radialSquared_periodic n y) x
  rw [← hg]
  exact norm_gradient_radialSquared_of_mem_cube (representative_mem_fundamentalCube _) hr hsmall (by rwa [he])

lemma cubeBall_eq_metricBall {r : ℝ} (hr : r ≤ 3/8) :
    cubeBall c r = Metric.ball (quotientMap c) r := by
  change representative ⁻¹' Metric.ball (c : Cover) r = _
  rw [← image_quotientMap_eq_preimage_representative (coverBall_subset_cube hr)]
  have he : Metric.ball (c : Cover) r = (fun v : Cover ↦ v+(c : Cover)) '' Metric.ball 0 r := by
    ext x
    constructor
    · intro hx
      exact ⟨x-c, by simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx, sub_add_cancel _ _⟩
    · rintro ⟨v,hv,rfl⟩
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hv
  rw [he, image_image]
  simp_rw [quotientMap_add]
  exact quotientMap_chart_image_ball _ (by linarith)

lemma closedBall_interior {r : ℝ} (hr : r < 3/8) :
    Metric.closedBall (c : Cover) r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-(c : Cover)) i).trans
    (show ‖x-(c : Cover)‖ ≤ r from hx)
  change ‖x i-(c : Cover) i‖ ≤ r at hh
  rw [Real.norm_eq_abs,abs_le] at hh
  have hc := coords c i
  constructor <;> linarith

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma center_add_mem {x : Cover} (hx : ‖x‖ < 3/8) :
    (c : Cover)+x ∈ fundamentalCube := by
  intro i
  have hi := (PiLp.norm_apply_le x i).trans_lt hx
  rw [Real.norm_eq_abs, abs_lt] at hi
  change 0 ≤ (c : Cover) i+x i ∧ (c : Cover) i+x i < 1
  have hc := coords c i
  constructor <;> linarith

lemma torusGraphRegion_symmDiff_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume ((U ∆ torusGraphRegion (c : Cover) n g) ∩
      Metric.ball (quotientMap (c : Cover)) s) ≤
      ∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap (c : Cover)) n r g y) := by
  let D := U ∆ torusGraphRegion (c : Cover) n g
  have hD : MeasurableSet D := hU.symmDiff (measurableSet_torusGraphRegion _ _ hg)
  let f : Cover → ℝ≥0∞ := (Metric.ball (0 : Cover) s).indicator
    (fun x ↦ ENNReal.ofReal (characteristic D (quotientMap x+quotientMap (c : Cover))))
  have hf : Measurable f := (((measurable_characteristic hD).comp
    (measurable_quotientMap.add_const _)).ennreal_ofReal).indicator measurableSet_ball
  have he : torusVolume (D ∩ Metric.ball (quotientMap (c : Cover)) s) = ∫⁻ x, f x := by
    have hm := lintegral_map (μ := volume.restrict (Metric.ball (0 : Cover) s))
      ((measurable_characteristic hD).ennreal_ofReal) (measurable_quotientMap.add_const (quotientMap (c : Cover)))
    rw [torusVolume_chart_map_restrict _ (by linarith : s ≤ 1/2)] at hm
    rw [lintegral_indicator measurableSet_ball]
    rw [← hm]
    have hi : (fun x ↦ ENNReal.ofReal (characteristic D x)) = D.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [characteristic, hx]
    rw [hi, lintegral_indicator hD, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hD]
  rw [he, ← (normalColumnChart_measurePreserving 0 n).lintegral_comp hf]
  have hb (t : ℝ) (y : Plane) : f (normalColumnChart 0 n (t,y)) ≤
      (Metric.ball (0 : Plane) (r/4)).indicator (fun y ↦ (Icc (-r/4) (r/4)).indicator
        (fun t ↦ ENNReal.ofReal |characteristic U
          (quotientMap (c : Cover)+quotientMap (normalPlaneEmbedding n y+t • n))-
            columnPhase (g y) t|) t) y := by
    let x := normalColumnChart (0 : Cover) n (t,y)
    by_cases hx : x ∈ Metric.ball (0 : Cover) s
    · have hxnorm : ‖x‖ < s := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      have ht : |t| ≤ ‖x‖ := by
        have hh := abs_real_inner_le_norm n x
        rw [hn, one_mul] at hh
        have ht0 : ⟪n,x⟫ = t := by simpa only [x, sub_zero] using normalColumnChart_height 0 hn t y
        rwa [ht0] at hh
      have hy : ‖y‖ ≤ ‖x‖ := by
        have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0
        have hy0 : normalPlaneCoordinates n x = y := by
          simpa only [x, sub_zero] using normalColumnChart_projection 0 hn t y
        simpa only [map_zero, hy0, dist_zero_right, one_mul, NNReal.coe_one] using hh
      rw [indicator_of_mem (show y ∈ Metric.ball (0 : Plane) (r/4) by
        simpa only [Metric.mem_ball, dist_zero_right] using hy.trans_lt (hxnorm.trans_le hs))]
      rw [indicator_of_mem (show t ∈ Icc (-r/4) (r/4) by
        have hh := abs_le.mp (ht.trans (hxnorm.le.trans hs)); constructor <;> linarith)]
      dsimp [f]
      rw [indicator_of_mem hx, characteristic_symmDiff_eq_abs]
      have hxc : (c : Cover)+x ∈ fundamentalCube := center_add_mem (by linarith)
      have heq : quotientMap x+quotientMap (c : Cover) = quotientMap ((c : Cover)+x) := by
        rw [quotientMap_add, add_comm]
      rw [heq, characteristic_torusGraphRegion hxc]
      have hc : (c : Cover)+x = normalColumnChart (c : Cover) n (t,y) := by
        simp only [x, normalColumnChart_apply _ hn, zero_add]
      rw [hc, graphSublevelIndicator_column _ hn]
      rw [normalColumnChart_apply _ hn, quotientMap_add]
    · change f x ≤ _
      dsimp [f]
      rw [indicator_of_notMem hx]
      exact zero_le
  calc
    _ ≤ ∫⁻ y : Plane, ∫⁻ t : ℝ, (Metric.ball (0 : Plane) (r/4)).indicator
        (fun y ↦ (Icc (-r/4) (r/4)).indicator
          (fun t ↦ ENNReal.ofReal |characteristic U
            (quotientMap (c : Cover)+quotientMap (normalPlaneEmbedding n y+t • n))-
              columnPhase (g y) t|) t) y := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod_symm (fun p : ℝ × Plane ↦ f (normalColumnChart 0 n p))
        (hf.comp (normalColumnChart 0 n).measurable).aemeasurable]
      exact lintegral_mono fun y ↦ lintegral_mono fun t ↦ hb t y
    _ = _ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Metric.ball (0 : Plane) (r/4)
      · simp only [indicator_of_mem hy]
        rw [lintegral_indicator measurableSet_Icc]
        exact (ofReal_integral_eq_lintegral_ofReal (columnGraphMismatch_integrable hU _ n r g y)
          (Eventually.of_forall fun _ ↦ abs_nonneg _)).symm
      · simp only [indicator_of_notMem hy, lintegral_zero]

end CubicTorus.MovingCenter

end
end

end

end OAI
