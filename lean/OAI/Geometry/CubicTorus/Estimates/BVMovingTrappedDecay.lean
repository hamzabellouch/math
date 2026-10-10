import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVMovingOrientedReplacement

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapped_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,Q,R,D,M,C,hr₀,hQ,hR,hRs,hD,hM,hC,hRQ,hg⟩ :=
    isMinimizerAt_trapped_harmonic_graphs hV hE hmin
  refine ⟨min r₀ (1/4),R,32*C*M,by positivity,hR,hRs,by positivity,?_⟩
  intro μ hμ H hH N hN hp hu c n r α e hn hr hrr hα0 hα he hes hαlim helim hrel htrap htilt θ ε hθ hθR hε
  obtain ⟨m,g,ψ,u,hψ,huS,hdata,hconv,huE⟩ :=
    hg μ hμ H hH N hN hp hu c n r α e hn hr (fun i ↦ (hrr i).trans (min_le_left _ _)) hα0 hα he hes hαlim helim hrel htrap htilt
  let f i := graphNormalize (r i) (e i) (m i) (g i)
  have hf (i) : ContDiff ℝ (⊤ : ℕ∞) (f i) := graphNormalize_contDiff (hdata i).1 _ _ _
  let p := fderiv ℝ u 0
  let A := 2*D+2*‖p‖^2*(volume : Measure Plane).real (Metric.ball 0 (2*θ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henergy (i) : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A :=
    graph_relative_energy_bound (hf i) ((Metric.ball_subset_ball hθR).trans hRQ) (hdata i).2.2.2.2.1 p
  have hmlim : Tendsto m atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hαlim
    exact Eventually.of_forall fun i ↦ (hdata i).2.2.2.1
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hh := hrel.mul (helim.pow 2)
    simpa only [div_mul_cancel₀ _ (pow_ne_zero 2 (he _).ne'), zero_pow (by norm_num : 2 ≠ 0),mul_zero] using hh
  let B i := D*α i+e i*(volume : Measure Plane).real (Metric.ball 0 (1/4))+e i
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      ((hαlim.const_mul D).add (helim.mul_const ((volume : Measure Plane).real (Metric.ball 0 (1/4))))).add helim
  have hUE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμU := hμ.congr_ae hUE.symm
  have hminU := (isMinimizerAt_congr_ae hUE).mpr hmin
  have hmismatch (i) : sublevelVolume
      ((openRepresentative E) ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
      (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i := by
    rw [show graphRescale (r i) (e i) (m i) (f i) = g i from graphRescale_normalize (hr i).ne' (he i).ne' _ _]
    have hsmall : r i*(2*θ) ≤ 1/4 := by
      have hri := (hrr i).trans (min_le_right _ _)
      nlinarith [mul_le_mul_of_nonneg_left (hθR.trans hRs) (hr i).le]
    unfold sublevelVolume
    rw [sublevelRegion_radialSquared (mul_nonneg (hr i).le (by positivity)) hsmall,cubeBall_eq_metricBall (by linarith : r i*(2*θ) ≤ 3/8)]
    apply ((hdata i).2.2.2.2.2.2 _ ?_).trans_lt
    · dsimp [B]
      nlinarith [mul_pos (pow_pos (hr i) 3) (pow_pos (he i) 3)]
    · calc
        _ ≤ r i*(1/4) := mul_le_mul_of_nonneg_left ((hθR.trans hRs).trans (by norm_num)) (hr i).le
        _ = _ := by ring
  have hconv' := strongL2_restrict_ball (fun i ↦ (hf (ψ i)).continuous) huS.continuous hθR hconv
  obtain ⟨χ,hχ,hdec⟩ := isMinimizerAt_sequential_oriented_decay hV
    (isOpen_openRepresentative E).measurableSet hminU hμU
    (c ∘ ψ) (r ∘ ψ) (e ∘ ψ) (m ∘ ψ) (α ∘ ψ) (B ∘ ψ) (n ∘ ψ) (f ∘ ψ)
    (fun i ↦ hr (ψ i)) (fun i ↦ he (ψ i)) (fun i ↦ hn (ψ i)) (fun i ↦ hf (ψ i))
    (hrlim.comp hψ.tendsto_atTop) (helim.comp hψ.tendsto_atTop)
    (hmlim.comp hψ.tendsto_atTop) (hαlim.comp hψ.tendsto_atTop) (hBlim.comp hψ.tendsto_atTop)
    (hrel.comp hψ.tendsto_atTop) hθ huS p hA (fun i ↦ henergy (ψ i)) (huE (2*θ) (by positivity)) hconv'
    (fun i y _ ↦ graphNormalize_height (hr (ψ i)) (he (ψ i)).ne' _ ((hdata (ψ i)).2.2.1) y)
    (fun i ↦ hmismatch (ψ i)) hε
  refine ⟨ψ ∘ χ,p,hψ.comp hχ,?_⟩
  have heq : 2*(C*M*(2*θ)^4)+ε = 32*C*M*θ^4+ε := by ring
  simpa only [Function.comp_def,heq] using hdec

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapping_subsequence {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
      (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
      (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ c : ℕ → Torus, (∀ i, c i ∈ frontier (openRepresentative E)) → ∀ (n : ℕ → Cover) (r e : ℕ → ℝ),
      (∀ i, ‖n i‖ = 1) → (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
      (∀ i, 0 ≤ e i) → Tendsto e atTop (𝓝 0) →
      (∀ i, (∫ x in Metric.closedBall (c i) (17*r i), ‖N x-n i‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∃ (ψ : ℕ → ℕ) (α : ℕ → ℝ), StrictMono ψ ∧ Tendsto α atTop (𝓝 0) ∧
        (∀ i, 0 < α i ∧ α i < 1/4) ∧
        ∀ i, normalCap (c (ψ i)) (n (ψ i)) (r (ψ i)) (α i*r (ψ i)) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (c (ψ i)) (-(n (ψ i))) (r (ψ i)) (α i*r (ψ i)) ⊆ openRepresentative E := by
  obtain ⟨R,δ,hR,hδ,htrap⟩ := isMinimizerAt_quantitative_trapping hV hE hmin
  obtain ⟨S,A,hS,hA,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  refine ⟨min R (S/16),by positivity,?_⟩
  intro μ hμ N hN hp hu c hc n r e hn hr hrr he helim ht
  let o i := normalOscillation (spatialNormalMeasure μ) N (c i) (n i) (8*r i)
  have hob (i) : o i ≤ (A+1)*e i :=
    oscillation_le_scaled_tilt hN hu (hn i) (c i) (hr i) (he i) hA.le
      (harea μ hμ (c i) (16*r i) (by have hh := hr i; positivity) (by have hh := (hrr i).trans (min_le_right _ _); linarith)) (ht i)
  have holim : Tendsto o atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (integral_nonneg fun x ↦ norm_nonneg _) (sq_nonneg _))
      (Eventually.of_forall hob)
    simpa only [mul_zero] using helim.const_mul (A+1)
  let α (i : ℕ) : ℝ := 1/((i:ℝ)+8)
  have hα (i) : 0 < α i ∧ α i < 1/4 := by
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
    dsimp [α]
    constructor
    · positivity
    · rw [div_lt_iff₀ (by positivity : 0 < (i:ℝ)+8)]
      linarith
  have hαlim : Tendsto α atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 8).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hevent (i) : ∀ᶠ j in atTop, 131072*o j < δ^2*(α i/4)^6 :=
    (show Tendsto (fun j ↦ 131072*o j) atTop (𝓝 0) from by simpa only [mul_zero] using holim.const_mul 131072).eventually
      (gt_mem_nhds (by have hh := (hα i).1; positivity))
  obtain ⟨ψ,hψ,hsmall⟩ := diagonal_strictMono hevent
  refine ⟨ψ,α,hψ,hαlim,hα,fun i ↦ ?_⟩
  exact htrap μ hμ N hN hp hu (c (ψ i)) (hc (ψ i)) (n (ψ i)) (hn _) (r (ψ i)) (α i)
    (hr _) ((hrr _).trans (min_le_left _ _)) (hα i).1 (hα i).2.le (hsmall i)

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_actual_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter), (∀ i, quotientMap (c i : Cover) ∈ frontier (openRepresentative E)) →
      ∀ (n : ℕ → Cover) (r e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto e atTop (𝓝 0) → Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hdec⟩ := isMinimizerAt_trapped_sequential_decay hV hE hmin
  obtain ⟨r₁,hr₁,htrap⟩ := isMinimizerAt_trapping_subsequence hV hE hmin
  refine ⟨min r₀ r₁,R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu c hc n r e hn hr hrr he hes helim hrel ht θ ε hθ hθR hε
  obtain ⟨ψ,α,hψ,hαlim,hα,hcap⟩ := htrap μ hμ N hN hp hu (fun i ↦ quotientMap (c i : Cover)) hc
    n r e hn hr (fun i ↦ (hrr i).trans (min_le_right _ _)) (fun i ↦ (he i).le) helim ht
  obtain ⟨χ,p,hχ,hsmall⟩ := hdec μ hμ H hH N hN hp hu (c ∘ ψ) (n ∘ ψ) (r ∘ ψ) α (e ∘ ψ)
    (fun i ↦ hn (ψ i)) (fun i ↦ hr (ψ i)) (fun i ↦ (hrr (ψ i)).trans (min_le_left _ _))
    (fun i ↦ (hα i).1.le) (fun i ↦ (hα i).2) (fun i ↦ he (ψ i)) (fun i ↦ hes (ψ i))
    hαlim (helim.comp hψ.tendsto_atTop) (hrel.comp hψ.tendsto_atTop) hcap
    (fun i ↦ ht (ψ i)) θ ε hθ hθR hε
  exact ⟨ψ ∘ χ,p,hψ.comp hχ,hsmall⟩

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

lemma spatial_tilt_closedBall_le_oriented {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {s r : ℝ} (hsr : s < r) (hr : r < 1/4) :
    (∫ x in Metric.closedBall (quotientMap (c : Cover)) s, ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*(bundleOrientedExcess c) μ n r := by
  have hi : Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ ‖(z.2 : Cover)-n‖^2) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsub : {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball (c : Cover) r} ⊆ {z | (radialSquared c) z.1 < r^2} := by
    intro z hz
    have hh : ‖(z.1 : Cover)-(c : Cover)‖ < r := by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hz
    change (radialSquared c) z.1 < r^2
    rw [(radialSquared_eventuallyEq_norm_sq (hh.trans hr)).eq_of_nhds]
    nlinarith [norm_nonneg ((z.1 : Cover)-(c : Cover))]
  calc
    _ ≤ ∫ x in Metric.ball (quotientMap (c : Cover)) r, ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus) :=
      setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
        (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.closedBall_subset_ball hsr).eventuallyLE
    _ = ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball (c : Cover) r}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) := integral_polar_tilt_ball hN hp _ _ _
      (Metric.ball_subset_closedBall.trans (closedBall_interior (by linarith)))
    _ ≤ ∫ z in {z : NormalBundle | (radialSquared c) z.1 < r^2}, ‖(z.2 : Cover)-n‖^2
        ∂(μ : Measure NormalBundle) :=
      setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE
    _ = 2*(bundleOrientedExcess c) μ n r := by
      unfold bundleOrientedExcess
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ by
        dsimp only
        rw [norm_sub_sq_real,z.2.property,hn]
        ring

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_epsilon_improvement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : InteriorCenter, quotientMap (c : Cover) ∈ frontier (openRepresentative E) → ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap (c : Cover)) (r*θ/2), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ 2*r^2*e^2*(K*θ^4+ε) := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,hseq⟩ := isMinimizerAt_actual_sequential_decay hV hE hmin
  refine ⟨min r₀ (1/4),R,K,by positivity,hR,hRs,hK,?_⟩
  intro μ hμ H hH N hN hp hu θ ε hθ hθR hε
  by_contra! hbad
  let d (i : ℕ) : ℝ := min (1/((i:ℝ)+1)) (1/2)
  have hdpos (i) : 0 < d i := by dsimp [d]; positivity
  have hds (i) : d i ≤ 1/2 := min_le_right _ _
  have hdlim : Tendsto d atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i ↦ (hdpos i).le) (Eventually.of_forall fun i ↦ min_le_left _ _)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (i) := hbad (d i) (hdpos i)
  choose c hc n r e hn hr hrr he hed hrel ht hno using hex
  have helim : Tendsto e atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ (he i).le) (Eventually.of_forall hed) hdlim
  have hrellim : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i ↦ div_nonneg (hr i).le (sq_nonneg _)) (Eventually.of_forall hrel) hdlim
  obtain ⟨ψ,p,hψ,hdec⟩ := hseq μ hμ H hH N hN hp hu c hc n r e hn hr
    (fun i ↦ (hrr i).trans (min_le_left _ _)) he (fun i ↦ (hed i).trans (hds i)) helim hrellim ht θ ε hθ hθR hε
  obtain ⟨i,hi⟩ := hdec.exists
  let ν := graphSlopeNormal (n (ψ i)) (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)
  have hν : ‖ν‖ = 1 := graphSlopeNormal_unit (hn _) _
  have hrθ : r (ψ i)*θ < 1/4 := by
    have hrs := (hrr (ψ i)).trans (min_le_right _ _)
    have hθs : θ < 1 := by linarith
    exact (mul_lt_of_lt_one_right (hr _) hθs).trans_le hrs
  have hs := spatial_tilt_closedBall_le_oriented (c:=c (ψ i)) hN hp hu hν (by have hh := hr (ψ i); nlinarith : r (ψ i)*θ/2 < r (ψ i)*θ) hrθ
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2))
  have hnob := hno (ψ i) ν hν
  have heq : 2*((r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε)) = 2*(r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by ring
  rw [heq] at hh
  exact (not_lt_of_ge hh) hnob

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_excess_contraction {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ ρ : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ c : InteriorCenter, quotientMap (c : Cover) ∈ frontier (openRepresentative E) → ∀ (n : Cover) (r e : ℝ), ‖n‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
        ∃ ν : Cover, ‖ν‖ = 1 ∧
          (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*(ρ*r)), ‖N x-ν‖^2
            ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ*r)^2*(e/2)^2 := by
  obtain ⟨r₀,R,K,hr₀,hR,hRs,hK,himp⟩ := isMinimizerAt_epsilon_improvement hV hE hmin
  obtain ⟨θ,ρ,ε,hθ,hθR,hρeq,hρ,hρs,hε,hsmall⟩ := choose_excess_scale hR hRs hK
  refine ⟨r₀,ρ,hr₀,hρ,hρs,?_⟩
  intro μ hμ H hH N hN hp hu
  obtain ⟨δ,hδ,hstep⟩ := himp μ hμ H hH N hN hp hu θ ε hθ hθR hε
  refine ⟨δ,hδ,?_⟩
  intro c hc n r e hn hr hrr he heδ hrel ht
  obtain ⟨ν,hν,hνt⟩ := hstep c hc n r e hn hr hrr he heδ hrel ht
  refine ⟨ν,hν,?_⟩
  have heq : 17*(ρ*r) = r*θ/2 := by rw [hρeq]; ring
  rw [heq]
  apply hνt.trans
  have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg r) (sq_nonneg e))
  nlinarith only [hh]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_uniform_tilt_iteration {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ ρ C : ℝ, 0 < r₀ ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : InteriorCenter,
        quotientMap (a : Cover) ∈ frontier (openRepresentative E) →
      ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖ = 1 → 0 < r → r ≤ r₀ →
        0 < e → e ≤ δ → r/e^2 ≤ δ →
        (∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ (n : ℕ → Cover) (ν : Cover), n 0 = n₀ ∧ (∀ i, ‖n i‖ = 1) ∧ ‖ν‖ = 1 ∧
        Tendsto n atTop (𝓝 ν) ∧
        (∀ i, (∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*(ρ^i*r)), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2) ∧
        (∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) := by
  obtain ⟨R₀,ρ,hR₀,hρ,hρs,hstep⟩ := isMinimizerAt_excess_contraction hV hE hmin
  obtain ⟨R,c,hR,hcpos,hd⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let C := 2/(Real.sqrt c*ρ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min R₀ R,ρ,C,lt_min hR₀ hR,hρ,hρs,hC,?_⟩
  intro μ hμ N hN hp hu
  obtain ⟨H,hH⟩ := isMinimizerAt_centered_multiplier hV hE hmin hc hμ
  obtain ⟨δ,hδ,hdec⟩ := hstep μ hμ H hH N hN hp hu
  refine ⟨δ,hδ,?_⟩
  intro a ha n₀ r e hn₀ hr hrr he heδ hrel ht
  let T (n : Cover) (r : ℝ) := ∫ x in Metric.closedBall (quotientMap (a : Cover)) (17*r),
    ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)
  apply excess_normal_iteration T hρ hρs _ hn₀ hr hrr he heδ hrel ht
  intro n s d hn hs hsR hdpos hdδ hsd hT
  obtain ⟨ν,hν,hνT⟩ := hdec a ha n s d hn hs (hsR.trans (min_le_left _ _)) hdpos hdδ hsd hT
  refine ⟨ν,hν,hνT,?_⟩
  have ha' := ha
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmin] at ha'
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsR : ρ*s ≤ R := (mul_le_of_le_one_left hs.le hρ1).trans (hsR.trans (min_le_right _ _))
  exact polar_normal_step_bound hN hu (quotientMap (a : Cover)) hcpos hρ hρ1 hs hdpos.le n ν
    (hd μ hμ _ ha' (ρ*s) (mul_pos hρ hs) hρsR) hT hνT

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_tilt_triangle {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n ν : Cover) (S : Set Torus) :
    (∫ x in S, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      2*(∫ x in S, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) +
      2*(spatialNormalMeasure μ : Measure Torus).real S*‖n-ν‖^2 := by
  have hn := (polar_tilt_integrable hN hu n).integrableOn (s := S)
  have hν := (polar_tilt_integrable hN hu ν).integrableOn (s := S)
  calc
    _ ≤ ∫ x in S, 2*‖N x-n‖^2+2*‖n-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus) := by
      apply integral_mono hν ((hn.const_mul 2).add (integrable_const _))
      intro x
      have hb : ‖N x-ν‖ ≤ ‖N x-n‖+‖n-ν‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (N x-n) (n-ν)
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖N x-n‖-‖n-ν‖), norm_nonneg (N x-ν),
        norm_nonneg (N x-n), norm_nonneg (n-ν)]
    _ = _ := by rw [integral_add (hn.const_mul 2) (integrable_const _),integral_const_mul,
                    integral_const,smul_eq_mul,measureReal_restrict_apply_univ]; ring

lemma iterated_tilt_limit_excess {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) (ν : Cover)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i)
    {s : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ∃ i : ℕ, ρ^(i+1)*r < s ∧ s ≤ ρ^i*r ∧
      normalExcess (spatialNormalMeasure μ) N a ν s ≤
        (2/ρ^2+8*A*C^2)*e^2*(1/2:ℝ)^(2*i) := by
  obtain ⟨i,hi,hsi⟩ := exists_nat_pow_near_of_lt_one (div_pos hs hr)
    ((div_le_one hr).2 hsr) hρ hρ1
  have hi' : ρ^(i+1)*r < s := (lt_div_iff₀ hr).mp hi
  have hsi' : s ≤ ρ^i*r := (div_le_iff₀ hr).mp hsi
  refine ⟨i,hi',hsi',?_⟩
  have hri : 0 < ρ^i*r := mul_pos (pow_pos hρ _) hr
  have hsub : Metric.closedBall a s ⊆ Metric.closedBall a (17*(ρ^i*r)) :=
    Metric.closedBall_subset_closedBall (by linarith)
  have htn : (∫ x in Metric.closedBall a s, ‖N x-n i‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤
      (ρ^i*r)^2*((1/2:ℝ)^i*e)^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu (n i)).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsub.eventuallyLE).trans (ht i)
  have hbound : 0 ≤ 2*C*e*(1/2:ℝ)^i :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) he) (by positivity)
  have hcn : ‖n i-ν‖^2 ≤ (2*C*e*(1/2:ℝ)^i)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hbound).mpr (hc i)
  have htν := polar_tilt_triangle hN hu (n i) ν (Metric.closedBall a s)
  have hmass := mul_le_mul_of_nonneg_right (hm s hs hsr) (sq_nonneg ‖n i-ν‖)
  have hmass' := mul_le_mul_of_nonneg_left hcn (show 0 ≤ A*s^2 by positivity)
  have hrad : (ρ^i*r)^2 ≤ s^2/ρ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hρ)).2
    rw [pow_succ] at hi'
    have hh : ρ*(ρ^i*r) < s := by nlinarith only [hi']
    have hh2 := pow_le_pow_left₀ (mul_pos hρ hri).le hh.le 2
    nlinarith only [hh2]
  have hrad' := mul_le_mul_of_nonneg_right hrad (sq_nonneg ((1/2:ℝ)^i*e))
  rw [normalExcess]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  have heq : 2*(s^2/ρ^2)*((1/2:ℝ)^i*e)^2 + 2*(A*s^2)*(2*C*e*(1/2:ℝ)^i)^2 =
      ((2/ρ^2+8*A*C^2)*e^2*(1/2:ℝ)^(2*i))*s^2 := by
    rw [Nat.mul_comm 2 i, pow_mul]
    ring
  rw [← heq]
  nlinarith only [htν,htn,hmass,hmass',hrad']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma iterated_tilt_limit_oscillation {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) {ν : Cover} (hν : ‖ν‖ = 1)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i)
    {s : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    normalOscillation (spatialNormalMeasure μ) N a ν s ^2 ≤
      A*(2/ρ^2+8*A*C^2)*e^2 := by
  obtain ⟨i,hi,hsi,hexc⟩ := iterated_tilt_limit_excess hN hu a hρ hρ1 hr he hA hC n ν hm ht hc hs hsr
  have hq : (1/2:ℝ)^(2*i) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hK : 0 ≤ (2/ρ^2+8*A*C^2)*e^2 := by positivity
  have hbound := hexc.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hK)
  have hh := (normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hu hν a hs (hm s hs hsr)).trans
    (mul_le_mul_of_nonneg_left hbound hA)
  nlinarith only [hh]

lemma iterated_tilt_boundary_cone {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {D d : ℝ} (hdpos : 0 < d)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ D →
      d*t^3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      d*t^3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    {a : Torus} (ha : a ∈ B) {ρ r e A C R ε : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hr : 0 < r) (he : 0 ≤ e)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) {ν : Cover} (hν : ‖ν‖ = 1)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i)
    (hRsmall : R ≤ 1/32) (hRD : 2*R ≤ D) (hRr : 16*R ≤ r)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : (131072:ℝ)^2*A*(2/ρ^2+8*A*C^2)*e^2 < (d^2*(ε/8)^6)^2) :
    ∀ y ∈ B, dist y a ≤ R → |⟪ν, shortestLift (y-a)⟫| ≤ ε*dist y a := by
  apply good_scales_boundary_cone hE hμ hN hp hu hdpos hd ha hν hRsmall hRD hε hε1
  intro s hs hsR
  have ho := iterated_tilt_limit_oscillation hN hu a hρ hρ1 hr he hA hC n hν hm ht hc hs
    (hsR.trans hRr)
  have hh := mul_le_mul_of_nonneg_left ho (by norm_num : (0:ℝ) ≤ 131072^2)
  have htpos : 0 < d^2*(ε/8)^6 := by positivity
  have hnosc := normalOscillation_nonneg (spatialNormalMeasure μ) N a ν s
  nlinarith only [hh,hsmall,htpos,hnosc]

lemma cone_change_normal {B : Set Torus} {a : Torus} {ν n : Cover} {R ε η : ℝ}
    (hcone : ∀ y ∈ B, dist y a ≤ R → |⟪ν, shortestLift (y-a)⟫| ≤ ε*dist y a)
    (hn : ‖n-ν‖ ≤ η) :
    ∀ y ∈ B, dist y a ≤ R → |⟪n, shortestLift (y-a)⟫| ≤ (ε+η)*dist y a := by
  intro y hy hyr
  have hh := abs_real_inner_le_norm (n-ν) (shortestLift (y-a))
  rw [norm_shortestLift, ← dist_eq_norm y a] at hh
  have hd := mul_le_mul_of_nonneg_right hn (dist_nonneg : 0 ≤ dist y a)
  have hi : ⟪n, shortestLift (y-a)⟫ = ⟪ν, shortestLift (y-a)⟫ + ⟪n-ν, shortestLift (y-a)⟫ := by
    rw [inner_sub_left]; ring
  rw [hi]
  have habs := abs_add_le ⟪ν, shortestLift (y-a)⟫ ⟪n-ν, shortestLift (y-a)⟫
  nlinarith only [habs,hh,hd,hcone y hy hyr]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma iterated_tilt_limit_excess_tendsto {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) (ν : Cover)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) :
    Tendsto (normalExcess (spatialNormalMeasure μ) N a ν) (𝓝[>] 0) (𝓝 0) := by
  let K := (2/ρ^2+8*A*C^2)*e^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : Tendsto (fun i : ℕ ↦ K*(1/2:ℝ)^(2*i)) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)).const_mul K
    simpa only [pow_mul, show (1/2:ℝ)^2 = 1/4 by norm_num, mul_zero] using hh
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [] with s
    exact hb.trans_le (div_nonneg (integral_nonneg fun x ↦ sq_nonneg _) (sq_nonneg s))
  · intro b hb
    obtain ⟨j,hj⟩ := (hq.eventually (Iio_mem_nhds hb)).exists
    have hjpos : 0 < ρ^(j+1)*r := by positivity
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hjpos)] with s hs hsrj
    have hspos : 0 < s := hs
    have hsr : s ≤ r := (show s < ρ^(j+1)*r from hsrj).le.trans
      (mul_le_of_le_one_left hr.le (pow_le_one₀ hρ.le hρ1.le))
    obtain ⟨i,hi,hsi,hexc⟩ := iterated_tilt_limit_excess hN hu a hρ hρ1 hr he hA hC n ν hm ht hc hspos hsr
    have hji : j ≤ i := by
      by_contra! hij
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one hρ.le hρ1.le (Nat.succ_le_succ hij.le)) hr.le
      exact (not_lt_of_ge hh) (hi.trans (show s < ρ^(j+1)*r from hsrj))
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
        (Nat.mul_le_mul_left 2 hji)) hK
    exact (hexc.trans hh).trans_lt hj

lemma iterated_tilt_limit_oscillation_tendsto {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {ρ r e A C : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (he : 0 ≤ e) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (n : ℕ → Cover) {ν : Cover} (hν : ‖ν‖ = 1)
    (hm : ∀ s : ℝ, 0 < s → s ≤ r →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a s) ≤ A*s^2)
    (ht : ∀ i, (∫ x in Metric.closedBall a (17*(ρ^i*r)), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (ρ^i*r)^2*((1/2:ℝ)^i*e)^2)
    (hc : ∀ i, ‖n i-ν‖ ≤ 2*C*e*(1/2:ℝ)^i) :
    Tendsto (normalOscillation (spatialNormalMeasure μ) N a ν) (𝓝[>] 0) (𝓝 0) := by
  have htend := iterated_tilt_limit_excess_tendsto hN hu a hρ hρ1 hr he hA hC n ν hm ht hc
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0,
      normalOscillation (spatialNormalMeasure μ) N a ν s ≤
        Real.sqrt (A*normalExcess (spatialNormalMeasure μ) N a ν s) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with s hs hsr
    have hh := normalOscillation_sq_le_excess (spatialNormalMeasure μ) hN hu hν a hs (hm s hs hsr.le)
    have hnex : 0 ≤ A*normalExcess (spatialNormalMeasure μ) N a ν s :=
      mul_nonneg hA (div_nonneg (integral_nonneg fun x ↦ sq_nonneg _) (sq_nonneg s))
    have hsqrt := Real.sq_sqrt hnex
    have hsnon := Real.sqrt_nonneg (A*normalExcess (spatialNormalMeasure μ) N a ν s)
    nlinarith only [hh,hsqrt,hsnon]
  apply squeeze_zero' (Eventually.of_forall fun s ↦ normalOscillation_nonneg _ _ _ _ _) hb
  simpa only [mul_zero,Real.sqrt_zero] using (htend.const_mul A).sqrt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma polar_normal_nearby_centers {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a b : Torus) {c r e : ℝ} (hc : 0 < c) (hr : 0 < r) (he : 0 ≤ e)
    (ha : c*r^2 ≤ (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r))
    (hab : dist a b ≤ r) (ν ω : Cover)
    (htν : (∫ x in Metric.closedBall a (2*r), ‖N x-ν‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (htω : (∫ x in Metric.closedBall b (2*r), ‖N x-ω‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2) :
    ‖ν-ω‖ ≤ (2/Real.sqrt c)*e := by
  have hsuba : Metric.ball a r ⊆ Metric.closedBall a (2*r) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hsubb : Metric.ball a r ⊆ Metric.closedBall b (2*r) := by
    intro x hx
    have hx' : dist x a < r := hx
    change dist x b ≤ 2*r
    linarith [dist_triangle x a b]
  have hν : (∫ x in Metric.ball a r, ‖N x-ν‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu ν).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsuba.eventuallyLE).trans htν
  have hω : (∫ x in Metric.ball a r, ‖N x-ω‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu ω).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) hsubb.eventuallyLE).trans htω
  have hd := (mul_le_mul_of_nonneg_right ha (sq_nonneg ‖ν-ω‖)).trans
    (polar_tilt_difference hN hu ν ω (Metric.ball a r))
  have hh : c*‖ν-ω‖^2 ≤ 4*e^2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp
    nlinarith only [hd,hν,hω]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hs2 := Real.sq_sqrt hc.le
  have heq : (2/Real.sqrt c)*e = (2*e)/Real.sqrt c := by ring
  rw [heq]
  apply (le_div_iff₀ hs).2
  have hsquared : (‖ν-ω‖*Real.sqrt c)^2 ≤ (2*e)^2 := by
    rw [mul_pow,hs2]
    nlinarith only [hh]
  nlinarith [mul_nonneg (norm_nonneg (ν-ω)) hs.le]

lemma continuousOn_of_uniform_normal_tilt {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (S : Set Cover) (ν : Cover → Cover) {c : ℝ} (hc : 0 < c)
    (r e : ℕ → ℝ) (hr : ∀ i, 0 < r i) (he : ∀ i, 0 ≤ e i)
    (helim : Tendsto e atTop (𝓝 0))
    (hm : ∀ a ∈ S, ∀ i, c*(r i)^2 ≤
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) (r i)))
    (ht : ∀ a ∈ S, ∀ i, (∫ x in Metric.closedBall (quotientMap a) (2*r i), ‖N x-ν a‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) :
    ContinuousOn ν S := by
  rw [Metric.continuousOn_iff]
  intro a ha ε hε
  have hl : Tendsto (fun i ↦ (2/Real.sqrt c)*e i) atTop (𝓝 0) := by
    simpa only [mul_zero] using helim.const_mul (2/Real.sqrt c)
  obtain ⟨i,hi⟩ := (hl.eventually (Iio_mem_nhds hε)).exists
  refine ⟨r i,hr i,?_⟩
  intro b hb hba
  have hdist : dist (quotientMap a) (quotientMap b) ≤ r i := by
    rw [dist_eq_norm, ← quotientMap_sub]
    apply (norm_quotientMap_le _).trans
    rw [← dist_eq_norm,dist_comm]
    exact hba.le
  have hh := polar_normal_nearby_centers hN hu (quotientMap a) (quotientMap b) hc (hr i) (he i)
    (hm a ha i) hdist (ν a) (ν b) (ht a ha i) (ht b hb i)
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt hi

lemma polar_tilt_limit_two_radius {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (a : Torus) {r e A C : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (n ν : Cover)
    (hm : (spatialNormalMeasure μ : Measure Torus).real (Metric.closedBall a (2*r)) ≤ 16*A*r^2)
    (ht : (∫ x in Metric.closedBall a (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (hc : ‖n-ν‖ ≤ 2*C*e) :
    (∫ x in Metric.closedBall a (2*r), ‖N x-ν‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (2+128*A*C^2)*r^2*e^2 := by
  have htn : (∫ x in Metric.closedBall a (2*r), ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
    (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
    (Eventually.of_forall fun x ↦ sq_nonneg _) (Metric.closedBall_subset_closedBall
      (by linarith : 2*r ≤ 17*r)).eventuallyLE).trans ht
  have hcn := pow_le_pow_left₀ (norm_nonneg _) hc 2
  have hmass := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖n-ν‖)
  have hmass' := mul_le_mul_of_nonneg_left hcn (show 0 ≤ 16*A*r^2 by positivity)
  have hh := polar_tilt_triangle hN hu n ν (Metric.closedBall a (2*r))
  nlinarith only [htn,hmass,hmass',hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_normal_field {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E)) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 < C ∧
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
        ∀ a ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          ‖ν a‖ = 1 ∧ ‖n₀-ν a‖ ≤ C*e ∧
          BoundaryFlatAt (frontier (openRepresentative E)) (quotientMap a) (ν a) := by
  classical
  obtain ⟨R₀,ρ,C,hR₀,hρ,hρs,hC,hiter⟩ := isMinimizerAt_uniform_tilt_iteration hV hE hmin hcenter
  obtain ⟨U,A,hU,hA,hupper⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨L,c,hL,hc,hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  obtain ⟨D,d,hD,hd,hdensity⟩ := isMinimizerAt_two_sided_density hV hE hmin
  let r₀ := min R₀ (min (U/2) (min L (1/8)))
  refine ⟨r₀,4*C,by dsimp [r₀]; positivity,by positivity,?_⟩
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
  let M := 2+128*A*C^2
  have hM : 0 < M := by dsimp [M]; positivity
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
    have ht' : (∫ z in Metric.closedBall (quotientMap (a' : Cover)) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 :=
      (setIntegral_mono_set (polar_tilt_integrable hN hu n₀).integrableOn
      (Eventually.of_forall fun z ↦ sq_nonneg _) hsub.eventuallyLE).trans htilt
    have ht'' : (∫ z in Metric.closedBall (quotientMap (a' : Cover)) (17*(r/2)), ‖N z-n₀‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r/2)^2*(2*e)^2 := by
      nlinarith only [ht']
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
        convert hclose i using 1
        ring
      have hh := polar_tilt_limit_two_radius hN hu (quotientMap a) hi hA.le (n i) ν hm (ht i) hci
      rw [mul_pow (Real.sqrt M),Real.sq_sqrt hM.le]
      dsimp [M] at *
      nlinarith only [hh]
  choose ν hν using hdata
  refine ⟨ν,?_,fun a ha ↦ ⟨(hν a ha).1,(hν a ha).2.1,(hν a ha).2.2.1⟩⟩
  apply continuousOn_of_uniform_normal_tilt hN hu S ν hc
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

end CubicTorus.MovingCenter

end
end

end

end OAI
