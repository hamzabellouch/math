import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NoncompactOptimal
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticVariational
import OAI.Geometry.WeakHessian.Calculus.QuadraticCompactness

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile47
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.compact_quadratic_cost_support {K N : ℝ}
    (hcd : CurvatureDimension m K N) (μ ν : ProbabilityMeasure X)
    (hm : (μ:Measure X) ≪ m) (hn : (ν:Measure X) ≪ m)
    (o : X) (R T : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      BoundedTracks (π:Measure (Curve X)) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∃ L : ℝ≥0, LipschitzWith L ψ) ∧
      (∀ x y, y ∈ Metric.closedBall o T → φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) := by
  have hm2 := hasSecondMoment_of_ae_dist_le o R (ae_iff.mpr hsμ)
  have hn2 := hasSecondMoment_of_ae_dist_le o T (ae_iff.mpr hsν)
  obtain ⟨p,hp,hgeo,ho,_⟩ := hcd μ ν inferInstance inferInstance hm2 hn2 hm hn
  let π : ProbabilityMeasure (Curve X) := ⟨p,hp⟩
  have haμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (R:ℝ) ≤ (R+T:ℝ≥0))) hx
  have haν : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (T:ℝ) ≤ (R+T:ℝ≥0))) hx
  have hb : BoundedTracks p := by
    refine ⟨o,3*((R+T:ℝ≥0):ℝ)+1,by positivity,?_⟩
    have H := optimalPlan_supported_tube π hgeo ho.1 (ae_iff.mp haμ) (ae_iff.mp haν)
    filter_upwards [ae_iff.mpr H] with γ hγ
    intro t
    exact (boundedEndpointTube_range hγ t).trans (by linarith)
  obtain ⟨f,g,hf,hg,hd,hc⟩ := bounded_support_kantorovich_potentials
    (isCompact_closedBall o ((R+T:ℝ≥0):ℝ)) (Metric.nonempty_closedBall.mpr (R+T).coe_nonneg)
    (μ:Measure X) (ν:Measure X) haμ haν ho
    (R := 2*(R+T)) (by
      intro x hx y hy
      have H := dist_triangle x o y
      rw [dist_comm o y] at H
      change dist x o ≤ (R+T:ℝ≥0) at hx
      change dist y o ≤ (R+T:ℝ≥0) at hy
      exact H.trans (by exact_mod_cast (by linarith : dist x o+dist y o ≤ 2*((R+T:ℝ≥0):ℝ))))
  have hcp : ∀ᵐ γ ∂p, f (γ timeZero)+g (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 :=
    ae_of_ae_map ((continuous_eval_const timeZero).measurable.prodMk
      (continuous_eval_const timeOne).measurable).aemeasurable hc
  let S := Metric.closedBall o (T:ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := Metric.nonempty_closedBall.mpr T.coe_nonneg
  let f' := compactCTransform S g
  have hq : QuadraticLipschitzBound o T f' := compactCTransform_difference_bound hS hne hg.continuous.continuousOn o (Subset.refl S)
  have hq' : QuadraticLipschitzBound o T (fun x => f' x-f' o) := by
    intro x y
    simpa only [sub_sub_sub_cancel_right] using hq x y
  have hg' : LipschitzWith (2*(R+T)) (fun y => g y+f' o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul x y
  have hsπ : ∀ᵐ γ ∂p, γ timeOne ∈ S := by
    apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS.measurableSet).mp
    change ∀ᵐ x ∂interpolation p timeOne, x ∈ S
    rw [ho.1.interpolation_endpoints.2]
    exact ae_iff.mpr hsν
  refine ⟨π,(fun x => f' x-f' o),(fun y => g y+f' o),hb,ho,hq',sub_self _,⟨_,hg'⟩,?_,?_⟩
  · intro x y hy
    have H := compactCTransform_le hS hne hg.continuous.continuousOn x hy
    dsimp [f']
    linarith
  · filter_upwards [hsπ,hcp] with γ hs hc
    have he := compactCTransform_contact hS hne hg.continuous.continuousOn hd hs hc
    change f' (γ timeZero)-f' o+(g (γ timeOne)+f' o) = _
    change f' (γ timeZero) = _ at he
    rw [he]
    linarith

theorem CurvatureDimension.noncompact_cost_support [SigmaFinite m] {K N : ℝ}
    (hcd : CurvatureDimension m K N)
    (w : X → ℝ) (hw : MemLp w 2 m) (hwm : Measurable w)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (hn : (ν:Measure X) ≪ m) (o : X) (T : ℝ≥0)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw hwm o
  let us (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  have hum (n : ℕ) : Measurable (us n) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  have hu2 (n : ℕ) : MemLp (us n) 2 m := (radial_mul_memLp hw o (n+k)).const_mul (c n)
  let μs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (us n) (hp n)
  have hμs (n : ℕ) : (μs n:Measure X) = squareDensityMeasure m (us n) := rfl
  let R (n : ℕ) : ℝ≥0 := (n+k:ℕ)+1
  have hsμ (n : ℕ) : (μs n:Measure X) (Metric.closedBall o (R n))ᶜ = 0 := by
    apply ae_iff.mp
    apply squareDensity_ae_support (hum n)
    apply ae_of_all
    intro x hx
    have hdn : ((n+k:ℕ):ℝ)+1 ≤ dist x o := by
      have H : ¬dist x o ≤ (R n:ℝ) := hx
      simpa only [R,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using (not_le.mp H).le
    have hz : radialCutoff o (n+k) x = 0 := by
      unfold radialCutoff
      rw [max_eq_left]
      exact sub_nonpos.mpr ((le_div_iff₀ (by positivity : (0:ℝ)<((n+k:ℕ):ℝ)+1)).mpr (by simpa using hdn))
    simp only [us,hz,mul_zero]
  have hμT : Tendsto μs atTop (𝓝 μ) := by
    have H := squareDensity_tendsto_probability hum hwm hu2 hw hp inferInstance (normalized_radial_tendsto hw o k hcT)
    have he : squareDensityProbability m w inferInstance = μ := ProbabilityMeasure.toMeasure_injective hμ.symm
    simpa only [he] using H
  have huW (n : ℕ) : MemLp (fun x => us n x*(dist x o+T)) 2 m := by
    convert ((radial_mul_memLp hwW o (n+k)).const_mul (c n)) using 1
    funext x; dsimp [us]; ring
  have hTV := radial_weighted_density_tendsto hwW o k hcT
  have hex (n : ℕ) := hcd.compact_quadratic_cost_support (μs n) ν
    (withDensity_absolutelyContinuous _ _) hn o (R n) T (hsμ n) hsν
  choose ps fs gs hbps hops hfs hzero hgs hdual hcontact using hex
  have h0 (n : ℕ) := (hops n).1.interpolation_endpoints.1
  have h1 (n : ℕ) := (hops n).1.interpolation_endpoints.2
  have hcf (n : ℕ) := (hfs n).continuous T.coe_nonneg
  have hcg (n : ℕ) := (hgs n).choose_spec.continuous
  have hsb : ∀ᵐ y ∂(ν:Measure X), y ∈ Metric.closedBall o T := ae_iff.mpr hsν
  have hig (n : ℕ) : Integrable (gs n) (ν:Measure X) :=
    LipschitzWith.integrable_supported_ball (hgs n).choose_spec o T hsb
  have hfbd (n : ℕ) : ∀ᵐ x ∂m, |fs n x| ≤ (dist x o+T)^2 :=
    ae_of_all _ fun x => (hfs n).centered_bound T.coe_nonneg (hzero n) x
  obtain ⟨q,hqp,hqo,hqt,hcost⟩ := exists_noncompact_optimal_of_quadratic_contacts hum hwm huW hwW hTV
    μ ν hμ μs hμs hμT ps (fun n => (hbps n).integrable_length_sq) h0 h1 fs gs hcf hcg hig hfbd
    measurableSet_closedBall hsb hdual hcontact
  obtain ⟨φ,s,hs,hφ,hφT,hφU⟩ := exists_quadratic_locally_uniform_subsequence o T fs hfs (by norm_num : (0:ℝ) ≤ 0)
    (fun n => by simp only [hzero n,abs_zero,le_refl])
  have hφo : φ o = 0 := tendsto_nhds_unique (hφT o) (by simpa only [hzero] using (tendsto_const_nhds (x := (0:ℝ))))
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφo,?_⟩
  intro ξ hξ q' hq' hq't
  exact limit_quadratic_transport_support (fun n => hum (s n)) hwm o T (fun n => huW (s n)) hwW
    (hTV.comp hs.tendsto_atTop) μ ν hμ (fun n => ps (s n)) (fun n => (h0 (s n)).trans (hμs (s n)))
    (fun n => h1 (s n)) (fun n => fs (s n)) (fun n => gs (s n)) φ (fun n => hfs (s n)) hφ
    (fun n => hzero (s n)) hφT (fun n => hcg (s n)) (fun n => hig (s n)) measurableSet_closedBall hsb
    (fun n => hdual (s n)) (fun n => hcontact (s n)) (hcost.comp hs.tendsto_atTop) ξ hξ hq' hq't
end WeakHessian

end
end InlinedFile47

end OAI
