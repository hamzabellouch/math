import Mathlib
import OAI.Geometry.WeakHessian.Entropy.RadialEntropy
import OAI.Geometry.WeakHessian.Entropy.QuadraticEntropyPairing
import OAI.Geometry.WeakHessian.Calculus.NoncompactOptimal
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticVariational
import OAI.Geometry.WeakHessian.Sobolev.RadialGradientBound
import OAI.Geometry.WeakHessian.Calculus.QuadraticCompactness

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile41
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m]

theorem RCD.noncompact_entropy_subdifferential {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (hEnt : FiniteEntropy m (μ:Measure X))
    (o : X) (T : ℝ≥0) (hT : 0 < T)
    (hwW : MemLp (fun x => w x*(dist x o+T)) 2 m)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ q : Measure (X×X), ∃ φ : X → ℝ,
      IsProbabilityMeasure q ∧ IsOptimalCoupling q μ ν ∧ QuadraticTransportCost q ≠ ∞ ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∀ ξ : ProbabilityMeasure X, Integrable (fun x => (dist x o+T)^2) (ξ:Measure X) →
        ∀ q' : Measure (X×X), IsCoupling q' ξ ν → QuadraticTransportCost q' ≠ ∞ →
        (QuadraticTransportCost q).toReal-(QuadraticTransportCost q').toReal ≤
          2*((∫ x,φ x ∂(μ:Measure X))-(∫ x,φ x ∂(ξ:Measure X)))) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*(QuadraticTransportCost q).toReal ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  obtain ⟨k,c,hc,hcT,hp⟩ := radial_probability_normalization hw.1 hwm o
  let us (n : ℕ) (x : X) := c n*(w x*radialCutoff o (n+k) x)
  have hum (n : ℕ) : Measurable (us n) :=
    (hwm.mul (radialCutoff_lipschitz o (n+k)).continuous.measurable).const_mul _
  have hu2 (n : ℕ) : MemLp (us n) 2 m := (radial_mul_memLp hw.1 o (n+k)).const_mul (c n)
  have hcn (n : ℕ) : 0 ≤ c n := (hc n).1.le
  obtain ⟨hus,hstrong⟩ := hrcd.1.normalized_radial_root_strong hfin hrcd.2 hw o k hcn hcT
  have hus' (n : ℕ) : Sobolev m (us n) := hus n
  obtain ⟨M,hM⟩ := normalized_radial_gradient_bounded hfin hw o k hcn hcT hus
  have hU (n : ℕ) : ∀ᵐ x ∂m, 0 ≤ us n x ∧ us n x ≤ 2*B := by
    filter_upwards [hwn,hwB] with x hx hxb
    refine ⟨mul_nonneg (hcn n) (mul_nonneg hx (radialCutoff_nonneg o (n+k) x)),?_⟩
    have H : w x*radialCutoff o (n+k) x ≤ B := (mul_le_of_le_one_right hx (radialCutoff_le_one o (n+k) x)).trans hxb
    exact (mul_le_mul_of_nonneg_left H (hcn n)).trans (mul_le_mul_of_nonneg_right (hc n).2 hB)
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
    have H := squareDensity_tendsto_probability hum hwm hu2 hw.1 hp inferInstance (normalized_radial_tendsto hw.1 o k hcT)
    have he : squareDensityProbability m w inferInstance = μ := ProbabilityMeasure.toMeasure_injective hμ.symm
    simpa only [he] using H
  have heT := normalized_radial_entropy_tendsto hw.1 hwm (hμ ▸ hEnt) o k
    (fun n => ⟨hcn n,(hc n).2⟩) hcT hp
  have huW (n : ℕ) : MemLp (fun x => us n x*(dist x o+T)) 2 m := by
    convert ((radial_mul_memLp hwW o (n+k)).const_mul (c n)) using 1
    funext x; dsimp [us]; ring
  obtain ⟨hdW,hWT⟩ := normalized_radial_weighted_tendsto hwW o k hcT
  have hTV := radial_weighted_density_tendsto hwW o k hcT
  have hex (n : ℕ) := hrcd.compact_quadratic_entropy_subgradient hN hfin (us n) (hus' n) (hum n)
    (by positivity : 0 ≤ 2*B) ((hU n).mono fun _ hx => hx.1) ((hU n).mono fun _ hx => hx.2)
    (μs n) ν (hμs n) o (R n) T hT (hsμ n) hsν hCt hdν
  choose ps fs gs hbps hops hfs hzero hgs hdual hcontact hent using hex
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
  refine ⟨q,φ,hqp,hqo,hqt,hφ,hφo,?_,?_⟩
  · intro ξ hξ q' hq' hq't
    exact limit_quadratic_transport_support (fun n => hum (s n)) hwm o T (fun n => huW (s n)) hwW
      (hTV.comp hs.tendsto_atTop) μ ν hμ (fun n => ps (s n)) (fun n => (h0 (s n)).trans (hμs (s n)))
      (fun n => h1 (s n)) (fun n => fs (s n)) (fun n => gs (s n)) φ (fun n => hfs (s n)) hφ
      (fun n => hzero (s n)) hφT (fun n => hcg (s n)) (fun n => hig (s n)) measurableSet_closedBall hsb
      (fun n => hdual (s n)) (fun n => hcontact (s n)) (hcost.comp hs.tendsto_atTop) ξ hξ hq' hq't
  · have hpair := hrcd.1.quadratic_entropy_pairing_tendsto hfin hrcd.2 o hT
      (fun n => hfs (s n)) hφ (by norm_num : (0:ℝ) ≤ 0)
      (fun n => by simp only [hzero,abs_zero,le_refl]) (by simp only [hφo,abs_zero,le_refl]) hφT hw
      (hwn.and hwB |>.mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2) hwW
      (fun n => hus' (s n)) (fun n => huW (s n)) (fun n => hdW (s n))
      (hWT.comp hs.tendsto_atTop) (hstrong.comp hs.tendsto_atTop) (fun n => hM (s n))
    have hEntT : Tendsto (fun n => entropyReal m (μs (s n):Measure X)) atTop (𝓝 (entropyReal m (μ:Measure X))) := by
      rw [hμ]
      exact heT.2.comp hs.tendsto_atTop
    exact le_of_tendsto_of_tendsto' ((hEntT.sub_const _).add ((hcost.comp hs.tendsto_atTop).const_mul (K/2)))
      hpair (fun n => hent (s n))
end WeakHessian

end
end InlinedFile41

end OAI
