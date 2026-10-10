import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.LipschitzMulDist
import OAI.Geometry.WeakHessian.Calculus.TendstoIntegralBoundedPairing
import OAI.Geometry.WeakHessian.Entropy.StrongEntropyConfinement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology NNReal ENNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_entropy_hopf {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    {b : ℝ} (hb : 0 < b) (f : X →ᵇ ℝ) {J : ℝ≥0} (hf : LipschitzWith J f) :
    (∫ x,cheegerHeat h b u x*boundedHopfMap f b x ∂m)-(∫ x,u x*f x ∂m) ≤
      ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))/2 := by
  let ts : ℕ → ℝ := fun n => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))
  have hpos (n : ℕ) : 0 < ts n := by dsimp only [ts]; positivity
  have hlim : Tendsto ts atTop (𝓝 0) := by
    have H : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))/(2*((L:ℝ)^2+1))) atTop (𝓝 ((0:ℝ)/(2*((L:ℝ)^2+1)))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2*((L:ℝ)^2+1))
    simpa only [zero_div] using H
  have hsmall (n : ℕ) : ts n*(L:ℝ)^2 ≤ 1/2 := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hden : 0 < 2*((L:ℝ)^2+1) := by positivity
    have h1 : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp only [ts]
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    have H := mul_le_mul_of_nonneg_right h1 (sq_nonneg (L:ℝ))
    nlinarith
  exact hcd.cheegerHeat_entropy_hopf_resolvents hN hfull hfin o h u hun hi hV hU hdecay hD hw hhalf hhalfi
    hpos hsmall hlim hb f hf

lemma CurvatureDimension.cheegerHeat_entropy_transport_localized {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    {b : ℝ} (hb : 0 < b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (cheegerHeat h b u) ∧ q.map Prod.snd = densityMeasure m u ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal
        (b*((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))) := by
  have hi := integrable_of_integral_eq_one hmass
  let := densityMeasure_probability_of_integrable u hun hi hmass
  let := hcd.cheegerHeat_probability hN hfull hfin o h u hun hmass hb.le
  apply exists_proper_coupling_cost_of_hopf_bound
  intro f hf
  obtain ⟨J,hf⟩ := hf
  let g : X →ᵇ ℝ := (1/b) • f
  have hg : LipschitzWith (‖(1/b)‖₊*J) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((1/b)*f x) ((1/b)*f y) ≤ _
    rw [dist_eq_norm,← mul_sub,norm_mul]
    simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (norm_nonneg (1/b))
  have H := hcd.cheegerHeat_entropy_hopf hN hfull hfin o h u hun hi hV hU hdecay hD hw hhalf hhalfi hb g hg
  have heq (x : X) : b*boundedHopfMap g b x = hopfLax f 1 x := by
    rw [boundedHopfMap_apply_pos g hb]
    exact hopfLax_scale_time f hb x
  rw [integral_densityMeasure m _ (cheegerHeat_nonneg h hb.le u hun),integral_densityMeasure m _ hun]
  calc
    (∫ x,cheegerHeat h b u x*hopfLax f 1 x ∂m)-(∫ x,u x*f x ∂m) =
      b*((∫ x,cheegerHeat h b u x*boundedHopfMap g b x ∂m)-(∫ x,u x*g x ∂m)) := by
        rw [mul_sub,← integral_const_mul,← integral_const_mul]
        congr 1
        · apply integral_congr_ae
          exact ae_of_all _ fun x => by dsimp only; rw [← heq]; ring
        · apply integral_congr_ae
          exact ae_of_all _ fun x => by
            simp only [g,BoundedContinuousFunction.smul_apply,smul_eq_mul]
            field_simp
    _ ≤ b*(((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))/2) :=
      mul_le_mul_of_nonneg_left H hb.le
    _ = _ := by ring

lemma CurvatureDimension.cheegerHeat_entropy_transport_supported {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {R : ℝ} (hR : ∀ᵐ x ∂m,R ≤ dist x o → u x = 0)
    {b : ℝ} (hb : 0 < b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (cheegerHeat h b u) ∧ q.map Prod.snd = densityMeasure m u ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ ENNReal.ofReal
        (b*((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (cheegerHeat h b u x) ∂m))) := by
  obtain ⟨a,ha,hw,hdecay,hD,hhalf,hhalfi⟩ := hcd.exists_strong_entropy_confinement hN hfull hfin o
  exact hcd.cheegerHeat_entropy_transport_localized hN hfull hfin o h u hun hmass
    (lipschitz_mul_dist o a) (memLp_exp_dist_of_support u ha.le o hR) hdecay hD hw hhalf hhalfi hb
end WeakHessian

end
end InlinedFile0

end OAI
