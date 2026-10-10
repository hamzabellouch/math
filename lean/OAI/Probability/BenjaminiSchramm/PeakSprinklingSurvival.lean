import OAI.Probability.BenjaminiSchramm.PeakSprinklingAverage
import OAI.Probability.BenjaminiSchramm.PeakCostBound
import OAI.Probability.BenjaminiSchramm.WeightedCostRetention

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peak_sprinkling_eventual_survival
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (O : G.OrbitRepresentatives) (p q b : unitInterval)
    (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hgb : ∀ l, g l ≤ C₀) (hglim : Tendsto g atTop (𝓝 0))
    (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (c rate A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hsurv : ∀ n : ℕ, 0 < n → ENNReal.ofReal (c*Real.exp (-rate*n)) ≤
      G.peakSurvivalProbability O a R q n)
    (hprofile : ∀ n : ℕ, 0 < n → ∀ l : ℕ, G.peakSurvivalLayerMoment O a R q n l ≤
      G.peakSurvivalProbability O a R q n *
        ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((c/2)*Real.exp (-(rate+ε)*n)) ≤
      G.fullPeakDownProbability O a p (R*n) := by
  let Ev (n : ℕ) (x : V) : Set (Set E) :=
    {ω | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x}
  let Z (x : V) (ω : Set E) := G.downwardLayerCost a R g ω x
  let F (n : ℕ) := C*(∑' l, g l*Real.exp (-A*max ((l : ℝ)-n) 0))
  have hEv (n : ℕ) (x : V) : MeasurableSet (Ev n x) :=
    measurableSet_lt measurable_const (G.measurable_peakDownBandCount a _ _ x)
  have hZ (x : V) : Measurable (Z x) := G.measurable_downwardLayerCost a R g x
  have hP (n : ℕ) : G.peakSurvivalProbability O a R q n < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact ENNReal.sum_ne_top.mpr fun x _ => ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hF : Tendsto (fun n : ℕ => F n/(n : ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := C) (f := atTop)).mul
      (exponential_continuation_cost_sublinear g C₀ A hg hC₀ hgb hA hglim)
    simpa only [F,div_eq_mul_inv,mul_assoc,mul_zero] using hh
  filter_upwards [sublinear_cost_eventually_small F hF (ε/2) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : 0 < n := by omega
  have htn : 0 < ε*(n : ℝ) := mul_pos hε (Nat.cast_pos.mpr hn0)
  have hcost : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω in Ev n x, Z x ω ∂G.law q)) ≤
      G.peakSurvivalProbability O a R q n*ENNReal.ofReal (F n) := by
    calc
      _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, (Ev n x).indicator (Z x) ω ∂G.law q) := by
        apply Finset.sum_congr rfl
        intro x _
        exact congrArg (fun z => ENNReal.ofReal (a x)*z) (lintegral_indicator (hEv n x) (Z x)).symm
      _ ≤ _ := G.peakSurvivalCostMoment_bound O a R q g hg C₀ hC₀ hgb A C hA hC n (hprofile n hn0)
  have hcost' := hcost.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
    (show F n ≤ ε*(n : ℝ)/2 by nlinarith [hn])))
  have hhalf := weighted_cost_retains_half O.roots (fun _ : V => G.law q)
    (fun x => ENNReal.ofReal (a x)) (Ev n) (fun x _ => hEv n x) Z (fun x _ => hZ x)
    (ε*n) htn (hP n) hcost'
  let B (x : V) := Ev n x ∩ {ω | Z x ω ≤ ENNReal.ofReal (ε*n)}
  have hB (x : V) : MeasurableSet (B x) := (hEv n x).inter (measurableSet_le (hZ x) measurable_const)
  have hBpeak (x : V) : B x ⊆ G.fullPeakDownHit a (R*n) x := by
    apply Set.Subset.trans Set.inter_subset_left
    exact G.positive_peakDownBandCount_subset_fullPeakDownHit hc hl a _ _ (R*n) (by nlinarith [hR]) x
  have htransfer := G.weighted_peak_sprinkling_average O q b p hparam a R hR (R*n)
    g hg (ε*n) htn.le hfin havoid B hB hBpeak (fun _ _ h => h.2)
  apply retained_peak_exponential_bound _ _ _ c rate ε n (hsurv n hn0) hhalf
  simpa only [B,neg_mul] using htransfer

end CriticalPercolation.BondGraph

end

end OAI
