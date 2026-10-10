import Mathlib
import OAI.Probability.SKRatio.Quantization.BinPartition
import OAI.Probability.SKRatio.Quantization.IntervalBins

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
  {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  {N : ℕ} {e : Fin N → ℝ}

lemma binT_eq_sqrt {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (σ : Fin n → α) (d : α) : binT σ d=sqrt ((count σ d:ℝ)/(n:ℝ)) := by
  rw [binT,Fintype.card_fin,sqrt_div (Nat.cast_nonneg _)]

lemma intervalBin_roots_empirical (hN : 0<N) (he : StrictMono e)
    (hX : ExponentialEmpiricalConcentration ρ X μ) :
    ExponentialConvergence ρ (fun n ω => binT (fun i => intervalBin e (X n ω i)))
      (massRoot μ (intervalBin e)) := by
  apply ExponentialConvergence.pi_finite
  intro d
  have hh := (intervalBin_empirical hN he hX d).continuous_map continuous_sqrt.continuousAt
  simpa only [binT_eq_sqrt,massRoot,binMass] using hh

lemma intervalBin_binSize_rare (hN : 0<N) (he : StrictMono e)
    (hX : ExponentialEmpiricalConcentration ρ X μ)
    (hm : ∀ d, 0<binMass μ (intervalBin e) d) :
    ExponentiallyRare ρ (fun n => {ω | ∃ d, count (fun i => intervalBin e (X n ω i)) d<2}) := by
  have hd (d : Fin (N+1)) : ExponentiallyRare ρ
      (fun n => {ω | count (fun i => intervalBin e (X n ω i)) d<2}) := by
    let p := binMass μ (intervalBin e) d
    have hp : 0<p := hm d
    apply ((intervalBin_empirical hN he hX d) (p/2) (by positivity)).mono
    have hlarge := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4/p))
    filter_upwards [hlarge,eventually_gt_atTop 0] with n hn hn0
    intro ω hω
    have hc : (count (fun i => intervalBin e (X n ω i)) d:ℝ)≤1 := by
      exact_mod_cast (show count (fun i => intervalBin e (X n ω i)) d≤1 from by simpa using hω)
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    change p/2≤|(count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)-p|
    have hpn := (div_le_iff₀ hp).mp hn
    have hu : (count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)≤p/2 := by
      apply (div_le_iff₀ hnR).mpr
      nlinarith only [hc,hpn]
    have hh := neg_le_abs ((count (fun i => intervalBin e (X n ω i)) d:ℝ)/(n:ℝ)-p)
    linarith only [hu,hh]
  apply (ExponentiallyRare.iUnion_finite hd).mono
  exact .of_forall (fun _ _ ⟨d,hd⟩ => Set.mem_iUnion.mpr ⟨d,hd⟩)

end SKRatio.Bins

end

end OAI
