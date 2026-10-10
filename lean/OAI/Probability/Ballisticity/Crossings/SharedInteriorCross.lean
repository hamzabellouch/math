import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridOccupation
import OAI.Probability.Ballisticity.Crossings.FinitePastCrossBound

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_interior_cross_bound {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g)
    (hgb : ∀ z, |g z| ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) (hgzero : ∀ z, |z| ≤ ρ → g z=0) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    |∫ P, jointCrossPastTest F (symmetricClip w) g (P,(v,s,t)) ∂(V : Measure RealPathPair)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*ρ^2/(9*(T*((t:ℝ)-s))))) := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let a := fun i => T*n i
  let H := fun i => ⌊(s:ℝ)*a i⌋₊+1
  let k := fun i => ⌊T*((t:ℝ)-s)*n i⌋₊
  let j := fun i z => ⌊(v z:ℝ)*a i⌋₊
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  have ha : Tendsto a atTop atTop := hn.const_mul_atTop hT
  have he := interiorPastGrid_eventually a ha v s t hv hst.le ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and (hr.1.eventually_gt_atTop 0))
  let u := fun i => i+N
  have hu : Tendsto u atTop atTop := tendsto_add_atTop_nat N
  have hgood (i : ℕ) := (hN (u i) (Nat.le_add_left N i)).1
  have hrpos (i : ℕ) := (hN (u i) (Nat.le_add_left N i)).2
  have hnpos (i : ℕ) : 0 < n (u i) := (mul_pos_iff_of_pos_left hT).mp (hgood i).1
  apply shared_limit_finite_past_cross_bound ν hue e f hef htrans (r ∘ u) hrpos (hr.comp hu) hnpos T hT
    (x ∘ u) (H ∘ u) (fun _ => Nat.succ_pos _) (j ∘ u) (fun i z => (hgood i).2.1 z)
    (fun i => interiorPastGrid (a (u i)) v s t) (v,s,t)
    ((interiorPastGrid_tendsto a ha v s t hst.le).comp hu)
    (μ ∘ u) V (hweak.comp hu) F g hg hgb hρ
    (mul_pos hT (sub_pos.mpr (show (s:ℝ) < t from hst))) hgzero w
  · exact fun i z => (hgood i).2.2.2.1 z
  · exact fun i => (hgood i).2.2.2.2.1
  · intro i
    change a (u i)*(interiorPastGrid (a (u i)) v s t |>.2.2:ℝ) = (H (u i):ℝ)+(k (u i):ℝ)
    have heq : ((t:ℝ)-s)*a (u i)=T*((t:ℝ)-s)*n (u i) := by dsimp [a]; ring
    simpa only [H,k,heq] using (hgood i).2.2.2.2.2
  · exact fun i => hμ (u i)

end DirectionalTransience

end

end

end OAI
