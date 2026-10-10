import OAI.Geometry.RCD.Coordinates.HarmonicCoordinateGram
import OAI.Geometry.RCD.Harmonic.FirstOrderFromScaledFamily

namespace OAI

/-! # The actual first-order splitting maps along a measured Euclidean sequence -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.initial_splitting_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 16 (ε k) (V k)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∀ β : ℝ, 0<β → ∀ᶠ k in atTop,
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic (p (α k)) (2*r (α k)) β u v := by
  obtain ⟨α,hα,w,hV₀,hw,hnorm,hconv⟩ := hX.finite_measured_harmonic_sequence hn
    p r ε V hr hcurv hε hε1 hεlim hV
  let η := fun k : ℕ => 1/((k:ℝ)+1)
  have hη : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hη0 (k : ℕ) : 0≤η k := by dsimp only [η]; positivity
  have hη1 (k : ℕ) : η k≤1 := by
    dsimp only [η]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hsmall (k : ℕ) {t : ℝ} (ht : 0≤t) (ht16 : t≤16) : -1≤K*(t*r (α k))^2 := by
    by_cases hK : 0≤K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · exact (hcurv (α k)).trans (mul_le_mul_of_nonpos_left
        (pow_le_pow_left₀ (mul_nonneg ht (hr (α k)).le)
          (mul_le_mul_of_nonneg_right ht16 (hr (α k)).le) 2) (le_of_not_ge hK))
  have hc1 (k : ℕ) : -1≤K*(r (α k))^2 := by
    simpa using hsmall k (t:=1) (by norm_num) (by norm_num)
  have hc5 (k : ℕ) : -1≤K*(5*r (α k))^2 := hsmall k (by norm_num) (by norm_num)
  obtain ⟨hgrad,hgram⟩ := hX.harmonic_coordinate_gram hn (p∘α) (r∘α) η (V∘α)
    (fun k => hr (α k)) hc1 hc5 hη0 hη1 hη hV₀ w hw hnorm hconv
  refine ⟨α,hα,?_⟩
  intro β hβ
  have hgrad' : ∀ᶠ k in atTop, ∀ i : Fin n,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (3*r (α k))),
        r (α k)^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w i k) x≤1+β :=
    eventually_all.mpr (fun i => hgrad i β hβ)
  have hgram' : ∀ᶠ k in atTop, ∀ i j : Fin n,
      ((hausdorff n X).real (ball (p (α k)) (2*r (α k))))⁻¹*
        (∫ x in ball (p (α k)) (2*r (α k)),
          |r (α k)^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w j k) x-(if i=j then 1 else 0)|
          ∂hausdorff n X)≤β := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    exact ((hgram i j).eventually (eventually_lt_nhds hβ)).mono (fun _ h => h.le)
  filter_upwards [hgrad',hgram'] with k hg hm
  exact hX.first_order_splitting_of_scaled_family hn (p (α k)) (hr (α k)) hβ (hc5 k)
    (fun i => w i k) (fun i => hw i k) (fun i => hnorm i k) hg hm

end RegularPointCoordinates

end

end OAI
