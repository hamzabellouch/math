import OAI.Geometry.RCD.Harmonic.HarmonicInteriorRepresentative
import OAI.Geometry.RCD.Metric.CountablePointedCompactness
import OAI.Geometry.RCD.Metric.PointedLimitCompatibility

namespace OAI

/-! # Simultaneous harmonic limits on countably many interior balls

All local limits use the same original subsequence. Full support identifies
the continuous source representatives, so the Euclidean limits agree on
every overlap.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem harmonic_countable_value_limits {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hgradient : LocalHarmonicL2GradientInput hX)
    {S : ℝ} (hS : 0<S) (T : ℕ → ℝ) (hT : ∀ m, 0<T m) (hTS : ∀ m, T m<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*r k^2) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0)) (v : ℕ → X → Euclidean n)
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (S*r k)) (u k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (u k)≤1) :
    ∃ (g : ℕ → Euclidean n → ℝ) (L : ℕ → ℝ≥0) (a : ℕ → ℕ), StrictMono a ∧
      (∀ m, LipschitzWith (L m) (g m)) ∧
      (∀ m η, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict
        (ball (p (a k)) (T m*r (a k))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u (a k)) x-g m (v (a k) x)|<η) ∧
      ∀ i j, EqOn (g i) (g j) (ball 0 (min (T i) (T j))) := by
  let μ := hausdorff n X
  let : μ.IsOpenPosMeasure := hX.openPos K n
  choose C hC hrep using fun m => harmonic_interior_bounded_representative hX hn hmean hgradient
    (sq_nonneg S) (div_pos (hT m) hS) ((div_lt_one hS).mpr (hTS m))
  have hC0 (m : ℕ) : 0≤C m := zero_le_one.trans (hC m)
  have hcurv' (k : ℕ) : -(S^2)≤K*(S*r k)^2 := by
    have hh := mul_le_mul_of_nonneg_left (hcurv k) (sq_nonneg S)
    nlinarith only [hh]
  have hreps (m k : ℕ) : ∃ w : X → ℝ, LipschitzWith (C m/(S*r k)).toNNReal w ∧
      (∀ x, |w x|≤C m) ∧ SobolevSpace.toLp μ hX.quadratic (u k) =ᵐ[
        μ.restrict (ball (p k) (T m*r k))] w := by
    have hh := hrep m (p k) (S*r k) (mul_pos hS (hr k)) (hcurv' k) (u k) (hu k) (hnorm k)
    have hrad : T m/S*(S*r k)=T m*r k := by field_simp
    simpa only [hrad] using hh
  choose w hw hwb hwr using hreps
  let L : ℕ → ℝ≥0 := fun m => ⟨C m/S,div_nonneg (hC0 m) hS.le⟩
  have hl (m k : ℕ) (x z : X) : |w m k x-w m k z|≤(L m:ℝ)*(dist x z/r k) := by
    have hh := (hw m k).dist_le_mul x z
    rw [Real.dist_eq,Real.coe_toNNReal _ (div_nonneg (hC0 m) (mul_pos hS (hr k)).le)] at hh
    change |w m k x-w m k z|≤(C m/S)*(dist x z/r k)
    convert hh using 1; ring
  obtain ⟨g,a,ha,hg⟩ := countable_pointed_function_compactness hS.le p r ε v hr hε hε1 hεlim hv
    w L C (fun m k x _ => hwb m k x) (fun m k x z _ _ => hl m k x z)
  have hsame (i j k : ℕ) : EqOn (w i k) (w j k) (ball (p k) (min (T i) (T j)*r k)) := by
    have hi : ball (p k) (min (T i) (T j)*r k) ⊆ ball (p k) (T i*r k) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_left _ _) (hr k).le)
    have hj : ball (p k) (min (T i) (T j)*r k) ⊆ ball (p k) (T j*r k) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_right _ _) (hr k).le)
    have hij : w i k =ᵐ[μ.restrict (ball (p k) (min (T i) (T j)*r k))] w j k := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hi (hwr i k),
        ae_restrict_of_ae_restrict_of_subset hj (hwr j k)] with x hxi hxj
      exact hxi.symm.trans hxj
    exact Measure.eqOn_open_of_ae_eq hij isOpen_ball
      (hw i k).continuous.continuousOn (hw j k).continuous.continuousOn
  refine ⟨g,L,a,ha,fun m => (hg m).1,?_,?_⟩
  · intro m η hη
    filter_upwards [(hg m).2 η hη] with k hk
    filter_upwards [hwr m (a k),ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    apply hk x
    have hd : dist x (p (a k))<T m*r (a k) := hball
    exact hd.le.trans (mul_le_mul_of_nonneg_right (hTS m).le (hr (a k)).le)
  · intro i j
    exact pointed_limits_eqOn ((min_le_left _ _).trans (hTS i).le)
      (p ∘ a) (r ∘ a) (ε ∘ a) (v ∘ a) (fun k => hr (a k)) (fun k => hε (a k))
      (hεlim.comp ha.tendsto_atTop) (fun k => hv (a k))
      (fun k => w i (a k)) (fun k => w j (a k)) (hg i).1 (hg j).1
      (fun k x hx => hsame i j (a k) hx) (hg i).2 (hg j).2

end RegularPointCoordinates

end

end OAI
