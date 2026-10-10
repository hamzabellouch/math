import OAI.Geometry.RCD.Transport.PointedVerticalGeodesic
import OAI.Geometry.RCD.Transport.GeodesicPackingSamples

namespace OAI

/-! # Separated points in an approximate residual factor

Only the source space is geodesic. The residual factor is an arbitrary
metric space; its separated samples are projections of one actual geodesic.
-/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] {n m : ℕ}

theorem pointed_vertical_samples (hgeo : IsGeodesicSpace X)
    {p : X} {z₀ z₁ : Z} {ρ ε : ℝ} (hρ : 0 < ρ) (he : 0 ≤ ε) (hm : 0 < m)
    {f : X → WithLp 2 (Euclidean n × Z)}
    (hf : IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) ρ 1 ε f)
    (hz : dist z₀ z₁ ≤ 1-ε)
    (hsmall : 3*ε/(m:ℝ)+ε+2*Real.sqrt (14*ε*(dist z₀ z₁+7*ε)) ≤
      dist z₀ z₁/(2*m)) :
    ∃ z : Fin m → Z,
      (∀ i, dist (z i) z₀ ≤ dist z₀ z₁+5*ε) ∧
      Pairwise (fun i j => dist z₀ z₁/(2*m) ≤ dist (z i) (z j)) := by
  obtain ⟨x,hx,hfx⟩ := hf.2.2 (WithLp.toLp 2 (0,z₁)) (by
    rw [metric_product_distance_L2]
    simpa only [WithLp.fst,WithLp.snd,dist_self,zero_pow (by norm_num : (2:ℕ)≠0),
      zero_add,Real.sqrt_sq dist_nonneg,dist_comm z₁ z₀] using hz)
  have hx' : dist x p ≤ ρ := by simpa using hx
  obtain ⟨γ,h0,h1,hγ⟩ := hgeo p x
  obtain ⟨hpoints,hhoriz,hnear,hL⟩ := pointed_vertical_geodesic hρ he hf hx' hfx hγ h0 h1
  let z : Fin m → Z := fun i => (f (γ (geodesicSampleTime hm i))).snd
  refine ⟨z,fun i => hnear _,?_⟩
  intro i j hij
  let s := geodesicSampleTime hm i
  let t := geodesicSampleTime hm j
  let E := Real.sqrt (14*ε*(dist z₀ z₁+7*ε))
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hL0 : 0 ≤ dist p x/ρ := div_nonneg dist_nonneg hρ.le
  have hsource : dist p x/ρ/(m:ℝ) ≤ dist (γ s) (γ t)/ρ := by
    rw [hγ s t,h0,h1]
    have hh := mul_le_mul_of_nonneg_right (geodesicSampleTime_gap hm hij) hL0
    dsimp only [s,t]
    convert hh using 1 <;> ring
  have hfull := (abs_le.mp (hf.2.1 (γ s) (γ t)
    (by simpa using hpoints s) (by simpa using hpoints t))).1
  have hprod : dist (f (γ s)) (f (γ t)) ≤
      dist (f (γ s)).fst (f (γ t)).fst+dist (z i) (z j) := by
    rw [metric_product_distance_L2]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · change dist (f (γ s)).fst (f (γ t)).fst^2+dist (z i) (z j)^2 ≤ _
      nlinarith [dist_nonneg (x := (f (γ s)).fst) (y := (f (γ t)).fst),
        dist_nonneg (x := z i) (y := z j)]
  have hhor : dist (f (γ s)).fst (f (γ t)).fst ≤ 2*E := by
    have ht := dist_triangle (f (γ s)).fst 0 (f (γ t)).fst
    rw [dist_zero_right,dist_zero_left] at ht
    linarith [hhoriz s,hhoriz t]
  have hLm : (dist z₀ z₁-3*ε)/(m:ℝ) ≤ dist p x/ρ/(m:ℝ) :=
    div_le_div_of_nonneg_right hL hm'.le
  have heq : (dist z₀ z₁-3*ε)/(m:ℝ) =
      2*(dist z₀ z₁/(2*m))-3*ε/(m:ℝ) := by field_simp
  rw [heq] at hLm
  dsimp only [E] at hhor
  linarith

end RegularPointCoordinates

end

end OAI
