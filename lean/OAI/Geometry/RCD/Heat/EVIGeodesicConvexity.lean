import OAI.Geometry.RCD.Heat.EVIInitialLimit
import OAI.Geometry.RCD.Transport.GeodesicSquareLower

namespace OAI

/-! # Entropy convexity along every geodesic from the actual evolution inequality -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [PseudoMetricSpace Y]

theorem geodesic_convexity_of_integrated_evi {E : Y → ℝ} {z : ℝ → Y} {x y : Y}
    {K θ T : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hT : 0 < T)
    (hz : ContinuousOn z (Icc 0 T)) (hE : ContinuousOn (fun t => E (z t)) (Icc 0 T))
    (hx : dist (z 0) x=θ*dist x y) (hy : dist (z 0) y=(1-θ)*dist x y)
    (hevi0 : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      (dist (z b) x^2-dist (z a) x^2)/2 ≤
        ∫ t in a..b, E x-E (z t)-(K/2)*dist (z t) x^2)
    (hevi1 : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ T →
      (dist (z b) y^2-dist (z a) y^2)/2 ≤
        ∫ t in a..b, E y-E (z t)-(K/2)*dist (z t) y^2) :
    E (z 0) ≤ (1-θ)*E x+θ*E y-(K/2)*θ*(1-θ)*dist x y^2 := by
  let D₀ := fun t => dist (z t) x^2
  let D₁ := fun t => dist (z t) y^2
  let G₀ := fun t => E x-E (z t)-(K/2)*D₀ t
  let G₁ := fun t => E y-E (z t)-(K/2)*D₁ t
  let G := fun t => (1-θ)*G₀ t+θ*G₁ t
  have hD₀ : ContinuousOn D₀ (Icc 0 T) :=
    fun t ht => ((hz t ht).dist continuousWithinAt_const).pow 2
  have hD₁ : ContinuousOn D₁ (Icc 0 T) :=
    fun t ht => ((hz t ht).dist continuousWithinAt_const).pow 2
  have hG₀ : ContinuousOn G₀ (Icc 0 T) :=
    (continuousOn_const.sub hE).sub (continuousOn_const.mul hD₀)
  have hG₁ : ContinuousOn G₁ (Icc 0 T) :=
    (continuousOn_const.sub hE).sub (continuousOn_const.mul hD₁)
  have hG : ContinuousOn G (Icc 0 T) :=
    (continuousOn_const.mul hG₀).add (continuousOn_const.mul hG₁)
  have hmin := weighted_sq_dist_at_geodesic x y (z 0) hx hy
  have hpos : 0 ≤ G 0 := by
    apply nonneg_initial_of_integral_nonneg hT hG
    intro b hb hbT
    have hsub : Icc (0:ℝ) b ⊆ Icc 0 T := Icc_subset_Icc le_rfl hbT
    have h₀ := integrated_inequality_initial_limit hb ((hD₀.div_const 2).mono hsub)
      (hG₀.mono hsub) (fun a ha hab => by
        have hh := hevi0 a b ha hab hbT
        dsimp only [D₀,G₀]
        linarith)
    have h₁ := integrated_inequality_initial_limit hb ((hD₁.div_const 2).mono hsub)
      (hG₁.mono hsub) (fun a ha hab => by
        have hh := hevi1 a b ha hab hbT
        dsimp only [D₁,G₁]
        linarith)
    have hw := weighted_sq_dist_lower x y (z b) hθ0 hθ1
    have hleft : 0 ≤ (1-θ)*(D₀ b/2-D₀ 0/2)+θ*(D₁ b/2-D₁ 0/2) := by
      dsimp only [D₀,D₁]
      nlinarith only [hw,hmin]
    have hi₀ : IntervalIntegrable G₀ volume 0 b := (hG₀.mono hsub).intervalIntegrable_of_Icc hb.le
    have hi₁ : IntervalIntegrable G₁ volume 0 b := (hG₁.mono hsub).intervalIntegrable_of_Icc hb.le
    have hi : (∫ t in 0..b, G t)=
        (1-θ)*(∫ t in 0..b, G₀ t)+θ*(∫ t in 0..b, G₁ t) := by
      rw [show G=(fun t => (1-θ)*G₀ t+θ*G₁ t) from rfl,
        intervalIntegral.integral_add (hi₀.const_mul _) (hi₁.const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    rw [hi]
    have hsum := add_le_add (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hθ1))
      (mul_le_mul_of_nonneg_left h₁ hθ0)
    exact hleft.trans hsum
  dsimp only [G,G₀,G₁,D₀,D₁] at hpos
  have hm := congrArg (fun a : ℝ => (K/2)*a) hmin
  nlinarith only [hpos,hm]

end RegularPointCoordinates

end

end OAI
