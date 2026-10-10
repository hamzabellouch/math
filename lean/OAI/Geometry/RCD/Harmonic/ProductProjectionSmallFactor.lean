import OAI.Geometry.RCD.Harmonic.ResidualCollapse

namespace OAI

/-! # Projecting a product approximation with a small residual fiber -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

private theorem product_dist_le_sum {A Z : Type*} [MetricSpace A] [MetricSpace Z]
    (x y : WithLp 2 (A × Z)) :
    dist x y ≤ dist x.fst y.fst+dist x.snd y.snd := by
  rw [metric_product_distance_L2]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [dist_nonneg (x := x.fst) (y := y.fst),
      dist_nonneg (x := x.snd) (y := y.snd)]

/-- A small residual fiber suffices for a coordinate approximation on a
fixed inner ball. The larger source ball is retained for target density. -/
theorem product_projection_small_factor {X Z : Type*} [MetricSpace X] [MetricSpace Z]
    {n : ℕ} {p : X} {z₀ : Z} {r ε a : ℝ} (hr : 0 < r) (he : 0 ≤ ε)
    (he16 : ε ≤ 1/16) (ha : 0 ≤ a)
    {f : X → WithLp 2 (Euclidean n × Z)}
    (hf : IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) r 1 ε f)
    (hsmall : ∀ z : Z, dist z₀ z ≤ 1/4 → dist z₀ z ≤ a) :
    IsPointedApproximation p 0 r (1/16) (3*ε+2*a) (fun x => (f x).fst) := by
  have hpp : dist p p ≤ 1*r := by simpa using hr.le
  have hlarge {x : X} (hx : dist x p ≤ 1/16*r) : dist x p ≤ 1*r := by linarith
  have hzbound {x : X} (hx : dist x p ≤ 1/16*r) : dist (f x).snd z₀ ≤ a := by
    have hd := (abs_le.mp (hf.2.1 x p (hlarge hx) hpp)).2
    have ht := dist_triangle (f x) (f p) (WithLp.toLp 2 (0,z₀))
    have hp := WithLp.dist_snd_le (f x) (WithLp.toLp 2 (0,z₀))
    change dist (f x).snd z₀ ≤ _ at hp
    have hxq : dist x p/r ≤ 1/16 := (div_le_iff₀ hr).mpr hx
    have hh : dist z₀ (f x).snd ≤ 1/4 := by rw [dist_comm]; linarith [hf.1]
    simpa only [dist_comm z₀] using hsmall (f x).snd hh
  refine ⟨(WithLp.dist_fst_le (f p) (WithLp.toLp 2 (0,z₀))).trans
    (hf.1.trans (by linarith)),?_,?_⟩
  · intro x y hx hy
    have hd := abs_le.mp (hf.2.1 x y (hlarge hx) (hlarge hy))
    have hlo := WithLp.dist_fst_le (f x) (f y)
    have hup := product_dist_le_sum (f x) (f y)
    have hz := dist_triangle (f x).snd z₀ (f y).snd
    rw [dist_comm z₀ (f y).snd] at hz
    have hxy : dist (f x).snd (f y).snd ≤ 2*a := by
      linarith [hzbound hx,hzbound hy]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro y hy
    have hylarge : dist (WithLp.toLp 2 (y,z₀)) (WithLp.toLp 2 (0,z₀)) ≤ 1-ε := by
      rw [metric_prod_same_second]
      linarith
    obtain ⟨x,hx,hxy⟩ := hf.2.2 (WithLp.toLp 2 (y,z₀)) hylarge
    refine ⟨x,?_,(WithLp.dist_fst_le (f x) (WithLp.toLp 2 (y,z₀))).trans
      (hxy.trans (by linarith))⟩
    have hd := (abs_le.mp (hf.2.1 x p hx hpp)).1
    have ht := dist_triangle (f x) (WithLp.toLp 2 (y,z₀)) (f p)
    have ht' := dist_triangle (WithLp.toLp 2 (y,z₀)) (WithLp.toLp 2 (0,z₀)) (f p)
    rw [metric_prod_same_second,dist_comm (WithLp.toLp 2 ((0:Euclidean n),z₀)) (f p)] at ht'
    apply (div_le_iff₀ hr).mp
    linarith [hf.1]

end RegularPointCoordinates

end

end OAI
