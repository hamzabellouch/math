import OAI.Geometry.RCD.Metric.ProductVerticalDeviation

namespace OAI

/-! # Actual geodesics under a pointed product approximation -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

variable {X Z : Type*} [MetricSpace X] [MetricSpace Z] {n : ℕ}

/-- The geodesic from the base point to a lift of a vertical target stays
quantitatively near the vertical fiber. The factor need not be geodesic. -/
theorem pointed_vertical_geodesic {p x : X} {z₀ z₁ : Z} {ρ ε : ℝ}
    (hρ : 0 < ρ) (he : 0 ≤ ε)
    {f : X → WithLp 2 (Euclidean n × Z)}
    (hf : IsPointedApproximation p (WithLp.toLp 2 (0,z₀)) ρ 1 ε f)
    (hx : dist x p ≤ ρ) (hfx : dist (f x) (WithLp.toLp 2 (0,z₁)) ≤ ε)
    {γ : C(Time,X)} (hγ : IsGeodesic γ) (h0 : γ 0=p) (h1 : γ 1=x) :
    (∀ t, dist (γ t) p ≤ ρ) ∧
    (∀ t, ‖(f (γ t)).fst‖ ≤ Real.sqrt (14*ε*(dist z₀ z₁+7*ε))) ∧
    (∀ t, dist (f (γ t)).snd z₀ ≤ dist z₀ z₁+5*ε) ∧
    dist z₀ z₁-3*ε ≤ dist p x/ρ := by
  have htime (t : Time) : dist (γ t) p=(t:ℝ)*dist p x := by
    have hh := hγ t 0
    rw [h0,h1] at hh
    change dist (γ t) p=|(t:ℝ)-0| * dist p x at hh
    simpa only [sub_zero,abs_of_nonneg t.2.1] using hh
  have htime1 (t : Time) : dist (γ t) x=(1-(t:ℝ))*dist p x := by
    have hh := hγ t 1
    rw [h0,h1] at hh
    change dist (γ t) x=|(t:ℝ)-1| * dist p x at hh
    simpa only [abs_of_nonpos (sub_nonpos.mpr t.2.2),neg_sub] using hh
  have hpoints (t : Time) : dist (γ t) p ≤ ρ := by
    rw [htime]
    exact (mul_le_of_le_one_left dist_nonneg t.2.2).trans (by simpa [dist_comm] using hx)
  have hp : dist p p ≤ 1*ρ := by simpa using hρ.le
  have hx' : dist x p ≤ 1*ρ := by simpa using hx
  have hfpx := abs_le.mp (hf.2.1 p x hp hx')
  have hvertical : dist (WithLp.toLp 2 ((0:Euclidean n),z₀))
      (WithLp.toLp 2 (0,z₁))=dist z₀ z₁ := by
    rw [metric_product_distance_L2]
    simp only [WithLp.fst,WithLp.snd,dist_self,zero_pow (by norm_num : (2:ℕ)≠0),
      zero_add,Real.sqrt_sq dist_nonneg]
  have hupper : dist p x/ρ ≤ dist z₀ z₁+3*ε := by
    have ht := dist_triangle (f p) (WithLp.toLp 2 (0,z₀)) (f x)
    have ht' := dist_triangle (WithLp.toLp 2 ((0:Euclidean n),z₀))
      (WithLp.toLp 2 (0,z₁)) (f x)
    rw [hvertical,dist_comm (WithLp.toLp 2 ((0:Euclidean n),z₁)) (f x)] at ht'
    linarith [hf.1]
  have hlower : dist z₀ z₁-3*ε ≤ dist p x/ρ := by
    have ht := dist_triangle (WithLp.toLp 2 ((0:Euclidean n),z₀)) (f p)
      (WithLp.toLp 2 (0,z₁))
    have ht' := dist_triangle (f p) (f x) (WithLp.toLp 2 (0,z₁))
    rw [hvertical,dist_comm (WithLp.toLp 2 ((0:Euclidean n),z₀)) (f p)] at ht
    linarith [hf.1]
  have hdist0 (t : Time) : dist (f (γ t)) (WithLp.toLp 2 (0,z₀)) ≤
      (t:ℝ)*(dist p x/ρ)+2*ε := by
    have hh := (abs_le.mp (hf.2.1 (γ t) p (by simpa using hpoints t) hp)).2
    rw [htime] at hh
    have ht := dist_triangle (f (γ t)) (f p) (WithLp.toLp 2 (0,z₀))
    have heq : (t:ℝ)*dist p x/ρ=(t:ℝ)*(dist p x/ρ) := by ring
    rw [heq] at hh
    linarith [hf.1]
  have hdist1 (t : Time) : dist (f (γ t)) (WithLp.toLp 2 (0,z₁)) ≤
      (1-(t:ℝ))*(dist p x/ρ)+2*ε := by
    have hh := (abs_le.mp (hf.2.1 (γ t) x (by simpa using hpoints t) hx')).2
    rw [htime1] at hh
    have ht := dist_triangle (f (γ t)) (f x) (WithLp.toLp 2 (0,z₁))
    have heq : (1-(t:ℝ))*dist p x/ρ=(1-(t:ℝ))*(dist p x/ρ) := by ring
    rw [heq] at hh
    linarith
  refine ⟨hpoints,?_,?_,hlower⟩
  · intro t
    have hd : dist (f (γ t)) (WithLp.toLp 2 (0,z₀))+
        dist (f (γ t)) (WithLp.toLp 2 (0,z₁)) ≤ dist z₀ z₁+7*ε := by
      linarith [hdist0 t,hdist1 t]
    have hs := product_vertical_deviation (f (γ t)) z₀ z₁ (by positivity : 0 ≤ 7*ε) hd
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    nlinarith only [hs]
  · intro t
    have hpbound : (t:ℝ)*(dist p x/ρ) ≤ dist p x/ρ :=
      mul_le_of_le_one_left (div_nonneg dist_nonneg hρ.le) t.2.2
    have hproj := WithLp.dist_snd_le (f (γ t)) (WithLp.toLp 2 (0,z₀))
    change dist (f (γ t)).snd z₀ ≤ _ at hproj
    linarith [hdist0 t]

end RegularPointCoordinates

end

end OAI
