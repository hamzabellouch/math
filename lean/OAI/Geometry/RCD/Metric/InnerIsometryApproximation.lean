import OAI.Geometry.RCD.Metric.RecenterApproximation
import OAI.Geometry.RCD.Metric.MetricBallLaw

namespace OAI

/-! # Transferring a full inner isometry to a small physical ball -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pointed_approximation_of_inner_isometry {n : ℕ} {p : X} {q : Y} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hεsmall : ε < 1/1024)
    {V : X → Y} (hV : IsPointedApproximation p q r 5 ε V)
    (f : closedBall q (1/4:ℝ) → Euclidean n) (hf : Isometry f)
    (hfq : f ⟨q,by simp⟩ = 0) (hfull : ball (0:Euclidean n) (1/32) ⊆ range f) :
    ∃ w : X → Euclidean n, IsPointedApproximation p 0 (r/256) 2 (4096*ε) w := by
  classical
  let F : Y → Euclidean n := fun y => if h : y ∈ closedBall q (1/4:ℝ) then f ⟨y,h⟩ else 0
  have hFe (y : Y) (hy : y ∈ closedBall q (1/4:ℝ)) : F y = f ⟨y,hy⟩ := by
    dsimp only [F]
    rw [dite_eq_left hy]
  have hFq : F q = 0 := by rw [hFe q (by simp),hfq]
  have hFd (x y : Y) (hx : x ∈ closedBall q (1/4:ℝ)) (hy : y ∈ closedBall q (1/4:ℝ)) :
      dist (F x) (F y) = dist x y := by rw [hFe x hx,hFe y hy,hf.dist_eq]; rfl
  have hrad {x : X} (hx : dist x p ≤ 5*r) :
      |dist (V x) q-dist x p/r| ≤ 2*ε :=
    pointed_metric_radial_distance hr (by norm_num) hV hx
  have hlarge {x : X} (hx : dist x p ≤ 2*(r/256)) : dist x p ≤ 5*r := by linarith
  have hinner {x : X} (hx : dist x p ≤ 2*(r/256)) : V x ∈ closedBall q (1/4:ℝ) := by
    have hh := (abs_le.mp (hrad (hlarge hx))).2
    have hx' : dist x p/r ≤ 1/128 := (div_le_iff₀ hr).mpr (by linarith)
    change dist (V x) q ≤ 1/4
    linarith
  have hscale (x y : Euclidean n) : dist ((256:ℝ) • x) ((256:ℝ) • y) = 256*dist x y := by
    rw [dist_smul₀]
    norm_num
  let g : X → Euclidean n := fun x => (256:ℝ) • F (V x)
  have hg : IsBallApproximation p 0 (r/256) 2 (1024*ε) g := by
    constructor
    · intro x y hx hy
      have hh := mul_le_mul_of_nonneg_left (hV.2.1 x y (hlarge hx) (hlarge hy))
        (by norm_num : (0:ℝ)≤256)
      have he : dist (g x) (g y)-dist x y/(r/256) =
          256*(dist (V x) (V y)-dist x y/r) := by
        dsimp only [g]
        rw [hscale,hFd _ _ (hinner hx) (hinner hy)]
        field_simp
      rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<256)]
      linarith
    · intro z hz
      let v := (1/256:ℝ) • z
      have hvn : ‖v‖ ≤ (2-1024*ε)/256 := by
        dsimp only [v]
        rw [norm_smul]
        norm_num
        have hz' : ‖z‖ ≤ 2-1024*ε := by simpa only [dist_zero_right] using hz
        linarith
      obtain ⟨y,hy⟩ := hfull (show v ∈ ball (0:Euclidean n) (1/32) by
        rw [mem_ball,dist_zero_right]
        linarith)
      have hFy : F y = v := (hFe y y.property).trans hy
      have hyd : dist (y:Y) q = ‖v‖ := by
        rw [← hFd _ _ y.property (by simp),hFy,hFq,dist_zero_right]
      obtain ⟨x,hx,hxy⟩ := hV.2.2 y (by rw [hyd]; linarith)
      have hx' : dist x p ≤ 2*(r/256) := by
        have hd := (abs_le.mp (hrad hx)).1
        have ht := dist_triangle (V x) y q
        rw [hyd] at ht
        have hb : dist x p/r ≤ 1/128 := by linarith
        have hc := (div_le_iff₀ hr).mp hb
        linarith
      refine ⟨x,hx',?_⟩
      have hzv : (256:ℝ) • v = z := by simp [v,smul_smul]
      change dist ((256:ℝ) • F (V x)) z ≤ 1024*ε
      rw [← hzv,hscale,← hFy,hFd _ _ (hinner hx') y.property]
      linarith
  obtain ⟨w,hw⟩ : ∃ w : X → Euclidean n,
      IsPointedApproximation p 0 (r/256) 2 (4*(1024*ε)) w :=
    ⟨_,hg.recenter (by positivity) (by positivity) (by linarith)⟩
  exact ⟨w,by convert hw using 1; ring⟩

end RegularPointCoordinates

end

end OAI
