import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

 def GeometricHolderAt {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (θ : ℝ) (f : X → Y) (p : X) : Prop :=
  ∃ r C : ℝ, 0<r ∧ 0 ≤ C ∧ ∀ j x, x∈Metric.ball p r → ∀ y, y∈Metric.ball p r →
    dist x y ≤ θ^j*r → dist (f x) (f y) ≤ C*(1/2)^j

 theorem GeometricHolderAt.mono_scale {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {θ η : ℝ} {f : X → Y} {p : X} (h : GeometricHolderAt θ f p)
    (hη : 0 ≤ η) (he : η ≤ θ) : GeometricHolderAt η f p := by
  obtain ⟨r,C,hr,hC,h⟩ := h
  refine ⟨r,C,hr,hC,fun j x hx y hy hxy ↦ h j x hx y hy (hxy.trans ?_)⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη he j) hr.le

 theorem GeometricHolderAt.shrink_amplitude {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {θ : ℝ} (hθ : 0<θ) {f : X → Y} {p : X} (h : GeometricHolderAt θ f p)
    {ε R : ℝ} (hε : 0<ε) (hR : 0<R) :
    ∃ r : ℝ, 0<r ∧ r ≤ R ∧ ∀ j x, x∈Metric.ball p r → ∀ y, y∈Metric.ball p r →
      dist x y ≤ θ^j*r → dist (f x) (f y) ≤ ε*(1/2)^j := by
  obtain ⟨s,C,hs,hC,h⟩ := h
  have ht : Tendsto (fun j : ℕ ↦ C*(1/2:ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).const_mul C
  obtain ⟨J,hJ⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  let r := min R (min s (θ^J*s))
  have hr : 0<r := lt_min hR (lt_min hs (by positivity))
  have hrs : r ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hrJ : r ≤ θ^J*s := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,min_le_left _ _,fun j x hx y hy hxy ↦ ?_⟩
  have hh := h (j+J) x (Metric.ball_subset_ball hrs hx) y (Metric.ball_subset_ball hrs hy)
    (hxy.trans (by simpa only [pow_add,mul_assoc] using
      mul_le_mul_of_nonneg_left hrJ (pow_nonneg hθ.le j)))
  apply hh.trans
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hJ.le (by positivity : 0 ≤ (1/2:ℝ)^j)]

 theorem GeometricHolderAt.congr {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {θ : ℝ} (hθ : 0 ≤ θ) {f g : X → Y} {p : X} (h : GeometricHolderAt θ f p)
    (he : f=ᶠ[𝓝 p] g) : GeometricHolderAt θ g p := by
  obtain ⟨r,C,hr,hC,h⟩ := h
  obtain ⟨s,hs,hsb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min r s,C,lt_min hr hs,hC,fun j x hx y hy hxy ↦ ?_⟩
  have hxs : dist x p<s := (Metric.mem_ball.mp hx).trans_le (min_le_right _ _)
  have hys : dist y p<s := (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
  rw [←hsb hxs,←hsb hys]
  exact h j x (Metric.ball_subset_ball (min_le_left _ _) hx) y
    (Metric.ball_subset_ball (min_le_left _ _) hy)
    (hxy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)))

 theorem GeometricHolderAt.prodMk {X Y Z : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [PseudoMetricSpace Z] {θ : ℝ} (hθ : 0 ≤ θ)
    {f : X → Y} {g : X → Z} {p : X}
    (hf : GeometricHolderAt θ f p) (hg : GeometricHolderAt θ g p) :
    GeometricHolderAt θ (fun x ↦ (f x,g x)) p := by
  obtain ⟨r,C,hr,hC,hf⟩ := hf
  obtain ⟨s,D,hs,hD,hg⟩ := hg
  refine ⟨min r s,max C D,lt_min hr hs,le_trans hC (le_max_left _ _),fun j x hx y hy hxy ↦ ?_⟩
  rw [Prod.dist_eq]
  apply max_le
  · exact (hf j x (Metric.ball_subset_ball (min_le_left _ _) hx) y
      (Metric.ball_subset_ball (min_le_left _ _) hy)
      (hxy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg hθ _)))).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (hg j x (Metric.ball_subset_ball (min_le_right _ _) hx) y
      (Metric.ball_subset_ball (min_le_right _ _) hy)
      (hxy.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hθ _)))).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

 theorem GeometricHolderAt.const {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (θ : ℝ) (p : X) (c : Y) : GeometricHolderAt θ (fun _ : X ↦ c) p := by
  refine ⟨1,0,by norm_num,le_rfl,?_⟩
  intros; simp

 theorem geometricHolderAt_of_local_lipschitz {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] {θ r L : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) (hr : 0<r) (hL : 0 ≤ L)
    {f : X → Y} {p : X}
    (h : ∀ x∈Metric.ball p r, ∀ y∈Metric.ball p r, dist (f x) (f y) ≤ L*dist x y) :
    GeometricHolderAt θ f p := by
  refine ⟨r,L*r,hr,mul_nonneg hL hr.le,fun j x hx y hy hxy ↦ ?_⟩
  exact (h x hx y hy).trans ((mul_le_mul_of_nonneg_left hxy hL).trans (by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ hθ' j) (mul_nonneg hL hr.le)
    nlinarith))

end RPISingularHarnack

end

end OAI
