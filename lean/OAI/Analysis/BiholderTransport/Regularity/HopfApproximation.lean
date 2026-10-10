import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.EuclideanUpper

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma hopfLax_le_self {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
    hopfLax t u z ≤ u z := by
  simpa only [cost,dist_self,zero_pow (by norm_num : 2≠0),zero_div,add_zero] using hopfLax_le hu t z z

lemma hopfLax_short_approx {u : M → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {t : ℝ} (ht : 0<t) (z : M) :
    u z-(L:ℝ)^2*t/2 ≤ hopfLax t u z ∧ hopfLax t u z ≤ u z := by
  refine ⟨?_,hopfLax_le_self hu.continuous t z⟩
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer hu.continuous t z
  have H := hu.dist_le_mul x z
  rw [Real.dist_eq] at H
  have H1 := (abs_le.mp H).1
  rw [hx,cost]
  apply (mul_le_mul_iff_left₀ ht).mp
  have he : (u x+dist x z^2/2/t)*t=u x*t+dist x z^2/2 := by field_simp
  rw [he]
  have H2 := mul_le_mul_of_nonneg_right H1 ht.le
  nlinarith only [H2,sq_nonneg (dist x z-(L:ℝ)*t)]

lemma hopfLax_minimizer_distance {u : M → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    {t : ℝ} (ht : 0<t) {z x : M}
    (hx : hopfLax t u z=u x+cost x z/t) : dist x z ≤ 2*(L:ℝ)*t := by
  have H := hopfLax_le_self hu.continuous t z
  rw [hx,cost] at H
  have Hl := (abs_le.mp (show |u x-u z| ≤ (L:ℝ)*dist x z by
    simpa only [Real.dist_eq] using hu.dist_le_mul x z)).1
  have HH : dist x z^2/2 ≤ (u z-u x)*t := by
    apply (div_le_iff₀ ht).mp
    linarith only [H]
  by_contra h
  have hq : 0 < dist x z := (by positivity : 0 ≤ 2*(L:ℝ)*t).trans_lt (lt_of_not_ge h)
  have Hl' := mul_le_mul_of_nonneg_right (show u z-u x ≤ (L:ℝ)*dist x z by linarith only [Hl]) ht.le
  nlinarith only [HH,Hl',mul_pos hq (sub_pos.mpr (lt_of_not_ge h))]

lemma hopfLax_time_comparison {u : M → ℝ} (hu : Continuous u) {H : ℝ}
    (hH : ∀ x y : M, cost x y ≤ H) (t s : ℝ) (z : M) :
    |hopfLax t u z-hopfLax s u z| ≤ H*|1/t-1/s| := by
  have hbound : ∀ x : M, |cost x z/t-cost x z/s| ≤ H*|1/t-1/s| := by
    intro x
    calc
      _=|cost x z*(1/t-1/s)| := by congr 1; ring
      _=cost x z*|1/t-1/s| := by rw [abs_mul,abs_of_nonneg (cost_nonneg x z)]
      _≤H*|1/t-1/s| := mul_le_mul_of_nonneg_right (hH x z) (abs_nonneg _)
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer hu t z
  obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hu s z
  have Hx := hopfLax_le hu s z x
  have Hy := hopfLax_le hu t z y
  have Bx := (abs_le.mp (hbound x)).1
  have By := (abs_le.mp (hbound y)).2
  rw [abs_le]
  constructor <;> linarith only [hx,hy,Hx,Hy,Bx,By]

lemma hopfLax_one (u : M → ℝ) (hu : Continuous u) :
    hopfLax 1 u=fun z => -cTransform u z := by
  funext z
  simpa only [one_mul,div_one] using hopfLax_eq_neg_transform hu (by norm_num : (0:ℝ)<1) z

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma uniform_hopfLax_minimizers_eventually_in (L : ℝ≥0) {x : M} {V : Set M}
    (hV : V∈𝓝 x) :
    ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x), 0<q.1 → ∀ f : M → ℝ, LipschitzWith L f →
      ∀ y : M, hopfLax q.1 f q.2=f y+cost y q.2/q.1 → y∈V := by
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hc : ContinuousAt (fun q : ℝ×M => 2*(L:ℝ)*q.1+dist q.2 x) (0,x) := by fun_prop
  have he : ∀ᶠ q : ℝ×M in 𝓝 ((0:ℝ),x),2*(L:ℝ)*q.1+dist q.2 x<r :=
    hc.eventually_lt continuousAt_const (by simpa only [mul_zero,dist_self,zero_add] using hr)
  filter_upwards [he] with q hq
  intro ht f hf y hy
  apply hrV
  change dist y x<r
  have hd := hopfLax_minimizer_distance hf ht hy
  have htri := dist_triangle y q.2 x
  linarith only [hd,htri,hq]

end WeakMTWTransport

end

end OAI
