import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.MovingStrips

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exists_int_coefficient_gt (a r : ℝ) (ha : a≠0) : ∃ m : ℤ, r<a*m := by
  rcases lt_or_gt_of_ne ha with ha|ha
  · obtain ⟨m,hm⟩ := exists_int_lt (r/a)
    exact ⟨m,by have := (lt_div_iff_of_neg ha).mp hm; nlinarith only [this]⟩
  · obtain ⟨m,hm⟩ := exists_int_gt (r/a)
    exact ⟨m,by have := (div_lt_iff₀ ha).mp hm; nlinarith only [this]⟩

lemma integer_coordinates_direction_unbounded (pi : V → ℂ)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (a b : ℝ) (hab : a^2+b^2=1) :
    ∀ r : ℕ, ∃ x, (r : ℝ)<normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b x := by
  intro r
  by_cases ha : a=0
  · have hb : -b≠0 := by intro hh; have : b=0 := neg_eq_zero.mp hh; simp [ha,this] at hab
    obtain ⟨m,hm⟩ := exists_int_coefficient_gt (-b) r hb
    obtain ⟨x,hx,hy⟩ := honto m 0
    exact ⟨x,by simpa [normalCoordinate,hx,hy] using hm⟩
  · obtain ⟨n,hn⟩ := exists_int_coefficient_gt a r ha
    obtain ⟨x,hx,hy⟩ := honto 0 n
    exact ⟨x,by simpa [normalCoordinate,hx,hy] using hn⟩

lemma rotated_coordinate_inverse (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (x : V) :
    u x=a*parallelCoordinate u v a b x-b*normalCoordinate u v a b x ∧
    v x=b*parallelCoordinate u v a b x+a*normalCoordinate u v a b x := by
  constructor <;> dsimp [parallelCoordinate,normalCoordinate] <;>
    nlinarith [congrArg (fun t => t*u x) hab,congrArg (fun t => t*v x) hab]

lemma rotated_box_bound (u v : V → ℝ) (a b U W : ℝ) (hab : a^2+b^2=1) (x : V)
    (hx : |parallelCoordinate u v a b x|≤U) (hy : |normalCoordinate u v a b x|≤W) :
    |u x|≤|a| *U+|b| *W ∧ |v x|≤|b| *U+|a| *W := by
  obtain ⟨he,hf⟩ := rotated_coordinate_inverse u v a b hab x
  constructor
  · rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
  · rw [hf]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg b))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg a))

lemma rotated_no_bounded_ray (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
      |parallelCoordinate u v a b (r.vertex n)|≤U ∧ |normalCoordinate u v a b (r.vertex n)|≤W := by
  rintro ⟨r,U,W,hr⟩
  exact h ⟨r,|a| *U+|b| *W,|b| *U+|a| *W,fun n => rotated_box_bound u v a b U W hab _ (hr n).1 (hr n).2⟩

lemma coordinate_linear_difference (u v : V → ℝ) (a b : ℝ) (x y : V) :
    parallelCoordinate u v a b x-parallelCoordinate u v a b y=a*(u x-u y)+b*(v x-v y) ∧
    normalCoordinate u v a b x-normalCoordinate u v a b y= -b*(u x-u y)+a*(v x-v y) := by
  constructor <;> dsimp [parallelCoordinate,normalCoordinate] <;> ring

lemma rotated_coordinate_increments (u v : V → ℝ) (a b D : ℝ) (hab : a^2+b^2=1) (hD : 0≤D)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |parallelCoordinate u v a b x-parallelCoordinate u v a b y|≤2*D) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |normalCoordinate u v a b x-normalCoordinate u v a b y|≤2*D) := by
  obtain ⟨ha,ha',hb,hb'⟩ := unit_pair_bounds hab
  have haa : |a|≤1 := abs_le.mpr ⟨ha,ha'⟩
  have hbb : |b|≤1 := abs_le.mpr ⟨hb,hb'⟩
  have bound : ∀ A B : ℝ, |A|≤1 → |B|≤1 → ∀ x y, G.fullGraph.Adj x y →
      |A*(u x-u y)+B*(v x-v y)|≤2*D := by
    intro A B hA hB x y hxy
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have hu' := mul_le_mul_of_nonneg_left (hu hxy) (abs_nonneg A)
    have hv' := mul_le_mul_of_nonneg_left (hv hxy) (abs_nonneg B)
    nlinarith [mul_le_mul_of_nonneg_right hA hD,mul_le_mul_of_nonneg_right hB hD]
  constructor
  · intro x y hxy
    rw [(coordinate_linear_difference u v a b x y).1]
    exact bound a b haa hbb x y hxy
  · intro x y hxy
    rw [(coordinate_linear_difference u v a b x y).2]
    exact bound (-b) a (by simpa only [abs_neg] using hbb) haa x y hxy

lemma rotated_aut_differences (u v : V → ℝ) (a b : ℝ) (phi : G.Aut)
    (hu : ∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y)
    (hv : ∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) :
    (∀ x y, parallelCoordinate u v a b (phi.vertex x)-parallelCoordinate u v a b (phi.vertex y)=
      parallelCoordinate u v a b x-parallelCoordinate u v a b y) ∧
    (∀ x y, normalCoordinate u v a b (phi.vertex x)-normalCoordinate u v a b (phi.vertex y)=
      normalCoordinate u v a b x-normalCoordinate u v a b y) := by
  constructor
  · intro x y
    rw [(coordinate_linear_difference u v a b _ _).1,(coordinate_linear_difference u v a b x y).1,hu,hv]
  · intro x y
    rw [(coordinate_linear_difference u v a b _ _).2,(coordinate_linear_difference u v a b x y).2,hu,hv]

end CriticalPercolation.BondGraph
end
end
end

end OAI
