import Mathlib
import OAI.Geometry.Cannon.Boundary.PolynomialPacking

namespace OAI

section
section
section
noncomputable section
namespace CannonGeometry
open Set Metric

variable (X : Type*) [MetricSpace X]

def ApproxSelfSimilar : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r → r ≤ diam (univ : Set X) →
    ∃ f : X ≃ₜ X, ∀ y ∈ ball x r, ∀ z ∈ ball x r,
      dist (f y) (f z)*r ≤ C*dist y z ∧ dist y z ≤ C*dist (f y) (f z)*r

end CannonGeometry

namespace CannonRelease
open CannonGraph CannonVisual CannonGeometry Set Metric

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance approxSelfSimilarSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_approx_self_similar :
    let _ := visualMetricSpace D hδ
    ApproxSelfSimilar (Boundary D) := by
  let _ := visualMetricSpace D hδ
  let U := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let L := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  let A := Real.exp (2*visualExponent δ)
  have hU : 0 < U := by dsimp [U]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : 0 < A := Real.exp_pos _
  have hLA : 0 < L*A := mul_pos hL hA
  refine ⟨1+U+L*A,by linarith,?_⟩
  intro x r hr hrdia
  have hdia : diam (univ : Set (Boundary D)) ≤ 1 :=
    diam_le_of_forall_dist_le zero_le_one (fun x _ y _ => boundaryDist_le_one D hδ x y)
  obtain ⟨k,hk,hk'⟩ := visualScale_near δ hr (hrdia.trans hdia)
  obtain ⟨ray,hrep⟩ := Quotient.exists_rep x
  subst x
  let f := boundaryHomeomorph D ⟨δ,hδ⟩ (ray.val k)⁻¹
  refine ⟨f,?_⟩
  intro y hy z hz
  have hy' : boundaryDist D hδ (Quotient.mk' ray) y ≤ visualScale δ k := by
    exact (dist_comm _ _).le.trans ((mem_ball.mp hy).le.trans hk)
  have hz' : boundaryDist D hδ (Quotient.mk' ray) z ≤ visualScale δ k := by
    exact (dist_comm _ _).le.trans ((mem_ball.mp hz).le.trans hk)
  have hh := visual_ball_expansion D hδ ray k y z hy' hz'
  change dist (f y) (f z)*visualScale δ k ≤ U*dist y z ∧
    dist y z ≤ L*dist (f y) (f z)*visualScale δ k at hh
  constructor
  · calc
      dist (f y) (f z)*r ≤ dist (f y) (f z)*visualScale δ k := mul_le_mul_of_nonneg_left hk dist_nonneg
      _ ≤ U*dist y z := hh.1
      _ ≤ (1+U+L*A)*dist y z := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
  · calc
      dist y z ≤ L*dist (f y) (f z)*visualScale δ k := hh.2
      _ ≤ L*dist (f y) (f z)*(A*r) := mul_le_mul_of_nonneg_left hk'
        (mul_nonneg hL.le dist_nonneg)
      _ = (L*A)*dist (f y) (f z)*r := by ring
      _ ≤ (1+U+L*A)*dist (f y) (f z)*r := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) dist_nonneg) hr.le

end CannonRelease

namespace CannonNet
open Set Metric

variable {X : Type*} [MetricSpace X]

def IsApproximation {ι : Type*} (p : ι → X) (C : ι → Set X) (s κ : ℝ) : Prop :=
  (∀ i, IsOpen (C i)) ∧ (∀ x, ∃ i, x ∈ C i) ∧
  (∀ i, ball (p i) (s/κ) ⊆ C i) ∧
  (∀ i, C i ⊆ ball (p i) (κ*s)) ∧
  (∀ i j, i ≠ j → Disjoint (ball (p i) (s/κ)) (ball (p j) (s/κ)))

lemma exists_scale_below {a s : ℝ} (ha : 1 < a) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, s/a < (a^n)⁻¹ ∧ (a^n)⁻¹ ≤ s := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hq : 0 < a⁻¹ := inv_pos.mpr hap
  have hq1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near_of_lt_one hs hs1 hq hq1
  rcases lt_or_eq_of_le hn' with hlt | heq
  · refine ⟨n+1,?_,?_⟩
    · rw [← inv_pow,pow_succ,div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hlt hq
    · simpa only [inv_pow] using hn.le
  · refine ⟨n,?_,?_⟩
    · rw [← inv_pow,← heq]
      exact (div_lt_self hs ha)
    · simpa only [inv_pow] using heq.ge

lemma balls_isApproximation {ι : Type*} (p : ι → X) {a r s κ : ℝ}
    (ha : 1 < a) (hs : 0 < s) (hκ : 2*a < κ) (hlow : s/a < r) (hupp : r ≤ s)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (p i) (p j))
    (hcover : ∀ x, ∃ i, dist (p i) x ≤ r) :
    IsApproximation p (fun i => ball (p i) (2*r)) s κ := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hκ2 : 2 < κ := by linarith
  have hκp : 0 < κ := by linarith
  have hr : 0 < r := (div_pos hs hap).trans hlow
  have h2inner : 2*(s/κ) < r := by
    apply lt_trans ?_ hlow
    calc
      2*(s/κ) = (2*s)/κ := by ring
      _ < s/a := (div_lt_div_iff₀ hκp hap).mpr (by nlinarith)
  have hinner : s/κ ≤ 2*r := by have := div_pos hs hκp; linarith
  have houter : 2*r ≤ κ*s := by nlinarith
  refine ⟨fun _ => isOpen_ball,?_,?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi⟩ := hcover x
    exact ⟨i,by change dist x (p i) < 2*r; rw [dist_comm]; linarith⟩
  · exact fun _ => ball_subset_ball hinner
  · exact fun _ => ball_subset_ball houter
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have htri := dist_triangle (p i) x (p j)
    have hxi' := mem_ball.mp hxi
    have hxj' := mem_ball.mp hxj
    rw [dist_comm x (p i)] at hxi'
    have hd := hsep i j hij
    linarith

theorem exists_net_sequence [CompactSpace X] {a : ℝ} (ha : 1 < a) :
    ∃ T : ℕ → Finset X, ∀ n,
      (∀ x ∈ T n, ∀ y ∈ T n, x ≠ y → (a^n)⁻¹ ≤ dist x y) ∧
      (∀ x : X, ∃ y ∈ T n, dist y x ≤ (a^n)⁻¹) := by
  classical
  have h (n : ℕ) := exists_compact_net (X:=X) ((a^n)⁻¹)
    (inv_pos.mpr (pow_pos (zero_lt_one.trans ha) n))
  choose T hs hc _ using h
  exact ⟨T,fun n => ⟨hs n,by intro x; simpa only [dist_comm] using hc n x⟩⟩

end CannonNet

end
end
end
end

end OAI
