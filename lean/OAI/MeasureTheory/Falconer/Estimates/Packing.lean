import OAI.MeasureTheory.Falconer.Angular.SphereModel
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-!
# Packing bounds for the cap centers

Disjoint Euclidean balls give a bound independent of the number of chosen
centers. This supplies the bounded-overlap count needed for a separated cap
partition, and a polynomial global bound on the cap count.
-/

namespace Falconer
open Set Metric MeasureTheory

private theorem volume_real_ball {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Space d)).real (ball x r) =
      r^d*(volume : Measure (Space d)).real (ball 0 1) := by
  simp only [measureReal_def,Measure.addHaar_ball_of_pos volume x hr,ENNReal.toReal_mul,
    finrank_euclideanSpace,Fintype.card_fin,ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

theorem separated_ball_card {d : ℕ} (S : Finset (Space d)) (x₀ : Space d)
    {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → s ≤ dist x y)
    (hball : ∀ x ∈ S, dist x x₀ ≤ r) :
    (S.card : ℝ) ≤ (2*r/s+1)^d := by
  have ht : 0 < s/2 := half_pos hs
  have hbig : 0 < r+s/2 := by linarith
  have hd : PairwiseDisjoint (S : Set (Space d)) (fun x => ball x (s/2)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hdist := dist_triangle x z y
    have h₁ := mem_ball.mp hz
    have h₂ := mem_ball.mp hz'
    rw [dist_comm z x] at h₁
    have hh := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ S, ball x (s/2)) ⊆ ball x₀ (r+s/2) := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp hz
    apply mem_ball.mpr
    have h₁ := mem_ball.mp hzx
    have h₂ := hball x hx
    have h₃ := dist_triangle z x x₀
    linarith
  have hm := measureReal_mono (μ := (volume : Measure (Space d))) hsub
    (measure_ball_lt_top.ne)
  rw [measureReal_biUnion_finset hd (fun _ _ => isOpen_ball.measurableSet)] at hm
  simp_rw [volume_real_ball _ ht] at hm
  rw [Finset.sum_const, nsmul_eq_mul, volume_real_ball _ hbig] at hm
  let V := (volume : Measure (Space d)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : Space d) zero_lt_one).ne' measure_ball_lt_top.ne
  have he : r+s/2 = (2*r/s+1)*(s/2) := by field_simp
  rw [he,mul_pow] at hm
  have hp : 0 < (s/2)^d*V := mul_pos (pow_pos ht d) hV
  apply (mul_le_mul_iff_right₀ hp).mp
  convert hm using 1 <;> ring

theorem separated_sphere_overlap {d : ℕ} (S : Finset (Sphere d))
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) (w : Sphere d) :
    ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^d := by
  classical
  let T := S.filter (fun c => dist w c ≤ δ)
  have hinj : Function.Injective (fun c : Sphere d => (c : Space d)) := Subtype.val_injective
  have he := separated_ball_card (T.image (fun c : Sphere d => (c : Space d))) (w : Space d)
    (half_pos hδ) hδ.le (by
      intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (fun hab => hxy (congrArg Subtype.val hab))) (by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      simpa only [Subtype.dist_eq,dist_comm] using (Finset.mem_filter.mp ha).2)
  rw [Finset.card_image_of_injective T hinj] at he
  have hratio : 2*δ/(δ/2)+1 = (5 : ℝ) := by
    field_simp
    norm_num
  simpa only [hratio] using he

end Falconer

end OAI
