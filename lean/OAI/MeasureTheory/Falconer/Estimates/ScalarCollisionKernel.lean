import OAI.MeasureTheory.Falconer.Radial.ScalarAffineFibers
import OAI.MeasureTheory.Falconer.Geometry.ProjectionEnergy

namespace OAI

/-! Counting projection collisions by a scalar kernel. The diagonal and
horizontal coincidences are separated before applying the affine estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def scalarPairCell (δ c : ℝ) (p : ℝ × ℝ) : ℤ := ⌊(p.1+c*p.2)/δ⌋

noncomputable def scalarCollisionKernel (δ η R : ℝ) (p q : ℝ × ℝ) : ℝ :=
  if p.2 = q.2 then 0 else
    if |p.1-q.1| ≤ δ+R*|p.2-q.2| then 5+4*δ/(η*|p.2-q.2|) else 0

theorem scalar_collision_support {δ c R : ℝ} (hδ : 0 < δ)
    (hc : |c| ≤ R) {p q : ℝ × ℝ} (hcell : scalarPairCell δ c p = scalarPairCell δ c q) :
    |p.1-q.1| ≤ δ+R*|p.2-q.2| := by
  have hh := (same_scalar_cell_dist_lt hδ hcell).le
  have he : p.1-q.1 = ((p.1+c*p.2)-(q.1+c*q.2))-c*(p.2-q.2) := by ring
  rw [he]
  have ht := abs_add_le ((p.1+c*p.2)-(q.1+c*q.2)) (-(c*(p.2-q.2)))
  rw [abs_neg,abs_mul] at ht
  have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg (p.2-q.2))
  have he' : |((p.1+c*p.2)-(q.1+c*q.2))-c*(p.2-q.2)| ≤
      |(p.1+c*p.2)-(q.1+c*q.2)|+|c| * |p.2-q.2| := by
    simpa only [sub_eq_add_neg] using ht
  linarith

theorem scalar_collision_parameter_kernel {δ η R : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (A : Finset ℝ) (hA : ∀ c ∈ A, |c| ≤ R)
    (hsepA : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    {p q : ℝ × ℝ} (hrow : p.2 = q.2 → p ≠ q → δ ≤ |p.1-q.1|) :
    ((A.filter fun c => scalarPairCell δ c p = scalarPairCell δ c q).card : ℝ) ≤
      (if p = q then (A.card : ℝ) else 0)+scalarCollisionKernel δ η R p q := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [scalarCollisionKernel]
  by_cases hy : p.2 = q.2
  · have hempty : (A.filter fun c => scalarPairCell δ c p = scalarPairCell δ c q) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      have hh := same_scalar_cell_dist_lt hδ (Finset.mem_filter.mp hc).2
      have he : (p.1+c*p.2)-(q.1+c*q.2) = p.1-q.1 := by rw [hy]; ring
      rw [he] at hh
      exact (not_lt_of_ge (hrow hy hpq)) hh
    simp only [hempty,Finset.card_empty,Nat.cast_zero,hpq,ite_false,scalarCollisionKernel,hy,ite_true,add_zero,le_refl]
  by_cases hs : |p.1-q.1| ≤ δ+R*|p.2-q.2|
  · have hr : 0 < |p.2-q.2| := abs_pos.mpr (sub_ne_zero.mpr hy)
    have hb := scalar_projection_collision_parameter_bound hδ hη hr p q le_rfl A hsepA
    have he : (A.filter fun c => scalarPairCell δ c p = scalarPairCell δ c q) =
        A.filter (fun c => ⌊(p.1+c*p.2)/δ⌋ = ⌊(q.1+c*q.2)/δ⌋) := by
      ext c
      constructor
      · intro hc
        obtain ⟨hc,he⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr ⟨hc,he⟩
      · intro hc
        obtain ⟨hc,he⟩ := Finset.mem_filter.mp hc
        exact Finset.mem_filter.mpr ⟨hc,he⟩
    rw [he]
    simpa only [scalarCollisionKernel,hpq,hy,hs,ite_false,ite_true,zero_add] using hb
  · have hempty : (A.filter fun c => scalarPairCell δ c p = scalarPairCell δ c q) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      obtain ⟨hcA,he⟩ := Finset.mem_filter.mp hc
      exact hs (scalar_collision_support hδ (hA c hcA) he)
    simp only [hempty,Finset.card_empty,Nat.cast_zero,hpq,ite_false,scalarCollisionKernel,hy,hs,zero_add,le_refl]

theorem scalar_projection_collision_sum (δ : ℝ) (A : Finset ℝ) (S : Finset (ℝ × ℝ)) :
    (∑ c ∈ A, ((cellCollisions S (scalarPairCell δ c)).card : ℝ)) =
      ∑ p ∈ S, ∑ q ∈ S, ((A.filter fun c => scalarPairCell δ c p = scalarPairCell δ c q).card : ℝ) := by
  classical
  have hn := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := A) (t := S ×ˢ S) (fun c v => scalarPairCell δ c v.1 = scalarPairCell δ c v.2)
  simp only [Finset.bipartiteAbove,Finset.bipartiteBelow] at hn
  change (∑ c ∈ A, ((cellCollisions S (scalarPairCell δ c)).card : ℝ)) = _
  have he : (∑ c ∈ A, ((cellCollisions S (scalarPairCell δ c)).card : ℝ)) =
      ∑ v ∈ S ×ˢ S, ((A.filter fun c => scalarPairCell δ c v.1 = scalarPairCell δ c v.2).card : ℝ) := by
    unfold cellCollisions
    exact_mod_cast hn
  rw [he,Finset.sum_product]

theorem scalar_projection_kernel_sum {δ η R : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (A : Finset ℝ) (hA : ∀ c ∈ A, |c| ≤ R)
    (hsepA : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (S : Finset (ℝ × ℝ))
    (hrow : ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p ≠ q → δ ≤ |p.1-q.1|) :
    (∑ c ∈ A, ((cellCollisions S (scalarPairCell δ c)).card : ℝ)) ≤
      (A.card : ℝ)*S.card+∑ p ∈ S, ∑ q ∈ S, scalarCollisionKernel δ η R p q := by
  classical
  rw [scalar_projection_collision_sum]
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        ((if p = q then (A.card : ℝ) else 0)+scalarCollisionKernel δ η R p q) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
        scalar_collision_parameter_kernel hδ hη A hA hsepA (hrow p hp q hq)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq]
      simp [mul_comm]

end Falconer

end OAI
