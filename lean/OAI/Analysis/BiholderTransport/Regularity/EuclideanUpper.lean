import Mathlib
import OAI.Analysis.BiholderTransport.Duality.CompactDual
import OAI.Analysis.BiholderTransport.CostGeometry.DividedAction

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def hopfLax (t : ℝ) (u : M → ℝ) (z : M) : ℝ :=
  sInf (Set.range (fun x => u x + cost x z / t))

lemma exists_hopfLax_minimizer {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z : M) :
    ∃ x, hopfLax t u z = u x+cost x z/t ∧
      ∀ a, u x+cost x z/t ≤ u a+cost a z/t := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left z).div_const t)).continuousOn
  have hmin : ∀ a, u x+cost x z/t ≤ u a+cost a z/t := fun a => hx (mem_univ a)
  refine ⟨x,le_antisymm ?_ ?_,hmin⟩
  · exact csInf_le ⟨_,by rintro _ ⟨a,rfl⟩; exact hmin a⟩ ⟨x,rfl⟩
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨a,rfl⟩; exact hmin a)

lemma hopfLax_le {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z x : M) :
    hopfLax t u z ≤ u x+cost x z/t := by
  obtain ⟨a,ha,hmin⟩ := exists_hopfLax_minimizer hu t z
  rw [ha]
  exact hmin x

lemma hopfLax_eq_of_min {u : M → ℝ} (hu : Continuous u) (t : ℝ) (z x : M)
    (hmin : ∀ a, u x+cost x z/t ≤ u a+cost a z/t) :
    hopfLax t u z = u x+cost x z/t := by
  apply le_antisymm (hopfLax_le hu t z x)
  obtain ⟨a,ha,_⟩ := exists_hopfLax_minimizer hu t z
  rw [ha]
  exact hmin a

lemma hopfLax_eq_neg_transform {u : M → ℝ} (hu : Continuous u) {t : ℝ}
    (ht : 0<t) (z : M) :
    hopfLax t u z = -cTransform (fun x => t*u x) z/t := by
  let v := fun x => t*u x
  have hv : Continuous v := continuous_const.mul hu
  obtain ⟨a,ha,hmin⟩ := exists_hopfLax_minimizer hu t z
  have hc : cTransform v z = -t*(u a+cost a z/t) := by
    apply le_antisymm
    · apply (cTransform_le_iff hv z _).mpr
      intro x
      have H := mul_le_mul_of_nonneg_left (hmin x) ht.le
      rw [mul_add,mul_div_cancel₀ _ ht.ne',mul_add,mul_div_cancel₀ _ ht.ne'] at H
      dsimp [v]
      rw [cost_symm z x]
      have : t*(u a+cost a z/t)=t*u a+cost a z := by field_simp
      rw [neg_mul,this]
      linarith
    · have H := cTransform_gap_nonneg hv z a
      dsimp [contactGap] at H
      rw [cost_symm z a] at H
      have : -t*(u a+cost a z/t) = -cost a z-t*u a := by field_simp; ring
      rw [this]
      linarith
  rw [hc,ha]
  field_simp

omit [CompactSpace M] [Nonempty M] in
lemma divided_cost_triangle (x z y : M) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    cost x y ≤ cost x z/t+cost z y/(1-t) := by
  convert squared_dist_divided_action_le x z y ht ht1 using 1 <;>
    simp only [cost,div_div,mul_comm]

lemma dual_hopfLax_sum_nonneg {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {t : ℝ} (ht : 0<t) (ht1 : t<1) (z : M) :
    0 ≤ hopfLax t u z+hopfLax (1-t) v z := by
  obtain ⟨x,hx,_⟩ := exists_hopfLax_minimizer hu t z
  obtain ⟨y,hy,_⟩ := exists_hopfLax_minimizer hv (1-t) z
  rw [hx,hy,cost_symm y z]
  have hg := dualPair_gap_nonneg hv hdual x y
  have hc := divided_cost_triangle x z y ht ht1
  dsimp [contactGap] at hg
  linarith

end WeakMTWTransport
end

end OAI
