import OAI.Combinatorics.ContingencyTables.Transport.FiniteIndependentAverages
import OAI.Combinatorics.ContingencyTables.Transport.FirstSuccess

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

def expectation (p : RationalLaw X) (g : X → ℝ) : ℝ := ∑ x,(p.mass x:ℝ)*g x

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

/-- Bounded real observables may be evaluated after a rational finite
experiment. Their expectation error follows from the actual output TV. -/
theorem expectation_difference (p q : RationalLaw X) (g : X → ℝ) (U : ℝ)
    (hg : ∀ x,|g x| ≤ U) :
    |expectation p g-expectation q g| ≤ 2*U*(variation p q:ℝ) := by
  have he : expectation p g-expectation q g=∑ x,((p.mass x:ℝ)-(q.mass x:ℝ))*g x := by
    unfold expectation
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ x,|((p.mass x:ℝ)-(q.mass x:ℝ))*g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,|(p.mass x:ℝ)-(q.mass x:ℝ)| * U := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg _)
    _ = _ := by
      rw [←Finset.sum_mul]
      simp only [variation,Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
      ring

lemma expectation_bounds (p : RationalLaw X) (g : X → ℝ) (L U : ℝ)
    (hg : ∀ x,L ≤ g x ∧ g x ≤ U) : L ≤ expectation p g ∧ expectation p g ≤ U := by
  have htotal : ∑ x,(p.mass x:ℝ)=1 := by exact_mod_cast p.total
  unfold expectation
  constructor
  · calc
      L = ∑ x,(p.mass x:ℝ)*L := by rw [←Finset.sum_mul,htotal,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).1 (by exact_mod_cast p.nonnegative x))
  · calc
      _ ≤ ∑ x,(p.mass x:ℝ)*U := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hg x).2 (by exact_mod_cast p.nonnegative x))
      _ = U := by rw [←Finset.sum_mul,htotal,one_mul]

end ContingencyTables.FiniteLawMoments

end OAI
