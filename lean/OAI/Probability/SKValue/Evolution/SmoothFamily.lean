import Mathlib
import OAI.Probability.SKValue.Evolution.BurgersDerivative

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

structure BoundedSmoothFamily (T : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  slices : ∀ t∈Icc (0 : ℝ) T, BoundedSmooth (F t)
  bound : ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0 : ℝ) T, ∀ x, |iteratedDeriv n (F t) x|≤C
  joint : ∀ n, ContinuousOn (fun p : ℝ×ℝ ↦ iteratedDeriv n (F p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ)

lemma SmoothEvolution.gradient_family {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) : BoundedSmoothFamily T (fun t ↦ deriv (V t)) :=
  ⟨fun t ht ↦ (h.slices t ht).jets,h.bound,h.jet_joint_continuousOn⟩

lemma BoundedSmoothFamily.deriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) : BoundedSmoothFamily T (fun t ↦ _root_.deriv (F t)) := by
  refine ⟨fun t ht ↦ (h.slices t ht).deriv,?_,?_⟩
  · intro n
    simpa only [iteratedDeriv_succ'] using h.bound (n+1)
  · intro n
    simpa only [iteratedDeriv_succ'] using h.joint (n+1)

lemma BoundedSmoothFamily.mul {T : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily T F) (hG : BoundedSmoothFamily T G) :
    BoundedSmoothFamily T (fun t x ↦ F t x*G t x) := by
  classical
  have hid (n : ℕ) (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
      iteratedDeriv n (fun x ↦ F t x*G t x) x =
      ∑ i∈Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i (F t) x*iteratedDeriv (n-i) (G t) x := by
    rw [iteratedDeriv_fun_mul
      ((hF.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      ((hG.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
  refine ⟨fun t ht ↦ (hF.slices t ht).mul (hG.slices t ht),?_,?_⟩
  · intro n
    choose A hA hFA using hF.bound
    choose B hB hGB using hG.bound
    refine ⟨∑ i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),?_,?_⟩
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))
    · intro t ht x
      rw [hid n t ht x]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFA i t ht x) (Nat.cast_nonneg _)) (hGB (n-i) t ht x)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
  · intro n
    apply ContinuousOn.congr (f := fun p : ℝ×ℝ ↦ ∑ i∈Finset.range (n+1),
      (n.choose i : ℝ)*iteratedDeriv i (F p.1) p.2*iteratedDeriv (n-i) (G p.1) p.2)
    · apply continuousOn_finsetSum
      intro i _
      simpa only [Pi.mul_def] using (continuousOn_const.mul (hF.joint i)).mul (hG.joint (n-i))
    · intro p hp
      exact hid n p.1 hp.1 p.2

lemma BoundedSmoothFamily.heat_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.joint 0) hC hb a x

end SKValue

end

end OAI
