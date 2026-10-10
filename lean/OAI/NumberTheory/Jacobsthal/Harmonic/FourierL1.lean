import OAI.NumberTheory.Jacobsthal.Estimates.UnitCyclicBounds
import OAI.NumberTheory.Jacobsthal.Partitions.IntervalHyperbolaAdapter

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier
attribute [local instance] Classical.decEq

theorem intervalWeight_l1 (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    (∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
      ‖intervalWeight N h x y lc rc T a‖) ≤
      (2*harmonicConstant)*(N : ℝ)*Real.log (2*(N : ℝ)) := by
  have hu : IsUnit (-(T : ZMod N)) := ((ZMod.isUnit_iff_coprime T N).mpr hTN).neg
  obtain ⟨u,hu⟩ := hu
  have he (h : ZMod N) : h*(u : ZMod N) = -h*(T : ZMod N) := by rw [hu]; ring
  calc
    _ ≤ ∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
        (N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [he]
      exact norm_intervalWeight_le_of_coprime N h (Finset.mem_filter.mp hh).2 x y lc rc T a hT hTN
    _ ≤ ∑ h : ZMod N,(N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (N : ℝ)*∑ h : ZMod N,1/(cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ (N : ℝ)*((2*harmonicConstant)*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (unit_cyclic_inverse_sum_le N u) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem intervalWeight_gcd_l1 (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    (∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
      ‖intervalWeight N h x y lc rc T a‖*Real.sqrt (Nat.gcd h.val N)) ≤
      (2*harmonicConstant)*(N : ℝ)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have hu : IsUnit (-(T : ZMod N)) := ((ZMod.isUnit_iff_coprime T N).mpr hTN).neg
  obtain ⟨u,hu⟩ := hu
  have he (h : ZMod N) : h*(u : ZMod N) = -h*(T : ZMod N) := by rw [hu]; ring
  calc
    _ ≤ ∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
        ((N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ))*Real.sqrt (Nat.gcd h.val N) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (norm_intervalWeight_le_of_coprime N h (Finset.mem_filter.mp hh).2 x y lc rc T a hT hTN)
        (Real.sqrt_nonneg _)
    _ ≤ ∑ h : ZMod N,
        ((N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ))*Real.sqrt (Nat.gcd h.val N) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (N : ℝ)*∑ h : ZMod N,Real.sqrt (Nat.gcd h.val N)/
        (cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ (N : ℝ)*((2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (unit_sqrt_gcd_cyclic_sum_le N u) (Nat.cast_nonneg _)
    _ = _ := by ring

end ErdosHyperbola

end

end Erdos970

end OAI
