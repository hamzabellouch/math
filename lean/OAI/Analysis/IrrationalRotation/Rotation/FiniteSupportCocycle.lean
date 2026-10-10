import OAI.Analysis.IrrationalRotation.Rotation.FloorCocycle
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

theorem exp_tsum_floor_zero {I : Type*} (x c : I → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑' i, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hf (i : I) : ⌊x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hx i)
  simp [hf]

theorem exp_tsum_floor_ratio_le_one {I : Type*} (x y θ c : I → ℝ) (k : ℤ)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + (k : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) ≤ 1 := by
  rw [← Real.exp_sub, Real.exp_le_one_iff]
  have hsum : (∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ)) ≤
      ∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ) := by
    apply Summable.tsum_le_tsum _ (summable_weighted_int c hx) (summable_weighted_int c hy)
    intro i
    apply mul_le_mul_of_nonneg_left _ (hc i)
    exact Int.cast_le.mpr (Int.floor_mono (add_le_add_left (hxy i) ((k : ℝ) * θ i)))
  linarith

theorem exp_tsum_floor_ratio_eq_crossings {I : Type*} (x y t c : I → ℝ)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + t i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + t i⌋)) :
    Real.exp (-(∑' i, c i * (⌊y i + t i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + t i⌋ : ℝ))) =
      Real.exp (-(∑' i, if x i < 1 - Int.fract (t i) ∧
        1 - Int.fract (t i) ≤ y i then c i else 0)) := by
  classical
  have hcoord (i : I) :
      c i * (⌊y i + t i⌋ : ℝ) - c i * (⌊x i + t i⌋ : ℝ) =
        if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0 := by
    rw [← mul_sub, ← Int.cast_sub,
      FloorCocycle.floor_sub_eq_crossing (hx01 i).1 (hx01 i).2
        (hy01 i).1 (hy01 i).2 (hxy i)]
    split_ifs <;> simp
  rw [← Real.exp_sub]
  congr 1
  rw [show -(∑' i, c i * (⌊y i + t i⌋ : ℝ)) -
      -(∑' i, c i * (⌊x i + t i⌋ : ℝ)) =
      -((∑' i, c i * (⌊y i + t i⌋ : ℝ)) -
        ∑' i, c i * (⌊x i + t i⌋ : ℝ)) by ring]
  rw [← (summable_weighted_int c hy).tsum_sub (summable_weighted_int c hx)]
  congr 1
  exact tsum_congr hcoord

theorem exp_tsum_floor_ratio_le_finite_crossings {I : Type*}
    (x y t c : I → ℝ) (s : Finset I)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + t i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + t i⌋))
    (hcross : ∀ i ∈ s, x i < 1 - Int.fract (t i) ∧
      1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑' i, c i * (⌊y i + t i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + t i⌋ : ℝ))) ≤
      Real.exp (-∑ i ∈ s, c i) := by
  classical
  let d : I → ℝ := fun i ↦
    if x i < 1 - Int.fract (t i) ∧ 1 - Int.fract (t i) ≤ y i then c i else 0
  have hd_eq (i : I) :
      c i * (⌊y i + t i⌋ : ℝ) - c i * (⌊x i + t i⌋ : ℝ) = d i := by
    rw [← mul_sub, ← Int.cast_sub,
      FloorCocycle.floor_sub_eq_crossing (hx01 i).1 (hx01 i).2
        (hy01 i).1 (hy01 i).2 (hxy i)]
    dsimp [d]
    split_ifs <;> simp
  have hd : Summable d :=
    ((summable_weighted_int c hy).sub (summable_weighted_int c hx)).congr hd_eq
  have hd_nonneg (i : I) : 0 ≤ d i := by
    dsimp [d]
    split_ifs <;> simp_all only [le_refl]
  have hbound : (∑ i ∈ s, c i) ≤ ∑' i, d i := by
    calc
      (∑ i ∈ s, c i) = ∑ i ∈ s, d i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [d, ite_eq_left (hcross i hi)]
      _ ≤ ∑' i, d i := hd.sum_le_tsum s (fun i _ ↦ hd_nonneg i)
  rw [exp_tsum_floor_ratio_eq_crossings x y t c hx01 hy01 hxy hx hy]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg hbound

end Invariant233.FiniteSupportCocycle

end OAI
