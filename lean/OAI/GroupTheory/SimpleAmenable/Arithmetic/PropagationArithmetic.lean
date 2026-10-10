import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PropagationArithmetic

@[simp] theorem endpointLabel_add (z w : CutRing) :
    endpointLabel (z+w) = endpointLabel z + endpointLabel w := rfl

@[simp] theorem endpointLabel_sub (z w : CutRing) :
    endpointLabel (z-w) = endpointLabel z - endpointLabel w := rfl

@[simp] theorem endpointLabel_intCast (k : ℤ) : endpointLabel (k : CutRing) = 0 := rfl

theorem endpointLabel_mul (l d : CutRing) :
    (endpointLabel (l*d) : ℝ) = conjugate l * (endpointLabel d : ℝ) +
      (endpointLabel l : ℝ) * ordinary d := by
  simp only [endpointLabel, QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul,
    Int.cast_one, ordinary_apply, conjugate_apply]
  rw [← Real.one_sub_goldenConj]
  ring

theorem endpointLabel_mul_bound (l d : CutRing) {N D : ℝ}
    (hq : |(endpointLabel d : ℝ)| ≤ N) (hd : |ordinary d| ≤ D) :
    |(endpointLabel (l*d) : ℝ)| ≤ |conjugate l| * N + |(endpointLabel l : ℝ)| * D := by
  rw [endpointLabel_mul]
  calc
    _ ≤ |conjugate l * (endpointLabel d : ℝ)| +
        |(endpointLabel l : ℝ) * ordinary d| := abs_add_le _ _
    _ = |conjugate l| * |(endpointLabel d : ℝ)| +
        |(endpointLabel l : ℝ)| * |ordinary d| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by gcongr

theorem exists_source_slope (c C : ℝ) (hc : 0 < c) :
    ∃ a : ℕ, 0 < a ∧
      ordinary (cutTau^a)*c > 1000*(C+1) ∧
      |conjugate (cutTau^a)| < 1/1000 := by
  obtain ⟨a,ha⟩ := pow_unbounded_of_one_lt (1000*(C+1)/c) Real.one_lt_goldenRatio
  have hconj : |Real.goldenConj| < 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  obtain ⟨b,hb⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1/1000) hconj
  refine ⟨max a b + 1, by omega, ?_, ?_⟩
  · have hp : Real.goldenRatio^a ≤ Real.goldenRatio^(max a b + 1) :=
      pow_le_pow_right₀ Real.one_lt_goldenRatio.le (by omega)
    simpa only [map_pow, ordinary_cutTau] using
      (div_lt_iff₀ hc).mp (lt_of_lt_of_le ha hp)
  · simp only [map_pow, conjugate_cutTau, abs_pow]
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (abs_nonneg _) hconj.le (by omega)) hb

theorem exists_source_slope_explicit :
    ∃ a : ℕ, 0 < a ∧ ordinary (cutTau^a)*(1/4) > 1000*(100+1) ∧
      |conjugate (cutTau^a)| < 1/1000 :=
  exists_source_slope (1/4) 100 (by norm_num)

end PropagationArithmetic

section BoundedOneDimensionalOrdering

variable {α : Type*}

private theorem real_list_sum_nonpos {l : List ℝ} (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    exact add_nonpos (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem exists_bounded_step_order (v : α → ℝ) (xs : List α)
    {L U δ x : ℝ} (hLU : L ≤ U) (_hδ : 0 ≤ δ)
    (hstep : ∀ t ∈ xs, |v t| ≤ δ)
    (hx : L-δ ≤ x ∧ x ≤ U+δ)
    (hy : L ≤ x+(xs.map v).sum ∧ x+(xs.map v).sum ≤ U) :
    ∃ ys : List α, ys.Perm xs ∧
      ∀ n : ℕ, L-δ ≤ x+((ys.take n).map v).sum ∧
        x+((ys.take n).map v).sum ≤ U+δ := by
  classical
  induction hn : xs.length using Nat.strong_induction_on generalizing xs x with
  | h n ih =>
    by_cases hnil : xs = []
    · subst xs
      exact ⟨[],List.Perm.refl _,fun _ => by simpa using hx⟩
    have hcons : ∃ t, t ∈ xs := List.exists_mem_of_ne_nil xs hnil
    have hchoose : ∃ t ∈ xs, L-δ ≤ x+v t ∧ x+v t ≤ U+δ := by
      by_cases hlow : x < L
      · have hp : ∃ t ∈ xs, 0 < v t := by
          by_contra! hp
          have hz : (xs.map v).sum ≤ 0 := real_list_sum_nonpos (by
            intro r hr
            obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
            exact hp t ht)
          linarith [hy.1]
        obtain ⟨t,ht,hpos⟩ := hp
        refine ⟨t,ht,by linarith [hx.1],?_⟩
        linarith [(abs_le.mp (hstep t ht)).2]
      · by_cases hhigh : U < x
        · have hp : ∃ t ∈ xs, v t < 0 := by
            by_contra! hp
            have hz : 0 ≤ (xs.map v).sum := List.sum_nonneg (by
              intro r hr
              obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
              exact hp t ht)
            linarith [hy.2]
          obtain ⟨t,ht,hneg⟩ := hp
          refine ⟨t,ht,?_,by linarith [hx.2]⟩
          linarith [(abs_le.mp (hstep t ht)).1]
        · obtain ⟨t,ht⟩ := hcons
          refine ⟨t,ht,?_,?_⟩ <;> linarith [abs_le.mp (hstep t ht)]
    obtain ⟨t,ht,htx⟩ := hchoose
    have hperm : (t :: xs.erase t).Perm xs := (List.perm_cons_erase ht).symm
    have he : v t + ((xs.erase t).map v).sum = (xs.map v).sum := by
      have := (hperm.map v).sum_eq
      simpa using this
    have hlen : (xs.erase t).length < n := by
      rw [← hn]
      rw [List.length_erase_of_mem ht]
      have : 0 < xs.length := List.length_pos_iff.mpr hnil
      omega
    obtain ⟨ys,hys,hbounds⟩ := ih _ hlen (xs.erase t) (x := x+v t)
      (fun s hs => hstep s (List.mem_of_mem_erase hs)) htx
      (by constructor <;> linarith [hy.1,hy.2]) rfl
    refine ⟨t::ys,(List.Perm.cons t hys).trans hperm,?_⟩
    intro k
    cases k with
    | zero => simpa using hx
    | succ k => simpa only [List.take_succ_cons,List.map_cons,List.sum_cons,add_assoc]
        using hbounds k

theorem exists_step_order_near_segment (v : α → ℝ) (xs : List α) {δ : ℝ}
    (hδ : 0 ≤ δ) (hstep : ∀ t ∈ xs, |v t| ≤ δ) :
    ∃ ys : List α, ys.Perm xs ∧ ∀ n : ℕ,
      min 0 (xs.map v).sum - δ ≤ ((ys.take n).map v).sum ∧
      ((ys.take n).map v).sum ≤ max 0 (xs.map v).sum + δ := by
  obtain ⟨ys,hy,hb⟩ := exists_bounded_step_order v xs
    (L := min 0 (xs.map v).sum) (U := max 0 (xs.map v).sum) (x := 0)
    min_le_max hδ hstep
    ⟨by linarith [min_le_left 0 (xs.map v).sum],
     by linarith [le_max_left 0 (xs.map v).sum]⟩
    ⟨by simp, by simp⟩
  exact ⟨ys,hy,fun n => by simpa using hb n⟩

end BoundedOneDimensionalOrdering

end SimpleAmenable
end
end

end OAI
