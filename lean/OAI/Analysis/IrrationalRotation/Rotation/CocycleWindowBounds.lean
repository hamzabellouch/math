import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Rotation.FiniteSupportCocycle
import OAI.Analysis.IrrationalRotation.Model.ConditionalConvolution

namespace OAI

noncomputable section
open scoped BigOperators
open Set

namespace Invariant233.ProductCocycle

theorem cocycleVersion_le_one_of_nonneg_time {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (k : ℤ) (hk : 0 ≤ k) (x : Space I) : cocycleVersion θ c k x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  have hfloor : (0 : ℤ) ≤ ⌊representative (x i) + (k : ℝ) * θ i⌋ :=
    Int.floor_nonneg.mpr (add_nonneg (representative_mem_Ico (x i)).1
      (mul_nonneg (by exact_mod_cast hk) (hθ i)))
  exact_mod_cast hfloor

theorem one_le_cocycleVersion_of_nonpos_time {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (k : ℤ) (hk : k ≤ 0) (x : Space I) : 1 ≤ cocycleVersion θ c k x := by
  apply Real.one_le_exp_iff.mpr
  apply neg_nonneg.mpr
  apply tsum_nonpos
  intro i
  apply mul_nonpos_of_nonneg_of_nonpos (hc i)
  have hfloor : ⌊representative (x i) + (k : ℝ) * θ i⌋ ≤ (0 : ℤ) := by
    calc
      _ ≤ ⌊representative (x i)⌋ := Int.floor_mono
        (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg
          (by exact_mod_cast hk) (hθ i)))
      _ = 0 := Int.floor_eq_zero_iff.mpr (representative_mem_Ico (x i))
  exact_mod_cast hfloor

theorem endpoint_floors_eq_zero {x y θ : ℝ} {K v : ℕ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Ico (0 : ℝ) 1)
    (hθ : 0 ≤ θ) (hv : v ≤ K)
    (hxl : x < 1 - (K : ℝ) * θ) (hyl : (K : ℝ) * θ ≤ y) :
    ⌊x + (v : ℝ) * θ⌋ = 0 ∧ ⌊y - (v : ℝ) * θ⌋ = 0 := by
  have hvθ : (v : ℝ) * θ ≤ (K : ℝ) * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hv) hθ
  have hvθ0 : 0 ≤ (v : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ
  constructor
  · apply Int.floor_eq_zero_iff.mpr
    constructor <;> linarith [hx.1]
  · apply Int.floor_eq_zero_iff.mpr
    constructor <;> linarith [hy.2]

theorem cocycle_window_bounds_of_endpoint_margins {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (s : Finset I) (K v : ℕ) (hv : v ≤ K)
    (x y : Space I)
    (hmargin : ∀ i ∉ s, representative (x i) < 1 - (K : ℝ) * θ i ∧
      (K : ℝ) * θ i ≤ representative (y i)) :
    1 / cocycleVersion θ c (v : ℤ) x ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
      cocycleVersion θ c (-(v : ℤ)) y ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  have hzero (i : I) (hi : i ∉ s) := endpoint_floors_eq_zero
    (representative_mem_Ico (x i)) (representative_mem_Ico (y i))
    (hθ i).1 hv (hmargin i hi).1 (hmargin i hi).2
  have hxsum : cocycleVersion θ c (v : ℤ) x =
      Real.exp (-∑ i ∈ s, c i * (⌊representative (x i) + (v : ℝ) * θ i⌋ : ℝ)) := by
    apply cocycleVersion_eq_finite_sum
    intro i hi
    simpa only [Int.cast_natCast] using (hzero i hi).1
  have hysum : cocycleVersion θ c (-(v : ℤ)) y =
      Real.exp (-∑ i ∈ s, c i * (⌊representative (y i) - (v : ℝ) * θ i⌋ : ℝ)) := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg] using
      cocycleVersion_eq_finite_sum θ c (-(v : ℤ)) y s (fun i hi => by
        simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg]
          using (hzero i hi).2)
  have htime (i : I) : (v : ℝ) * θ i ≤ K := by
    calc
      _ ≤ (v : ℝ) * 1 := mul_le_mul_of_nonneg_left (hθ i).2 (Nat.cast_nonneg _)
      _ ≤ K := by simpa only [mul_one] using (show (v : ℝ) ≤ K by exact_mod_cast hv)
  have hxbound : (∑ i ∈ s, c i * (⌊representative (x i) + (v : ℝ) * θ i⌋ : ℝ)) ≤
      ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hf := Int.floor_le (representative (x i) + (v : ℝ) * θ i)
    have hcoord : (⌊representative (x i) + (v : ℝ) * θ i⌋ : ℝ) ≤ (K : ℝ) + 1 := by
      linarith [(representative_mem_Ico (x i)).2, htime i]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcoord (hc i)
  have hybound : -(∑ i ∈ s, c i * (⌊representative (y i) - (v : ℝ) * θ i⌋ : ℝ)) ≤
      ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hf := Int.lt_floor_add_one (representative (y i) - (v : ℝ) * θ i)
    have hcoord : -(⌊representative (y i) - (v : ℝ) * θ i⌋ : ℝ) ≤ (K : ℝ) + 1 := by
      linarith [(representative_mem_Ico (y i)).1, htime i]
    simpa only [mul_neg, mul_comm] using mul_le_mul_of_nonneg_left hcoord (hc i)
  constructor
  · rw [hxsum, one_div, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hxbound
  · rw [hysum]
    exact Real.exp_le_exp.mpr hybound

theorem signed_cocycle_window_bounds {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (s : Finset I) (K : ℕ)
    (x y : Space I)
    (hmargin : ∀ i ∉ s, representative (x i) < 1 - (K : ℝ) * θ i ∧
      (K : ℝ) * θ i ≤ representative (y i))
    (k : ℤ) (hk : |k| ≤ (K : ℤ)) :
    1 / cocycleVersion θ c k x ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
      cocycleVersion θ c (-k) y ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  by_cases hk0 : 0 ≤ k
  · have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    have hnat : k.toNat ≤ K := by
      have hk' : k ≤ (K : ℤ) := (le_abs_self k).trans hk
      exact_mod_cast (show (k.toNat : ℤ) ≤ (K : ℤ) by simpa only [hcast] using hk')
    simpa only [hcast] using cocycle_window_bounds_of_endpoint_margins
      θ c hθ hc s K k.toNat hnat x y hmargin
  · have hneg : k ≤ 0 := (lt_of_not_ge hk0).le
    have hD : 1 ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hc i))
    constructor
    · apply le_trans _ hD
      exact (div_le_one (cocycleVersion_pos θ c k x)).mpr
        (one_le_cocycleVersion_of_nonpos_time θ c (fun i => (hθ i).1) hc k hneg x)
    · apply le_trans _ hD
      exact cocycleVersion_le_one_of_nonneg_time θ c (fun i => (hθ i).1) hc (-k)
        (by omega) y

theorem endpoint_margins_of_scale {x y θ N : ℝ} (K : ℕ)
    (hθ : θ ≤ 2 / N) (hx : x < 1 - 2 * (K : ℝ) / N)
    (hy : 2 * (K : ℝ) / N ≤ y) :
    x < 1 - (K : ℝ) * θ ∧ (K : ℝ) * θ ≤ y := by
  have hmul : (K : ℝ) * θ ≤ 2 * (K : ℝ) / N := by
    calc
      _ ≤ (K : ℝ) * (2 / N) := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg _)
      _ = _ := by ring
  constructor <;> linarith

theorem reweighted_coefficient_bounds {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (s : Finset I) (K : ℕ)
    (x y : Space I)
    (hmargin : ∀ i ∉ s, representative (x i) < 1 - (K : ℝ) * θ i ∧
      (K : ℝ) * θ i ≤ representative (y i))
    (ξ γ : ℤ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (hγ : ∀ k, ‖γ k‖ ≤ 1)
    (k : ℤ) (hk : |k| ≤ (K : ℤ)) :
    ‖ξ k / (cocycleVersion θ c k x : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
      ‖(cocycleVersion θ c (-k) y : ℂ) * star (γ (-k))‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hleft, hright⟩ := signed_cocycle_window_bounds θ c hθ hc s K x y hmargin k hk
  have hxpos := cocycleVersion_pos θ c k x
  have hypos := cocycleVersion_pos θ c (-k) y
  constructor
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    exact ((div_le_div_iff_of_pos_right hxpos).mpr (hξ k)).trans hleft
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos, norm_star]
    calc
      _ ≤ cocycleVersion θ c (-k) y * 1 := mul_le_mul_of_nonneg_left (hγ (-k)) hypos.le
      _ ≤ _ := by simpa only [mul_one] using hright

end Invariant233.ProductCocycle

open scoped BigOperators ComplexConjugate lp
namespace Invariant233.CocycleWindowBounds

theorem floor_forward_eq_zero {x α v K : ℝ}
    (hx : 0 ≤ x) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : x + K * α < 1) : ⌊x + v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_right hvK hα
    linarith

theorem floor_backward_eq_zero {y α v K : ℝ}
    (hy : y < 1) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : K * α ≤ y) : ⌊y - v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hvK hα).trans hexclude)
  · exact (sub_le_self y (mul_nonneg hv hα)).trans_lt hy

theorem floor_forward_le {x α v : ℝ} (K : ℕ)
    (hx : x < 1) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    (⌊x + v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.floor_le (x + v * α)]

theorem neg_floor_backward_le {y α v : ℝ} (K : ℕ)
    (hy : 0 ≤ y) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    -(⌊y - v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.lt_floor_add_one (y - v * α)]

theorem tsum_weighted_le_prefix {I : Type*} (s : Finset I)
    (c a : I → ℝ) (B : ℝ) (hc : ∀ i, 0 ≤ c i)
    (hout : ∀ i ∉ s, a i = 0) (hbound : ∀ i ∈ s, a i ≤ B) :
    (∑' i, c i * a i) ≤ B * ∑ i ∈ s, c i := by
  rw [tsum_eq_sum (s := s) (fun i hi => by rw [hout i hi]; simp)]
  calc
    (∑ i ∈ s, c i * a i) ≤ ∑ i ∈ s, c i * B :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbound i hi) (hc i))
    _ = B * ∑ i ∈ s, c i := by rw [← Finset.sum_mul]; ring

theorem signed_floor_sums_le {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    (∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i ∧
    -(∑' i, c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
  have hcost : 0 ≤ ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hc i)
  rcases le_or_gt 0 v with hv0 | hv0
  · have hv0' : (0 : ℝ) ≤ v := by exact_mod_cast hv0
    have hvK : (v : ℝ) ≤ K := by exact_mod_cast (le_abs_self v).trans hv
    constructor
    · apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_forward_eq_zero (hx i).1 (hα i).1 hv0' hvK (hleft i hi)]
        simp
      · intro i _
        exact floor_forward_le K (hx i).2 (hα i).2 hv0' hvK
    · rw [← tsum_neg]
      have heq : (fun i => -(c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ))) =
          (fun i => c i * -(⌊y i - (v : ℝ) * α i⌋ : ℝ)) := by
        funext i; ring
      rw [heq]
      apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_backward_eq_zero (hy i).2 (hα i).1 hv0' hvK (hright i hi)]
        simp
      · intro i _
        exact neg_floor_backward_le K (hy i).1 (hα i).2 hv0' hvK
  · have hv0' : (v : ℝ) ≤ 0 := by exact_mod_cast hv0.le
    constructor
    · apply le_trans (tsum_nonpos fun i => ?_) hcost
      apply mul_nonpos_of_nonneg_of_nonpos (hc i)
      have hf : ⌊x i + (v : ℝ) * α i⌋ ≤ 0 := by
        apply Int.floor_le_iff.mpr
        norm_num
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1)).trans_lt
          (hx i).2
      exact_mod_cast hf
    · apply le_trans (neg_nonpos.mpr (tsum_nonneg fun i => ?_)) hcost
      apply mul_nonneg (hc i)
      have hf : (0 : ℤ) ≤ ⌊y i - (v : ℝ) * α i⌋ := by
        apply Int.floor_nonneg.mpr
        exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1).trans (hy i).1)
      exact_mod_cast hf

theorem cocycle_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    1 / Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    signed_floor_sums_le s x y α c K hx hy hα hc hleft hright v hv
  constructor
  · simpa only [Real.exp_neg, one_div, inv_inv] using Real.exp_le_exp.mpr hforward
  · simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using
      Real.exp_le_exp.mpr hbackward

theorem coefficient_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    ‖ξ v / (Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    ‖(Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) : ℂ) *
        conj (γ (-v))‖ ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    cocycle_bounds s x y α c K hx hy hα hc hleft hright v hv
  have hξv : ‖ξ v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) ξ v).trans hξ
  have hγv : ‖γ (-v)‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) γ (-v)).trans hγ
  constructor
  · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (div_le_div_of_nonneg_right hξv (Real.exp_pos _).le).trans hforward
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_conj]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hγv).trans hbackward

end Invariant233.CocycleWindowBounds

end

end OAI
