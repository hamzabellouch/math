import OAI.NumberTheory.CubicMoment.Estimates.HuxleyLiftedPacking

namespace OAI

/-! Square-grid packing of the actual lifted reduced fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma same_floor_abs_sub_lt_one {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x-y| < 1 := by
  have hx := Int.floor_le x
  have hy := Int.floor_le y
  have hx' := Int.lt_floor_add_one x
  have hy' := Int.lt_floor_add_one y
  rw [h] at hx hx'
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

def huxleyGrid (Q : ℝ) (z x : ℂ) : ℤ × ℤ :=
  (⌊6*Q*(x-z).re⌋,⌊6*Q*(x-z).im⌋)

lemma huxleyGrid_close {Q : ℝ} (hQ : 0 < Q) {z x y : ℂ}
    (h : huxleyGrid Q z x = huxleyGrid Q z y) :
    ‖x-y‖ < 1/(3*Q) := by
  have h6 : 0 < 6*Q := by positivity
  have hcoord {a b : ℝ} (he : ⌊6*Q*a⌋ = ⌊6*Q*b⌋) : |a-b| < 1/(6*Q) := by
    have hh := same_floor_abs_sub_lt_one he
    rw [show 6*Q*a-6*Q*b = (6*Q)*(a-b) by ring,abs_mul,abs_of_pos h6] at hh
    exact (lt_div_iff₀ h6).mpr (by simpa only [mul_comm] using hh)
  have hre := hcoord (congrArg Prod.fst h)
  have him := hcoord (congrArg Prod.snd h)
  simp only [Complex.sub_re,Complex.sub_im,sub_sub_sub_cancel_right] at hre him
  have ht := Complex.norm_le_abs_re_add_abs_im (x-y)
  simp only [Complex.sub_re,Complex.sub_im] at ht
  have he : 1/(6*Q)+1/(6*Q) = 1/(3*Q) := by ring
  linarith

lemma huxleyGrid_fiber_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) (k : ℤ × ℤ) :
    ((S.filter (fun i => huxleyGrid Q z i.frequency = k)).card:ℝ) ≤ 18 := by
  let T := S.filter (fun i => huxleyGrid Q z i.frequency = k)
  by_cases hT : T.Nonempty
  · obtain ⟨i0,hi0⟩ := hT
    apply huxleyLift_local_count Q hQ i0.frequency T
    · intro i hi
      exact hred i (Finset.mem_filter.mp hi).1
    · intro i hi
      apply huxleyGrid_close hQ
      exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi0).2.symm
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change (T.card:ℝ) ≤ _
    simp [he]

lemma huxleyLift_count_of_grid_mem (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    (S : Finset HuxleyLift) (T : Finset (ℤ × ℤ))
    (hred : ∀ i ∈ S, i.reduced Q)
    (hT : ∀ i ∈ S, huxleyGrid Q z i.frequency ∈ T) :
    (S.card:ℝ) ≤ 18*T.card := by
  have he := Finset.card_eq_sum_card_fiberwise hT
  have he' : (S.card:ℝ) = ∑ k ∈ T,
      ((S.filter (fun i => huxleyGrid Q z i.frequency = k)).card:ℝ) := by
    exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ k ∈ T, (18:ℝ) := Finset.sum_le_sum (fun k hk => huxleyGrid_fiber_count Q hQ z S hred k)
    _ = _ := by simp [mul_comm]

lemma floor_scaled_in_box {A R x : ℝ} (hA : 0 ≤ A)
    (hx : |x| ≤ R) :
    ⌊A*x⌋ ∈ Finset.Icc (-⌈A*R⌉-1) (⌈A*R⌉+1) := by
  have hx' := abs_le.mp hx
  have hlo := mul_le_mul_of_nonneg_left hx'.1 hA
  have hhi := mul_le_mul_of_nonneg_left hx'.2 hA
  have hc := Int.le_ceil (A*R)
  have hf := Int.floor_le (A*x)
  have hf' := Int.lt_floor_add_one (A*x)
  apply Finset.mem_Icc.mpr
  constructor
  · have hh : ((-⌈A*R⌉-1:ℤ):ℝ) ≤ (⌊A*x⌋:ℝ) := by push_cast; nlinarith
    exact_mod_cast hh
  · have hh : (⌊A*x⌋:ℝ) ≤ ((⌈A*R⌉+1:ℤ):ℝ) := by push_cast; nlinarith
    exact_mod_cast hh


/-- Uniform disk count for all reduced residue fractions and their translates. -/
lemma huxleyLift_disk_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset HuxleyLift) (hred : ∀ i ∈ S, i.reduced Q)
    (hball : ∀ i ∈ S, ‖i.frequency-z‖ ≤ R) :
    (S.card:ℝ) ≤ 6000*(1+Q^2*R^2) := by
  let B : ℤ := ⌈6*Q*R⌉+1
  let T := (Finset.Icc (-B) B).product (Finset.Icc (-B) B)
  have hlow : -B = -⌈(6*Q)*R⌉-1 := by dsimp [B]; ring
  have hmem : ∀ i ∈ S, huxleyGrid Q z i.frequency ∈ T := by
    intro i hi
    apply Finset.mem_product.mpr
    constructor
    · change ⌊6*Q*(i.frequency-z).re⌋ ∈ Finset.Icc (-B) B
      rw [hlow]
      exact floor_scaled_in_box (by positivity)
        ((Complex.abs_re_le_norm _).trans (hball i hi))
    · change ⌊6*Q*(i.frequency-z).im⌋ ∈ Finset.Icc (-B) B
      rw [hlow]
      exact floor_scaled_in_box (by positivity)
        ((Complex.abs_im_le_norm _).trans (hball i hi))
  have hc := huxleyLift_count_of_grid_mem Q hQ z S T hred hmem
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hc0 : (0:ℤ) ≤ ⌈6*Q*R⌉ := Int.ceil_nonneg (by positivity)
    omega
  have hcard : ((Finset.Icc (-B) B).card:ℝ) = 2*(B:ℝ)+1 := by
    rw [Int.card_Icc]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  have hT : (T.card:ℝ) = (2*(B:ℝ)+1)^2 := by
    dsimp [T]
    rw [Finset.card_product,Nat.cast_mul,hcard]
    ring
  rw [hT] at hc
  have hB : (B:ℝ) ≤ 6*Q*R+2 := by
    have hh := Int.ceil_lt_add_one (6*Q*R)
    dsimp [B]
    push_cast
    linarith
  have hsz : 0 ≤ 2*(B:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*B+1 by omega)
  have hsquare : (2*(B:ℝ)+1)^2 ≤ (12*(Q*R)+5)^2 := by
    apply (sq_le_sq₀ hsz (by positivity)).mpr
    linarith
  have hpoly : 18*(12*(Q*R)+5)^2 ≤ 6000*(1+Q^2*R^2) := by
    nlinarith [sq_nonneg (12*(Q*R)-5),sq_nonneg (Q*R)]
  exact hc.trans ((mul_le_mul_of_nonneg_left hsquare (by norm_num)).trans hpoly)

end CubicFirstMoment

end

end OAI
