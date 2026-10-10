import OAI.Analysis.OInfinity.EvenCARRelations

namespace OAI

/-! # Geometric modes for a finite even-row shift

The coefficient calculation is shared with the binary case, but the CAR
family and shift here come from the actual given finite even row.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] {n : ℕ}

def evenGeometricMode (r : Fin 2 × Fin n → E) (start L : ℕ) (ζ : ℂ) : E :=
  carSynthesis (fun i : Fin L => evenRowCAR r (start + i.val))
    (fun i => carModeCoefficient L ζ i.val)

def evenGeometricShift (r : Fin 2 × Fin n → E) (start L : ℕ) (ζ : ℂ) : E :=
  carSynthesis (fun i : Fin L => evenRowCAR r (start + i.val + 1))
    (fun i => carModeCoefficient L ζ i.val)

lemma evenGeometricShift_eq (r : Fin 2 × Fin n → E) (start L : ℕ) (ζ : ℂ) :
    evenGeometricShift r start L ζ = evenGeometricMode r (start + 1) L ζ := by
  unfold evenGeometricShift evenGeometricMode carSynthesis
  apply Finset.sum_congr rfl
  intro i _
  change carModeCoefficient L ζ i.val • evenRowCAR r (start + i.val + 1) =
    carModeCoefficient L ζ i.val • evenRowCAR r (start + 1 + i.val)
  have hidx : start + i.val + 1 = start + 1 + i.val := by omega
  rw [hidx]

lemma evenGeometricMode_as_synthesis (r : Fin 2 × Fin n → E) (start L : ℕ) (ζ : ℂ) :
    evenGeometricMode r start L ζ =
      carSynthesis (fun i : Fin (L + 1) => evenRowCAR r (start + i.val))
        (carModeInitialCoefficient L ζ) := by
  unfold evenGeometricMode carSynthesis
  rw [Fin.sum_univ_castSucc]
  simp only [carModeInitialCoefficient, Fin.val_castSucc, Fin.isLt, ite_true,
    Fin.val_last, lt_self_iff_false, ite_false, zero_smul, add_zero]

lemma evenGeometricShift_as_synthesis (r : Fin 2 × Fin n → E) (start L : ℕ) (ζ : ℂ) :
    evenGeometricShift r start L ζ =
      carSynthesis (fun i : Fin (L + 1) => evenRowCAR r (start + i.val))
        (carModeShiftCoefficient L ζ) := by
  unfold evenGeometricShift carSynthesis
  rw [Fin.sum_univ_succ]
  simp only [carModeShiftCoefficient, Fin.val_zero, ite_true, zero_smul, zero_add,
    Fin.val_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.add_assoc]

variable (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

include hqstar hqq hrow hsum in
lemma evenGeometricMode_support (start L : ℕ) (ζ : ℂ) :
    q * evenGeometricMode r start L ζ = evenGeometricMode r start L ζ ∧
      evenGeometricMode r start L ζ * q = evenGeometricMode r start L ζ := by
  apply carSynthesis_support
  · intro i
    exact (evenRowCAR_support q r hqstar hqq hrow hsum _).1
  · intro i
    exact (evenRowCAR_support q r hqstar hqq hrow hsum _).2

include hqstar hqq hrow hsum in
lemma evenGeometricMode_gram (start L : ℕ) (hL : 0 < L) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    star (evenGeometricMode r start L ζ) * evenGeometricMode r start L ζ +
      evenGeometricMode r start L ζ * star (evenGeometricMode r start L ζ) = q := by
  have hf : Function.Injective (fun i : Fin L => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have hcar (i j : Fin L) :
      star (evenRowCAR r (start + i.val)) * evenRowCAR r (start + j.val) +
        evenRowCAR r (start + j.val) * star (evenRowCAR r (start + i.val)) =
          if i = j then q else 0 := by
    simpa only [hf.eq_iff] using
      evenRowCAR_star_anticommute q r hqstar hqq hrow hsum (start + i.val) (start + j.val)
  have h := carSynthesis_star_anticommute q
    (fun i : Fin L => evenRowCAR r (start + i.val)) hcar
    (fun i => carModeCoefficient L ζ i.val) (fun i => carModeCoefficient L ζ i.val)
  simpa only [evenGeometricMode, carModeCoefficient_inner_self L hL ζ hζ, one_smul] using h

include hqstar hqq hrow hsum in
lemma evenGeometricMode_square_zero (start L : ℕ) (ζ : ℂ) :
    evenGeometricMode r start L ζ * evenGeometricMode r start L ζ = 0 := by
  apply carSynthesis_square_zero
  intro i j
  exact evenRowCAR_anticommute q r hqstar hqq hrow hsum _ _

include hqstar hqq hrow hsum in
lemma evenGeometricMode_norm_le_one (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) : ‖evenGeometricMode r start L ζ‖ ≤ 1 := by
  have hf : Function.Injective (fun i : Fin L => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have h := evenRowCAR_synthesis_norm_sq_le q r hqstar hqq hrow hsum
    (fun i : Fin L => start + i.val) hf (fun i => carModeCoefficient L ζ i.val)
  rw [carModeCoefficient_norm_sq_sum L hL ζ hζ] at h
  change ‖evenGeometricMode r start L ζ‖ * ‖evenGeometricMode r start L ζ‖ ≤ 1 at h
  nlinarith [norm_nonneg (evenGeometricMode r start L ζ)]

include hqstar hqq hrow hsum in
lemma evenGeometricMode_shift_error (start L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖evenGeometricShift r start L ζ - ζ • evenGeometricMode r start L ζ‖ *
      ‖evenGeometricShift r start L ζ - ζ • evenGeometricMode r start L ζ‖ ≤
        2 / (L : ℝ) := by
  let x : Fin (L + 1) → E := fun i => evenRowCAR r (start + i.val)
  let c : Fin (L + 1) → ℂ := fun i =>
    carModeShiftCoefficient L ζ i - ζ * carModeInitialCoefficient L ζ i
  have hrepr : evenGeometricShift r start L ζ - ζ • evenGeometricMode r start L ζ =
      carSynthesis x c := by
    rw [evenGeometricShift_as_synthesis, evenGeometricMode_as_synthesis]
    simp only [x, c, carSynthesis, sub_smul, Finset.sum_sub_distrib,
      Finset.smul_sum, smul_smul]
  rw [hrepr]
  have hf : Function.Injective (fun i : Fin (L + 1) => start + i.val) := by
    intro i j h
    apply Fin.ext
    change start + i.val = start + j.val at h
    omega
  have h := evenRowCAR_synthesis_norm_sq_le q r hqstar hqq hrow hsum
    (fun i : Fin (L + 1) => start + i.val) hf c
  simpa only [x, c, carModeCoefficient_error_sq_sum L hL ζ hζ] using h

include hqstar hqq hrow hsum in
lemma evenGeometricMode_shift (start L : ℕ) (ζ : ℂ) :
    evenRowShift r (evenGeometricMode r start L ζ) =
      evenRowParity r * evenGeometricShift r start L ζ := by
  unfold evenGeometricMode evenGeometricShift carSynthesis
  rw [evenRowShift_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [evenRowShift_smul, evenRowCAR_shift_single q r hqstar hqq hrow hsum, mul_smul_comm]

include hqstar hqq hrow in
lemma evenGeometricMode_commute_parity (start L : ℕ) (hstart : 0 < start) (ζ : ℂ) :
    Commute (evenRowParity r) (evenGeometricMode r start L ζ) := by
  unfold evenGeometricMode carSynthesis
  apply Commute.sum_right
  intro i _
  have hk : start + i.val = (start + i.val - 1) + 1 := by omega
  have hc : Commute (evenRowParity r) (evenRowCAR r (start + i.val)) := by
    rw [hk]
    exact evenRowCAR_succ_commute_parity q r hqstar hqq hrow _
  change evenRowParity r * (carModeCoefficient L ζ i.val • evenRowCAR r (start + i.val)) =
    (carModeCoefficient L ζ i.val • evenRowCAR r (start + i.val)) * evenRowParity r
  rw [mul_smul_comm, smul_mul_assoc, hc.eq]

include hqstar hqq hrow in
lemma evenGeometricShift_commute_parity (start L : ℕ) (ζ : ℂ) :
    Commute (evenRowParity r) (evenGeometricShift r start L ζ) := by
  rw [evenGeometricShift_eq]
  exact evenGeometricMode_commute_parity q r hqstar hqq hrow _ _ (by omega) _

include hqstar hqq in
private lemma modeSymmetry_norm_le_one (c : E) (hcc : c * c = 0)
    (hgram : star c * c + c * star c = q) : ‖c + star c‖ ≤ 1 := by
  have hqnorm : ‖q‖ ≤ 1 := by
    have h : ‖star q * q‖ = ‖q‖ * ‖q‖ := CStarRing.norm_star_mul_self
    rw [hqstar, hqq] at h
    nlinarith [norm_nonneg q]
  have hss : star c * star c = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hcc
  have hu : star (c + star c) * (c + star c) = q := by
    simp only [star_add, star_star, add_mul, mul_add, hcc, hss, zero_add, add_zero]
    exact hgram
  have hn := congrArg norm hu
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (c + star c)]

def evenModeSymmetry (r : Fin 2 × Fin n → E) (base L : ℕ) : E :=
  evenGeometricMode r base L 1 + star (evenGeometricMode r base L 1)

def evenShiftSymmetry (r : Fin 2 × Fin n → E) (base L : ℕ) : E :=
  evenGeometricShift r base L 1 + star (evenGeometricShift r base L 1)

def evenEigenMode (r : Fin 2 × Fin n → E) (start base L : ℕ) (ζ : ℂ) : E :=
  evenGeometricMode r start L ζ * evenModeSymmetry r base L

include hqstar hqq hrow hsum in
lemma evenModeSymmetry_support (base L : ℕ) :
    q * evenModeSymmetry r base L = evenModeSymmetry r base L := by
  have hc := evenGeometricMode_support q r hqstar hqq hrow hsum base L 1
  have hcs : q * star (evenGeometricMode r base L 1) =
      star (evenGeometricMode r base L 1) := by
    simpa only [star_mul, hqstar] using congrArg star hc.2
  simp only [evenModeSymmetry, mul_add, hc.1, hcs]

include hqstar hqq hrow hsum in
lemma evenShiftSymmetry_support (base L : ℕ) :
    q * evenShiftSymmetry r base L = evenShiftSymmetry r base L := by
  simpa only [evenShiftSymmetry, evenModeSymmetry, evenGeometricShift_eq] using
    evenModeSymmetry_support q r hqstar hqq hrow hsum (base + 1) L

include hqstar hqq hrow hsum in
lemma evenShiftSymmetry_norm_le_one (base L : ℕ) (hL : 0 < L) :
    ‖evenShiftSymmetry r base L‖ ≤ 1 := by
  rw [evenShiftSymmetry, evenGeometricShift_eq]
  apply modeSymmetry_norm_le_one q hqstar hqq
  · exact evenGeometricMode_square_zero q r hqstar hqq hrow hsum _ _ _
  · exact evenGeometricMode_gram q r hqstar hqq hrow hsum _ _ hL 1 (by simp)

include hqstar hqq hrow hsum in
lemma evenModeSymmetry_shift (base L : ℕ) :
    evenRowShift r (evenModeSymmetry r base L) = evenRowParity r * evenShiftSymmetry r base L := by
  have hp := (evenRowParity_relations q r hqstar hqq hrow hsum).1
  have hc := evenGeometricShift_commute_parity q r hqstar hqq hrow base L 1
  have hcs : Commute (evenRowParity r) (star (evenGeometricShift r base L 1)) := by
    simpa only [hp] using hc.star_star
  unfold evenModeSymmetry evenShiftSymmetry
  rw [evenRowShift_add, ← evenRowShift_star,
    evenGeometricMode_shift q r hqstar hqq hrow hsum, star_mul, hp, ← hcs.eq, mul_add]

include hqstar hqq hrow hsum in
lemma evenEigenMode_shift (start base L : ℕ) (ζ : ℂ) :
    evenRowShift r (evenEigenMode r start base L ζ) =
      evenGeometricShift r start L ζ * evenShiftSymmetry r base L := by
  rw [evenEigenMode, ← evenRowShift_mul q r hrow _ _
    (evenModeSymmetry_support q r hqstar hqq hrow hsum base L),
    evenGeometricMode_shift q r hqstar hqq hrow hsum,
    evenModeSymmetry_shift q r hqstar hqq hrow hsum]
  have hc := evenGeometricShift_commute_parity q r hqstar hqq hrow start L ζ
  calc
    _ = evenGeometricShift r start L ζ * (evenRowParity r * evenRowParity r) *
        evenShiftSymmetry r base L := by rw [hc.eq]; noncomm_ring
    _ = _ := by
      rw [(evenRowParity_relations q r hqstar hqq hrow hsum).2.1, mul_assoc,
        evenShiftSymmetry_support q r hqstar hqq hrow hsum]

include hqstar hqq hrow hsum in
lemma evenEigenMode_shift_error (start base L : ℕ) (hL : 0 < L)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖evenRowShift r (evenEigenMode r start base L ζ) - ζ • evenEigenMode r start base L ζ‖ ^ 2 ≤
      18 / (L : ℝ) := by
  let a := evenGeometricMode r start L ζ
  let a' := evenGeometricShift r start L ζ
  let b := evenGeometricMode r base L 1
  let b' := evenGeometricShift r base L 1
  let u := evenModeSymmetry r base L
  let u' := evenShiftSymmetry r base L
  have hu' : ‖u'‖ ≤ 1 := evenShiftSymmetry_norm_le_one q r hqstar hqq hrow hsum base L hL
  have ha : ‖ζ • a‖ ≤ 1 := by
    rw [norm_smul, hζ, one_mul]
    exact evenGeometricMode_norm_le_one q r hqstar hqq hrow hsum start L hL ζ hζ
  have hu : ‖u' - u‖ ≤ 2 * ‖b' - b‖ := by
    have he : u' - u = (b' - b) + star (b' - b) := by
      change (b' + star b') - (b + star b) = _
      rw [star_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖b' - b‖ + ‖star (b' - b)‖ := norm_add_le _ _
      _ = _ := by rw [norm_star]; ring
  have he : a' * u' - ζ • (a * u) = (a' - ζ • a) * u' + (ζ • a) * (u' - u) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc]
    abel
  have hn : ‖a' * u' - ζ • (a * u)‖ ≤ ‖a' - ζ • a‖ + 2 * ‖b' - b‖ := by
    rw [he]
    calc
      _ ≤ ‖(a' - ζ • a) * u'‖ + ‖(ζ • a) * (u' - u)‖ := norm_add_le _ _
      _ ≤ ‖a' - ζ • a‖ * ‖u'‖ + ‖ζ • a‖ * ‖u' - u‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖a' - ζ • a‖ * 1 + 1 * (2 * ‖b' - b‖) := by gcongr
      _ = _ := by ring
  have hA := evenGeometricMode_shift_error q r hqstar hqq hrow hsum start L hL ζ hζ
  have hB := evenGeometricMode_shift_error q r hqstar hqq hrow hsum base L hL 1 (by simp)
  change ‖a' - ζ • a‖ * ‖a' - ζ • a‖ ≤ 2 / (L : ℝ) at hA
  simp only [one_smul] at hB
  change ‖b' - b‖ * ‖b' - b‖ ≤ 2 / (L : ℝ) at hB
  have hsq := mul_le_mul hn hn (norm_nonneg (a' * u' - ζ • (a * u)))
    (by positivity : 0 ≤ ‖a' - ζ • a‖ + 2 * ‖b' - b‖)
  rw [evenEigenMode_shift q r hqstar hqq hrow hsum]
  change ‖a' * u' - ζ • (a * u)‖ ^ 2 ≤ 18 / (L : ℝ)
  calc
    _ ≤ 3 * (‖a' - ζ • a‖ * ‖a' - ζ • a‖) +
        6 * (‖b' - b‖ * ‖b' - b‖) := by
      nlinarith [sq_nonneg (‖a' - ζ • a‖ - ‖b' - b‖)]
    _ ≤ 3 * (2 / (L : ℝ)) + 6 * (2 / (L : ℝ)) := by
      linarith
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
