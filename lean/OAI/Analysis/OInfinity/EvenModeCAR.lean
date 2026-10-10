import OAI.Analysis.OInfinity.EvenShiftModes

namespace OAI

/-! # Disjoint modes for the finite even-row shift

Twisting each geometric mode by the same disjoint reference symmetry removes
the shift parity and preserves its CAR relations. These are actual elements
of the given even-row corner, with the quantitative shift estimate inherited
from the finite geometric sums.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma mode_cross_mul {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (y : J → E) (c : I → ℂ) (d : J → ℂ) :
    carSynthesis x c * carSynthesis y d =
      ∑ i, ∑ j, (c i * d j) • (x i * y j) := by
  unfold carSynthesis
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

private lemma mode_cross_anticommute {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (y : J → E) (hxy : ∀ i j, x i * y j + y j * x i = 0)
    (c : I → ℂ) (d : J → ℂ) :
    carSynthesis x c * carSynthesis y d + carSynthesis y d * carSynthesis x c = 0 := by
  have hswap : carSynthesis y d * carSynthesis x c =
      ∑ i, ∑ j, (c i * d j) • (y j * x i) := by
    rw [mode_cross_mul, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (d j)]
  rw [mode_cross_mul, hswap, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, ← smul_add, hxy, smul_zero]
  simp only [Finset.sum_const_zero]

/-- The product identity responsible for preserving CAR under a common odd symmetry. -/
lemma carReferenceTwist_mul (q u c d : E) (huu : u * u = q)
    (hdq : d * q = d) (hud : u * d + d * u = 0) :
    (c * u) * (d * u) = -(c * d) := by
  have hud' : u * d = -(d * u) := eq_neg_of_add_eq_zero_left hud
  calc
    _ = c * (u * d) * u := by noncomm_ring
    _ = -((c * d) * (u * u)) := by rw [hud']; noncomm_ring
    _ = -(c * d) := by rw [huu, mul_assoc, hdq]

lemma carReferenceTwist_star_mul (q u c d : E) (hustar : star u = u)
    (huu : u * u = q) (hdq : d * q = d)
    (huc : u * c + c * u = 0) (hud : u * d + d * u = 0) :
    star (c * u) * (d * u) = star c * d := by
  have hucstar : u * star c = -(star c * u) := by
    have h := congrArg star huc
    simp only [star_add, star_mul, hustar, star_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hud' : u * d = -(d * u) := eq_neg_of_add_eq_zero_left hud
  rw [star_mul, hustar]
  calc
    _ = (u * star c) * d * u := by noncomm_ring
    _ = -(star c * (u * d) * u) := by rw [hucstar]; noncomm_ring
    _ = (star c * d) * (u * u) := by rw [hud']; noncomm_ring
    _ = star c * d := by rw [huu, mul_assoc, hdq]

variable {n : ℕ} (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

include hqstar hqq hrow hsum in
lemma evenGeometricMode_anticommute (start stop L K : ℕ) (ζ μ : ℂ) :
    evenGeometricMode r start L ζ * evenGeometricMode r stop K μ +
      evenGeometricMode r stop K μ * evenGeometricMode r start L ζ = 0 := by
  apply mode_cross_anticommute
  intro i j
  exact evenRowCAR_anticommute q r hqstar hqq hrow hsum _ _

include hqstar hqq hrow hsum in
lemma evenGeometricMode_disjoint_star_anticommute (start stop L K : ℕ)
    (hdisjoint : start + L ≤ stop ∨ stop + K ≤ start) (ζ μ : ℂ) :
    star (evenGeometricMode r start L ζ) * evenGeometricMode r stop K μ +
      evenGeometricMode r stop K μ * star (evenGeometricMode r start L ζ) = 0 := by
  unfold evenGeometricMode
  rw [carSynthesis_star]
  apply mode_cross_anticommute
  intro i j
  have hij : start + i.val ≠ stop + j.val := by
    have hi := i.isLt
    have hj := j.isLt
    rcases hdisjoint with h | h <;> omega
  simpa only [hij, ite_false] using
    evenRowCAR_star_anticommute q r hqstar hqq hrow hsum
      (start + i.val) (stop + j.val)

lemma evenModeSymmetry_star (base L : ℕ) :
    star (evenModeSymmetry r base L) = evenModeSymmetry r base L := by
  simp only [evenModeSymmetry, star_add, star_star, add_comm]

include hqstar hqq hrow hsum in
lemma evenModeSymmetry_sq (base L : ℕ) (hL : 0 < L) :
    evenModeSymmetry r base L * evenModeSymmetry r base L = q := by
  have hzero := evenGeometricMode_square_zero q r hqstar hqq hrow hsum base L 1
  have hstarzero := congrArg star hzero
  simp only [star_mul, star_zero] at hstarzero
  have hgram := evenGeometricMode_gram q r hqstar hqq hrow hsum base L hL 1 (by simp)
  simp only [evenModeSymmetry, add_mul, mul_add, hzero, hstarzero, zero_add, add_zero]
  simpa only [add_comm] using hgram

include hqstar hqq hrow hsum in
lemma evenModeSymmetry_anticommute (base start L : ℕ)
    (hdisjoint : base + L ≤ start ∨ start + L ≤ base) (ζ : ℂ) :
    evenModeSymmetry r base L * evenGeometricMode r start L ζ +
      evenGeometricMode r start L ζ * evenModeSymmetry r base L = 0 := by
  have h₁ := evenGeometricMode_anticommute q r hqstar hqq hrow hsum base start L L 1 ζ
  have h₂ := evenGeometricMode_disjoint_star_anticommute q r hqstar hqq hrow hsum
    base start L L hdisjoint 1 ζ
  calc
    _ = (evenGeometricMode r base L 1 * evenGeometricMode r start L ζ +
          evenGeometricMode r start L ζ * evenGeometricMode r base L 1) +
        (star (evenGeometricMode r base L 1) * evenGeometricMode r start L ζ +
          evenGeometricMode r start L ζ * star (evenGeometricMode r base L 1)) := by
      unfold evenModeSymmetry
      noncomm_ring
    _ = 0 := by rw [h₁, h₂, add_zero]

include hqstar hqq hrow hsum in
lemma evenEigenMode_anticommute (base start stop L : ℕ) (hL : 0 < L)
    (hstart : base + L ≤ start ∨ start + L ≤ base)
    (hstop : base + L ≤ stop ∨ stop + L ≤ base) (ζ μ : ℂ) :
    evenEigenMode r start base L ζ * evenEigenMode r stop base L μ +
      evenEigenMode r stop base L μ * evenEigenMode r start base L ζ = 0 := by
  have huu := evenModeSymmetry_sq q r hqstar hqq hrow hsum base L hL
  have hc := evenModeSymmetry_anticommute q r hqstar hqq hrow hsum base start L hstart ζ
  have hd := evenModeSymmetry_anticommute q r hqstar hqq hrow hsum base stop L hstop μ
  simp only [evenEigenMode]
  rw [carReferenceTwist_mul q _ _ _ huu
      (evenGeometricMode_support q r hqstar hqq hrow hsum stop L μ).2 hd,
    carReferenceTwist_mul q _ _ _ huu
      (evenGeometricMode_support q r hqstar hqq hrow hsum start L ζ).2 hc,
    ← neg_add, evenGeometricMode_anticommute q r hqstar hqq hrow hsum, neg_zero]

include hqstar hqq hrow hsum in
lemma evenEigenMode_star_anticommute (base start stop L : ℕ) (hL : 0 < L)
    (hstart : base + L ≤ start ∨ start + L ≤ base)
    (hstop : base + L ≤ stop ∨ stop + L ≤ base)
    (hdisjoint : start + L ≤ stop ∨ stop + L ≤ start) (ζ μ : ℂ) :
    star (evenEigenMode r start base L ζ) * evenEigenMode r stop base L μ +
      evenEigenMode r stop base L μ * star (evenEigenMode r start base L ζ) = 0 := by
  have huu := evenModeSymmetry_sq q r hqstar hqq hrow hsum base L hL
  have hc := evenModeSymmetry_anticommute q r hqstar hqq hrow hsum base start L hstart ζ
  have hd := evenModeSymmetry_anticommute q r hqstar hqq hrow hsum base stop L hstop μ
  have hstar := evenModeSymmetry_star r base L
  have hother : evenEigenMode r stop base L μ * star (evenEigenMode r start base L ζ) =
      evenGeometricMode r stop L μ * star (evenGeometricMode r start L ζ) := by
    unfold evenEigenMode
    rw [star_mul, hstar]
    calc
      _ = evenGeometricMode r stop L μ * (evenModeSymmetry r base L *
          evenModeSymmetry r base L) * star (evenGeometricMode r start L ζ) := by noncomm_ring
      _ = _ := by
        rw [huu, (evenGeometricMode_support q r hqstar hqq hrow hsum stop L μ).2]
  rw [hother]
  simp only [evenEigenMode]
  rw [carReferenceTwist_star_mul q _ _ _ hstar huu
      (evenGeometricMode_support q r hqstar hqq hrow hsum stop L μ).2 hc hd]
  exact evenGeometricMode_disjoint_star_anticommute q r hqstar hqq hrow hsum
    start stop L L hdisjoint ζ μ

include hqstar hqq hrow hsum in
lemma evenEigenMode_gram (base start L : ℕ) (hL : 0 < L)
    (hstart : base + L ≤ start ∨ start + L ≤ base) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    star (evenEigenMode r start base L ζ) * evenEigenMode r start base L ζ +
      evenEigenMode r start base L ζ * star (evenEigenMode r start base L ζ) = q := by
  have huu := evenModeSymmetry_sq q r hqstar hqq hrow hsum base L hL
  have hc := evenModeSymmetry_anticommute q r hqstar hqq hrow hsum base start L hstart ζ
  have hstar := evenModeSymmetry_star r base L
  have hsupport := (evenGeometricMode_support q r hqstar hqq hrow hsum start L ζ).2
  unfold evenEigenMode
  rw [carReferenceTwist_star_mul q _ _ _ hstar huu hsupport hc hc]
  have hother : (evenGeometricMode r start L ζ * evenModeSymmetry r base L) *
      star (evenGeometricMode r start L ζ * evenModeSymmetry r base L) =
      evenGeometricMode r start L ζ * star (evenGeometricMode r start L ζ) := by
    rw [star_mul, hstar]
    calc
      _ = evenGeometricMode r start L ζ * (evenModeSymmetry r base L *
          evenModeSymmetry r base L) * star (evenGeometricMode r start L ζ) := by noncomm_ring
      _ = _ := by rw [huu, hsupport]
  rw [hother]
  exact evenGeometricMode_gram q r hqstar hqq hrow hsum start L hL ζ hζ

include hqstar hqq hrow hsum in
lemma evenEigenMode_support (base start L : ℕ) (ζ : ℂ) :
    q * evenEigenMode r start base L ζ = evenEigenMode r start base L ζ ∧
      evenEigenMode r start base L ζ * q = evenEigenMode r start base L ζ := by
  have hc := evenGeometricMode_support q r hqstar hqq hrow hsum start L ζ
  have hu := evenModeSymmetry_support q r hqstar hqq hrow hsum base L
  have hu' : evenModeSymmetry r base L * q = evenModeSymmetry r base L := by
    simpa only [star_mul, hqstar, evenModeSymmetry_star] using congrArg star hu
  constructor
  · change q * (_ * _) = _
    rw [← mul_assoc, hc.1]
    rfl
  · change (_ * _) * q = _
    rw [mul_assoc, hu']
    rfl

/-- Consecutive disjoint geometric blocks, with block zero reserved for the reference. -/
def evenBlockMode {m : ℕ} (r : Fin 2 × Fin n → E) (L : ℕ)
    (ζ : Fin m → ℂ) (i : Fin m) : E :=
  evenEigenMode r ((i.val + 1) * L) 0 L (ζ i)

private lemma block_separate (L i j : ℕ) (hij : i ≠ j) :
    (i + 1) * L + L ≤ (j + 1) * L ∨ (j + 1) * L + L ≤ (i + 1) * L := by
  rcases lt_or_gt_of_ne hij with h | h
  · left
    have : i + 2 ≤ j + 1 := by omega
    nlinarith
  · right
    have : j + 2 ≤ i + 1 := by omega
    nlinarith

include hqstar hqq hrow hsum in
lemma evenBlockMode_CAR {m : ℕ} (L : ℕ) (hL : 0 < L)
    (ζ : Fin m → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    (∀ i j, evenBlockMode r L ζ i * evenBlockMode r L ζ j +
      evenBlockMode r L ζ j * evenBlockMode r L ζ i = 0) ∧
    (∀ i j, star (evenBlockMode r L ζ i) * evenBlockMode r L ζ j +
      evenBlockMode r L ζ j * star (evenBlockMode r L ζ i) = if i = j then q else 0) := by
  have hbase (i : Fin m) : 0 + L ≤ (i.val + 1) * L ∨ (i.val + 1) * L + L ≤ 0 := by
    left
    nlinarith
  constructor
  · intro i j
    exact evenEigenMode_anticommute q r hqstar hqq hrow hsum 0 _ _ L hL
      (hbase i) (hbase j) _ _
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      exact evenEigenMode_gram q r hqstar hqq hrow hsum 0 _ L hL (hbase i) _ (hζ i)
    · simp only [hij, ite_false]
      apply evenEigenMode_star_anticommute q r hqstar hqq hrow hsum 0 _ _ L hL
        (hbase i) (hbase j)
      exact block_separate L i.val j.val (fun h => hij (Fin.ext h))

include hqstar hqq hrow hsum in
lemma evenBlockMode_support {m : ℕ} (L : ℕ) (ζ : Fin m → ℂ) (i : Fin m) :
    q * evenBlockMode r L ζ i = evenBlockMode r L ζ i ∧
      evenBlockMode r L ζ i * q = evenBlockMode r L ζ i :=
  evenEigenMode_support q r hqstar hqq hrow hsum 0 _ L _

include hqstar hqq hrow hsum in
lemma evenBlockMode_shift_error {m : ℕ} (L : ℕ) (hL : 0 < L)
    (ζ : Fin m → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) (i : Fin m) :
    ‖evenRowShift r (evenBlockMode r L ζ i) - ζ i • evenBlockMode r L ζ i‖ ^ 2 ≤
      18 / (L : ℝ) :=
  evenEigenMode_shift_error q r hqstar hqq hrow hsum _ _ L hL _ (hζ i)

end WeakPureInfiniteness

end

end OAI
