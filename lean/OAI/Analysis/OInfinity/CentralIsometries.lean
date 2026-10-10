import OAI.Analysis.OInfinity.BergTent

namespace OAI

/-! # Global approximately central isometries

An unused Cuntz isometry supplies the bottom of a strictly contracting
recursion. Its norm limit is an actual isometry. The damping gives estimates
on the whole algebra, including the last tail; no tail norm is discarded.
-/

noncomputable section
open scoped CStarAlgebra NNReal
open Filter Topology

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def centralDampedBase (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ) : E :=
  r * ((1 - φ 1) + ε • φ 1)

def centralDampedStep (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ) (ρ : ℝ≥0) (x : E) : E :=
  centralDampedBase φ r ε + (ρ : ℝ) • φ x

lemma centralDampedStep_contracting (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) : ContractingWith ρ (centralDampedStep φ r ε ρ) := by
  refine ⟨hρ, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have he : centralDampedStep φ r ε ρ x - centralDampedStep φ r ε ρ y =
      (ρ : ℝ) • φ (x - y) := by
    simp only [centralDampedStep, map_sub, smul_sub]
    abel
  rw [dist_eq_norm, dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ρ.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ _) ρ.coe_nonneg

def centralDampedLimit (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) : E :=
  (centralDampedStep_contracting φ r ε ρ hρ).fixedPoint

lemma centralDampedLimit_eq (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) :
    centralDampedLimit φ r ε ρ hρ = centralDampedBase φ r ε +
      (ρ : ℝ) • φ (centralDampedLimit φ r ε ρ hρ) :=
  (centralDampedStep_contracting φ r ε ρ hρ).fixedPoint_isFixedPt.symm

private lemma centralDampedBase_star_mul (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (ρ : ℝ≥0) (hr : star r * r = 1)
    (hε : ε * ε + (ρ : ℝ) * ρ = 1) :
    star (centralDampedBase φ r ε) * centralDampedBase φ r ε =
      1 - ((ρ : ℝ) * ρ) • φ 1 := by
  have hqstar : star (φ 1) = φ 1 := by rw [← map_star, star_one]
  have hqq : φ 1 * φ 1 = φ 1 := by rw [← map_mul, one_mul]
  have he : ε * ε = 1 - (ρ : ℝ) * ρ := by linarith
  simp only [centralDampedBase, star_mul, star_add, star_sub, star_one,
    star_smul, star_trivial, hqstar]
  rw [mul_assoc, ← mul_assoc (star r), hr, one_mul]
  simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hqq, sub_self, zero_add, smul_smul]
  rw [he]
  module

private lemma centralDampedBase_star_mul_image (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (horth : ∀ x, star r * φ x = 0) (x : E) :
    star (centralDampedBase φ r ε) * φ x = 0 := by
  rw [centralDampedBase, star_mul, mul_assoc, horth, mul_zero]

private lemma centralDampedImage_star_mul_base (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (horth : ∀ x, star r * φ x = 0) (x : E) :
    star (φ x) * centralDampedBase φ r ε = 0 := by
  simpa only [star_mul, star_star, star_zero] using
    congrArg star (centralDampedBase_star_mul_image φ r ε horth x)

/-- The fixed point remains an isometry, by contraction of its multiplicative
defect. This also controls the infinite terminal tail. -/
lemma centralDampedLimit_isometry (φ : E →⋆ₙₐ[ℂ] E) (r : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) (hr : star r * r = 1)
    (hε : ε * ε + (ρ : ℝ) * ρ = 1)
    (horth : ∀ x, star r * φ x = 0) :
    star (centralDampedLimit φ r ε ρ hρ) * centralDampedLimit φ r ε ρ hρ = 1 := by
  let R := centralDampedLimit φ r ε ρ hρ
  have hR : R = centralDampedBase φ r ε + (ρ : ℝ) • φ R :=
    centralDampedLimit_eq φ r ε ρ hρ
  have hphi : star (φ R) * φ R = φ (star R * R) := by rw [map_mul, map_star]
  have hprod : star R * R = 1 - ((ρ : ℝ) * ρ) • φ 1 +
      ((ρ : ℝ) * ρ) • φ (star R * R) := by
    conv_lhs => rw [hR]
    simp only [star_add, star_smul, star_trivial, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul,
      centralDampedBase_star_mul φ r ε ρ hr hε,
      centralDampedBase_star_mul_image φ r ε horth,
      centralDampedImage_star_mul_base φ r ε horth,
      smul_zero, add_zero, zero_add, hphi]
  have he : star R * R - 1 = ((ρ : ℝ) * ρ) • φ (star R * R - 1) := by
    rw [map_sub, smul_sub]
    conv_lhs => rw [hprod]
    abel
  have hn : ‖star R * R - 1‖ ≤ ((ρ : ℝ) * ρ) * ‖star R * R - 1‖ := by
    conv_lhs => rw [he]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
    exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ _)
      (mul_self_nonneg _)
  have hρreal : (ρ : ℝ) < 1 := hρ
  have hρsq : (ρ : ℝ) * ρ < 1 := by nlinarith [ρ.coe_nonneg]
  have hz : ‖star R * R - 1‖ = 0 := by
    rcases eq_or_lt_of_le (norm_nonneg (star R * R - 1)) with hz | hpos
    · exact hz.symm
    · have hp := mul_pos (sub_pos.mpr hρsq) hpos
      nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

private lemma eq_zero_of_damped_norm (x : E) (ρ : ℝ≥0) (hρ : ρ < 1)
    (h : ‖x‖ ≤ (ρ : ℝ) * ‖x‖) : x = 0 := by
  apply norm_eq_zero.mp
  rcases eq_or_lt_of_le (norm_nonneg x) with hz | hpos
  · exact hz.symm
  · have hp := mul_pos (sub_pos.mpr (show (ρ : ℝ) < 1 from hρ)) hpos
    nlinarith

/-- Orthogonal spare isometries give orthogonal limiting isometries. -/
lemma centralDampedLimit_orthogonal (φ : E →⋆ₙₐ[ℂ] E) (r b : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) (hrb : star r * b = 0)
    (hr : ∀ x, star r * φ x = 0) (hb : ∀ x, star b * φ x = 0) :
    star (centralDampedLimit φ r ε ρ hρ) * centralDampedLimit φ b ε ρ hρ = 0 := by
  let R := centralDampedLimit φ r ε ρ hρ
  let B := centralDampedLimit φ b ε ρ hρ
  have hbase : star (centralDampedBase φ r ε) * centralDampedBase φ b ε = 0 := by
    simp only [centralDampedBase, star_mul]
    calc
      _ = star ((1 - φ 1) + ε • φ 1) * (star r * b) * ((1 - φ 1) + ε • φ 1) := by
        noncomm_ring
      _ = 0 := by rw [hrb, mul_zero, zero_mul]
  have hphi : star (φ R) * φ B = φ (star R * B) := by rw [map_mul, map_star]
  have he : star R * B = ((ρ : ℝ) * ρ) • φ (star R * B) := by
    conv_lhs => rw [show R = centralDampedBase φ r ε + (ρ : ℝ) • φ R from
      centralDampedLimit_eq φ r ε ρ hρ,
      show B = centralDampedBase φ b ε + (ρ : ℝ) • φ B from
      centralDampedLimit_eq φ b ε ρ hρ]
    simp only [star_add, star_smul, star_trivial, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, smul_smul, hbase,
      centralDampedBase_star_mul_image φ r ε hr,
      centralDampedImage_star_mul_base φ b ε hb,
      smul_zero, add_zero, zero_add, hphi]
  apply eq_zero_of_damped_norm (star R * B) (ρ * ρ) (by
    have hρreal : (ρ : ℝ) < 1 := hρ
    change (ρ : ℝ) * ρ < 1
    nlinarith [ρ.coe_nonneg])
  conv_lhs => rw [he]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
  exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ _)
    (mul_self_nonneg _)

lemma centralDampedLimit_commutes (φ : E →⋆ₙₐ[ℂ] E) (r y : E) (ε : ℝ)
    (ρ : ℝ≥0) (hρ : ρ < 1) (hbase : Commute (centralDampedBase φ r ε) y)
    (hφ : ∀ x, φ x * y - y * φ x = φ (x * y - y * x)) :
    Commute (centralDampedLimit φ r ε ρ hρ) y := by
  let R := centralDampedLimit φ r ε ρ hρ
  have he : R * y - y * R = (ρ : ℝ) • φ (R * y - y * R) := by
    conv_lhs => rw [show R = centralDampedBase φ r ε + (ρ : ℝ) • φ R from
      centralDampedLimit_eq φ r ε ρ hρ]
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hbase.eq]
    calc
      _ = (ρ : ℝ) • (φ R * y - y * φ R) := by rw [smul_sub]; abel
      _ = _ := by rw [hφ]
  apply sub_eq_zero.mp
  apply eq_zero_of_damped_norm _ ρ hρ
  conv_lhs => rw [he]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ _) ρ.coe_nonneg

section FiniteRow

variable {I : Type*} [Fintype I] [DecidableEq I]

private lemma finiteCuntzDiagonal_orthogonal_unused (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (r : E) (hr : ∀ i, star (s i) * r = 0) (x : E) :
    star r * finiteCuntzDiagonalHom s hs x = 0 := by
  have hrs (i : I) : star r * s i = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star (hr i)
  change star r * (∑ i, s i * x * star (s i)) = 0
  simp only [Finset.mul_sum, ← mul_assoc, hrs, zero_mul, Finset.sum_const_zero]

lemma finiteCuntzDiagonal_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (x : E) (i : I) :
    finiteCuntzDiagonalHom s hs x * s i = s i * x :=
  finiteCuntzTransfer_mul s s hs x i

lemma finiteCuntzGenerator_star_mul_diagonal (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (x : E) (i : I) :
    star (s i) * finiteCuntzDiagonalHom s hs x = x * star (s i) := by
  simpa only [star_mul, ← map_star, star_star] using
    congrArg star (finiteCuntzDiagonal_mul_generator s hs (star x) i)

lemma centralDampedLimit_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (r : E) (ε : ℝ) (ρ : ℝ≥0) (hρ : ρ < 1) (i : I) :
    centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ * s i =
      ε • (r * s i) + (ρ : ℝ) •
        (s i * centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ) := by
  conv_lhs => rw [centralDampedLimit_eq]
  rw [add_mul, smul_mul_assoc,
    finiteCuntzDiagonal_mul_generator]
  simp only [centralDampedBase, mul_assoc, add_mul, sub_mul, one_mul,
    smul_mul_assoc, finiteCuntzDiagonal_mul_generator, mul_one, sub_self,
    zero_add, mul_smul_comm]

lemma centralDampedLimit_generator_star_mul (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (r : E) (hr : ∀ i, star (s i) * r = 0)
    (ε : ℝ) (ρ : ℝ≥0) (hρ : ρ < 1) (i : I) :
    star (s i) * centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ =
      (ρ : ℝ) •
        (centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ * star (s i)) := by
  conv_lhs => rw [centralDampedLimit_eq]
  rw [mul_add, mul_smul_comm,
    finiteCuntzGenerator_star_mul_diagonal]
  simp only [centralDampedBase, ← mul_assoc, hr, zero_mul, zero_add]

lemma centralDampedLimit_commutes_other_row (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (r y : E)
    (hy : ∀ i, Commute (s i) y ∧ Commute (star (s i)) y) (hry : Commute r y)
    (ε : ℝ) (ρ : ℝ≥0) (hρ : ρ < 1) :
    Commute (centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ) y := by
  let φ := finiteCuntzDiagonalHom s hs
  have hright (x : E) : φ x * y = φ (x * y) := by
    change (∑ i, s i * x * star (s i)) * y = ∑ i, s i * (x * y) * star (s i)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = s i * x * (star (s i) * y) := by noncomm_ring
      _ = _ := by rw [(hy i).2.eq]; noncomm_ring
  have hleft (x : E) : y * φ x = φ (y * x) := by
    change y * (∑ i, s i * x * star (s i)) = ∑ i, s i * (y * x) * star (s i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (y * s i) * x * star (s i) := by noncomm_ring
      _ = _ := by rw [← (hy i).1.eq]; noncomm_ring
  have hq : Commute (φ 1) y := by
    change φ 1 * y = y * φ 1
    rw [hright, hleft, one_mul, mul_one]
  apply centralDampedLimit_commutes
  · exact hry.mul_left (((Commute.one_left y).sub_left hq).add_left (hq.smul_left ε))
  · intro x
    rw [hright, hleft, map_sub]

variable [Nontrivial E]

/-- Global bounds for the actual limiting isometry. -/
lemma centralDampedLimit_commutator_bounds (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (r : E) (hr : star r * r = 1) (hrs : ∀ i, star (s i) * r = 0)
    (ε : ℝ) (hε0 : 0 ≤ ε) (ρ : ℝ≥0) (hρ : ρ < 1)
    (hε : ε * ε + (ρ : ℝ) * ρ = 1) (i : I) :
    let R := centralDampedLimit (finiteCuntzDiagonalHom s hs) r ε ρ hρ
    star R * R = 1 ∧
      ‖R * s i - s i * R‖ ≤ ε + (1 - (ρ : ℝ)) ∧
      ‖R * star (s i) - star (s i) * R‖ ≤ 1 - (ρ : ℝ) := by
  intro R
  have hR : star R * R = 1 := centralDampedLimit_isometry _ r ε ρ hρ hr hε
    (finiteCuntzDiagonal_orthogonal_unused s hs r hrs)
  have hisonorm (z : E) (hz : star z * z = 1) : ‖z‖ = 1 := by
    have hn := congrArg norm hz
    rw [CStarRing.norm_star_mul_self, norm_one] at hn
    nlinarith [norm_nonneg z]
  have hnR : ‖R‖ = 1 := hisonorm R hR
  have hnr : ‖r‖ = 1 := hisonorm r hr
  have hns : ‖s i‖ = 1 := hisonorm _ (by simpa using hs i i)
  have hρreal : (ρ : ℝ) ≤ 1 := hρ.le
  refine ⟨hR, ?_, ?_⟩
  · have he : R * s i - s i * R =
        ε • (r * s i) - (1 - (ρ : ℝ)) • (s i * R) := by
      rw [centralDampedLimit_mul_generator]
      module
    rw [he]
    calc
      _ ≤ ‖ε • (r * s i)‖ + ‖(1 - (ρ : ℝ)) • (s i * R)‖ := norm_sub_le _ _
      _ ≤ ε * (‖r‖ * ‖s i‖) + (1 - (ρ : ℝ)) * (‖s i‖ * ‖R‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0,
          abs_of_nonneg (sub_nonneg.mpr hρreal)]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_mul_le _ _) hε0)
          (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (sub_nonneg.mpr hρreal))
      _ = _ := by rw [hnr, hns, hnR]; ring
  · have he : R * star (s i) - star (s i) * R =
        (1 - (ρ : ℝ)) • (R * star (s i)) := by
      rw [centralDampedLimit_generator_star_mul s hs r hrs ε ρ hρ]
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hρreal)]
    calc
      _ ≤ (1 - (ρ : ℝ)) * (‖R‖ * ‖star (s i)‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (sub_nonneg.mpr hρreal)
      _ = _ := by rw [norm_star, hnR, hns]; ring

end FiniteRow

private lemma exists_central_damping (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ε : ℝ) (ρ : ℝ≥0), 0 ≤ ε ∧ ρ < 1 ∧
      ε * ε + (ρ : ℝ) * ρ = 1 ∧ ε + (1 - (ρ : ℝ)) < δ := by
  let ε := min (δ / 3) (1 / 2)
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hεthird : ε ≤ δ / 3 := min_le_left _ _
  have hrad : 0 ≤ 1 - ε * ε := by nlinarith
  let ρ : ℝ≥0 := ⟨Real.sqrt (1 - ε * ε), Real.sqrt_nonneg _⟩
  have hsquare : (ρ : ℝ) * ρ = 1 - ε * ε := Real.mul_self_sqrt hrad
  have hρlt : ρ < 1 := by
    change Real.sqrt (1 - ε * ε) < 1
    have hnonneg := Real.sqrt_nonneg (1 - ε * ε)
    change (Real.sqrt (1 - ε * ε)) * Real.sqrt (1 - ε * ε) = 1 - ε * ε at hsquare
    nlinarith
  have hsmall : 1 - (ρ : ℝ) ≤ ε := by nlinarith [ρ.coe_nonneg]
  refine ⟨ε, ρ, hεpos.le, hρlt, ?_, ?_⟩
  · linarith
  · linarith

/-- A whole infinite orthogonal row approximately commutes with the prescribed
finite row and exactly commutes with the other tensor factor. -/
lemma exists_approximately_central_cuntz_row [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (s i) (t j) ∧ Commute (s i) (star (t j)))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ → E,
      (∀ j k, star (r j) * r k = if j = k then 1 else 0) ∧
      (∀ j i, i < n → ‖r j * s i - s i * r j‖ < δ ∧
        ‖r j * star (s i) - star (s i) * r j‖ < δ) ∧
      ∀ j k, Commute (r j) (t k) ∧ Commute (r j) (star (t k)) := by
  obtain ⟨ε, ρ, hε0, hρ, hε, hsmall⟩ := exists_central_damping δ hδ
  let sf (i : Fin n) := s i
  have hsf (i j : Fin n) : star (sf i) * sf j = if i = j then 1 else 0 := by
    simpa only [sf, Fin.ext_iff] using hs i j
  let φ := finiteCuntzDiagonalHom sf hsf
  let r (j : ℕ) := centralDampedLimit φ (s (n + j)) ε ρ hρ
  have horth (j : ℕ) (i : Fin n) : star (sf i) * s (n + j) = 0 := by
    have hij : (i : ℕ) ≠ n + j := by omega
    change star (s i) * s (n + j) = 0
    simp only [hs, ite_eq_right hij]
  have hriso (j : ℕ) : star (s (n + j)) * s (n + j) = 1 := by simpa using hs (n + j) (n + j)
  refine ⟨r, ?_, ?_, ?_⟩
  · intro j k
    by_cases hjk : j = k
    · subst k
      simpa [r] using centralDampedLimit_isometry φ (s (n + j))
        ε ρ hρ (hriso j) hε (finiteCuntzDiagonal_orthogonal_unused sf hsf _ (horth j))
    · rw [ite_eq_right hjk]
      apply centralDampedLimit_orthogonal
      · have hne : n + j ≠ n + k := by omega
        simp only [hs, ite_eq_right hne]
      · exact finiteCuntzDiagonal_orthogonal_unused sf hsf _ (horth j)
      · exact finiteCuntzDiagonal_orthogonal_unused sf hsf _ (horth k)
  · intro j i hi
    have hb := centralDampedLimit_commutator_bounds sf hsf (s (n + j))
      (hriso j) (horth j) ε hε0 ρ hρ hε ⟨i, hi⟩
    exact ⟨hb.2.1.trans_lt hsmall, hb.2.2.trans_lt (lt_of_le_of_lt (by linarith) hsmall)⟩
  · intro j k
    constructor
    · exact centralDampedLimit_commutes_other_row sf hsf _ _
        (fun i => ⟨(hc i k).1, (hc i k).2.star_left⟩) (hc (n + j) k).1 ε ρ hρ
    · exact centralDampedLimit_commutes_other_row sf hsf _ _
        (fun i => ⟨(hc i k).2, (hc i k).1.star_star⟩) (hc (n + j) k).2 ε ρ hρ

end WeakPureInfiniteness

end

end OAI
