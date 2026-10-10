import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.MatrixSubspaceCount

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

/-- Squared coefficient energy, averaged using the supplied question weights. -/
noncomputable def energy (weight : Q → ℝ) (a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, a q i ^ 2

/-- Squared energy retained by a coordinate projection. -/
noncomputable def cutoffEnergy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) : ℝ := by
  classical
  exact ∑ q, weight q * ∑ i, if keep q i then a q i ^ 2 else 0

/-- Diagonal spectral quadratic form. -/
noncomputable def spectralEnergy (weight : Q → ℝ) (eigen a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, eigen q i * a q i ^ 2

theorem energy_nonneg (weight : Q → ℝ) (a : (q : Q) → I q → ℝ)
    (hw : ∀ q, 0 ≤ weight q) : 0 ≤ energy weight a := by
  exact Finset.sum_nonneg (fun q _ => mul_nonneg (hw q)
    (Finset.sum_nonneg (fun i _ => sq_nonneg (a q i))))

theorem cutoffEnergy_nonneg (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) (hw : ∀ q, 0 ≤ weight q) :
    0 ≤ cutoffEnergy weight keep a := by
  classical
  unfold cutoffEnergy
  apply Finset.sum_nonneg
  intro q _
  apply mul_nonneg (hw q)
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- The projection onto any set of coefficient indices is a contraction in
the weighted squared norm. -/
theorem cutoffEnergy_le_energy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) (hw : ∀ q, 0 ≤ weight q) :
    cutoffEnergy weight keep a ≤ energy weight a := by
  classical
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (hw q)
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> nlinarith [sq_nonneg (a q i)]

/-- Retained and discarded coefficient coordinates are orthogonal: their
energies add exactly to the original energy. -/
theorem energy_split (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (a : (q : Q) → I q → ℝ) :
    energy weight a = cutoffEnergy weight keep a +
      cutoffEnergy weight (fun q i => ¬ keep q i) a := by
  classical
  unfold energy cutoffEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : keep q i <;> simp [h]

/-- A spectral multiplier bounded by one on retained indices and by `η`
elsewhere contributes at most retained energy plus `η` times total energy. -/
theorem spectralEnergy_le_cutoff_add
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (eigen a : (q : Q) → I q → ℝ) (η : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hη : 0 ≤ η)
    (hone : ∀ q i, eigen q i ≤ 1)
    (hhigh : ∀ q i, ¬ keep q i → eigen q i ≤ η) :
    spectralEnergy weight eigen a ≤ cutoffEnergy weight keep a + η * energy weight a := by
  classical
  have hpoint (q : Q) (i : I q) :
      eigen q i * a q i ^ 2 ≤ (if keep q i then a q i ^ 2 else 0) + η * a q i ^ 2 := by
    by_cases hk : keep q i
    · have h := mul_le_mul_of_nonneg_right (hone q i) (sq_nonneg (a q i))
      have hn := mul_nonneg hη (sq_nonneg (a q i))
      simp only [hk, ite_true]
      nlinarith
    · simpa only [hk, ite_false, zero_add] using
        mul_le_mul_of_nonneg_right (hhigh q i hk) (sq_nonneg (a q i))
  calc
    spectralEnergy weight eigen a
        ≤ ∑ q, weight q * ∑ i,
          ((if keep q i then a q i ^ 2 else 0) + η * a q i ^ 2) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint q i)) (hw q)
    _ = cutoffEnergy weight keep a + η * energy weight a := by
      simp only [cutoffEnergy, energy, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Unit total energy and spectral value above `δ` force retained energy above
`δ/2` when all discarded multipliers are at most `δ/2`. -/
theorem cutoffEnergy_gt_half
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (eigen a : (q : Q) → I q → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hδ : 0 ≤ δ)
    (hone : ∀ q i, eigen q i ≤ 1)
    (hhigh : ∀ q i, ¬ keep q i → eigen q i ≤ δ / 2)
    (htotal : energy weight a = 1) (hvalue : δ < spectralEnergy weight eigen a) :
    δ / 2 < cutoffEnergy weight keep a := by
  have h := spectralEnergy_le_cutoff_add weight keep eigen a (δ / 2)
    hw (by linarith) hone hhigh
  rw [htotal] at h
  linarith

/-- The elementary square bound, summed over the retained coefficients.  The
discarded term on the right uses the full coefficient difference, giving the
contraction needed for equation (5.11) without introducing square roots. -/
theorem cutoffEnergy_le_twice_difference_add
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (H G : (q : Q) → I q → ℝ)
    (hw : ∀ q, 0 ≤ weight q) :
    cutoffEnergy weight keep H ≤
      2 * energy weight (fun q i => H q i - G q i) + 2 * cutoffEnergy weight keep G := by
  classical
  have hpoint (q : Q) (i : I q) :
      (if keep q i then H q i ^ 2 else 0) ≤
        2 * (H q i - G q i) ^ 2 + 2 * (if keep q i then G q i ^ 2 else 0) := by
    by_cases hk : keep q i
    · simp only [hk, ite_true]
      nlinarith [sq_nonneg (H q i - 2 * G q i)]
    · simp only [hk, ite_false, mul_zero, add_zero]
      nlinarith [sq_nonneg (H q i - G q i)]
  calc
    cutoffEnergy weight keep H ≤
        ∑ q, weight q * ∑ i,
          (2 * (H q i - G q i) ^ 2 + 2 * (if keep q i then G q i ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint q i)) (hw q)
    _ = 2 * energy weight (fun q i => H q i - G q i) +
        2 * cutoffEnergy weight keep G := by
      simp only [energy, cutoffEnergy, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
      congr 1 <;> rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;> intro q _ <;> ring

theorem deleted_energy_gt_eighth
    (weight : Q → ℝ) (keep : (q : Q) → I q → Prop) (H G : (q : Q) → I q → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q)
    (hlarge : δ / 2 < cutoffEnergy weight keep H)
    (hsmall : cutoffEnergy weight keep G ≤ δ / 8) :
    δ / 8 < energy weight (fun q i => H q i - G q i) := by
  have h := cutoffEnergy_le_twice_difference_add weight keep H G hw
  linarith

/-- Squared Boolean functions equal their values under a finite weighted sum. -/
theorem boolean_energy_eq_mass (weight : Q → ℝ) (H : (q : Q) → I q → ℝ)
    (hbool : ∀ q i, H q i = 0 ∨ H q i = 1) :
    energy weight H = ∑ q, weight q * ∑ i, H q i := by
  unfold energy
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rcases hbool q i with h | h <;> simp [h]

/-- A finite union bound for fractional removed mass dominated by indicator
events. Both the event choice and the removed value may depend on the outcome. -/
theorem weighted_union_bound {Ω J : Type*} [Fintype Ω] [Fintype J]
    (weight value : Ω → ℝ) (event : J → Ω → Prop)
    [∀ j, DecidablePred (event j)]
    (hw : ∀ ω, 0 ≤ weight ω) (hvalue : ∀ ω, value ω ≤ 1)
    (hcover : ∀ ω, 0 < value ω → ∃ j, event j ω) :
    (∑ ω, weight ω * value ω) ≤
      ∑ j, ∑ ω, weight ω * (if event j ω then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  by_cases hp : 0 < value ω
  · obtain ⟨j, hj⟩ := hcover ω hp
    have hs : (if event j ω then (1 : ℝ) else 0) ≤
        ∑ k, if event k ω then (1 : ℝ) else 0 := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun k : J => if event k ω then (1 : ℝ) else 0) (a := j)
      · intro k _; split_ifs <;> norm_num
      · exact Finset.mem_univ j
    exact le_trans (hvalue ω) (by simpa [hj] using hs)
  · exact le_trans (le_of_not_gt hp) (Finset.sum_nonneg (by intro j _; split_ifs <;> norm_num))

/-- Finite real pigeonhole principle for the one fixed color/subspace choice. -/
theorem exists_fixed_event {J : Type*} [Fintype J] (mass : J → ℝ)
    (threshold budget : ℝ)
    (hcount : (Fintype.card J : ℝ) * threshold ≤ budget)
    (hmass : budget < ∑ j, mass j) : ∃ j, threshold < mass j := by
  classical
  by_contra h
  push Not at h
  have hs : (∑ j, mass j) ≤ (Fintype.card J : ℝ) * threshold := by
    calc
      (∑ j, mass j) ≤ ∑ _j : J, threshold := Finset.sum_le_sum (fun j _ => h j)
      _ = _ := by simp
  linarith

/-- The explicit denominator in (5.13), for any supplied event-count bound. -/
theorem exists_fixed_event_scaled {J : Type*} [Fintype J]
    (mass : J → ℝ) (N : ℕ) (δ : ℝ)
    (hN : 0 < N) (hδ : 0 ≤ δ) (hcard : Fintype.card J ≤ N)
    (hmass : δ / 8 < ∑ j, mass j) :
    ∃ j, δ / (8 * (N : ℝ)) < mass j := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcardreal : (Fintype.card J : ℝ) ≤ N := by exact_mod_cast hcard
  have hthreshold : 0 ≤ δ / (8 * (N : ℝ)) :=
    div_nonneg hδ (mul_nonneg (by norm_num) hNreal.le)
  have hcancel : (N : ℝ) * (δ / (8 * (N : ℝ))) = δ / 8 := by
    field_simp [ne_of_gt hNreal]
  apply exists_fixed_event mass (δ / (8 * (N : ℝ))) (δ / 8) _ hmass
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_right hcardreal hthreshold

section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual rank of a Fourier index restricted to the alphabet subspace. -/
noncomputable def linearRankOn (C : Submodule F2 F) (S : F →ₗ[F2] E) : ℕ :=
  Module.finrank F2 (LinearMap.range (S.comp C.subtype))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearRankOn_top (S : F →ₗ[F2] E) :
    linearRankOn (⊤ : Submodule F2 F) S =
      Module.finrank F2 (LinearMap.range S) := by
  have hrange : LinearMap.range (S.comp (⊤ : Submodule F2 F).subtype) =
      LinearMap.range S := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.1, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨⟨v, by simp⟩, hv⟩
  exact congrArg (fun P : Submodule F2 E => Module.finrank F2 P) hrange

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Restricting to the image of a symbol embedding has the same image rank
as composition with that embedding, even when it is not injective. -/
theorem linearRankOn_range {V : Type*} [AddCommGroup V] [Module F2 V]
    (S : F →ₗ[F2] E) (ι : V →ₗ[F2] F) :
    linearRankOn (LinearMap.range ι) S =
      Module.finrank F2 (LinearMap.range (S.comp ι)) := by
  have hrange : LinearMap.range (S.comp (LinearMap.range ι).subtype) =
      LinearMap.range (S.comp ι) := by
    ext x
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ := v.property
      refine ⟨u, ?_⟩
      change S (ι u) = x
      rw [hu]
      exact hv
    · rintro ⟨u, hu⟩
      exact ⟨⟨ι u, ⟨u, rfl⟩⟩, hu⟩
  exact congrArg (fun P : Submodule F2 E => Module.finrank F2 P) hrange

/-- Projection onto trace characters whose index has bounded rank on `C`. -/
noncomputable def rankProjection (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ := by
  classical
  exact ∑ S : F →ₗ[F2] E,
    (if linearRankOn C S ≤ r then linearCoeff f S else 0) •
      (fun X => (linearTraceCharacter S X).re)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sub (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X - g X) S = linearCoeff f S - linearCoeff g S := by
  simp only [linearCoeff, sub_mul, Finset.expect_sub_distrib]

/-- The genuine function-space projection acts by the claimed coefficient mask. -/
theorem linearCoeff_rankProjection (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (rankProjection C r f) S =
      if linearRankOn C S ≤ r then linearCoeff f S else 0 := by
  classical
  unfold rankProjection
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- Squared norm of the actual projection equals the retained coefficient mass. -/
theorem rankProjection_parseval (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X ^ 2) =
      ∑ S : F →ₗ[F2] E, if linearRankOn C S ≤ r then linearCoeff f S ^ 2 else 0 := by
  classical
  rw [← linear_parseval]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankProjection]
  split_ifs <;> simp

/-- Contraction for the actual rank projection with the uniform function norm. -/
theorem rankProjection_contraction (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankProjection_parseval, ← linear_parseval]
  apply Finset.sum_le_sum
  intro S _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-- The projected part is orthogonal to the discarded part in the actual
uniform function inner product. -/
theorem rankProjection_orthogonal (C : Submodule F2 F) (r : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankProjection C r f X * (f X - rankProjection C r f X)) = 0 := by
  classical
  rw [← linear_parseval_inner]
  apply Finset.sum_eq_zero
  intro S _
  rw [linearCoeff_sub, linearCoeff_rankProjection]
  split_ifs <;> simp

theorem linear_energy_parseval (weight : Q → ℝ) (f : Q → (E →ₗ[F2] F) → ℝ) :
    energy weight (fun q S => linearCoeff (f q) S) =
      ∑ q, weight q * (𝔼 X, f q X ^ 2) := by
  simp only [energy, linear_parseval]

theorem linear_difference_energy_parseval (weight : Q → ℝ)
    (H G : Q → (E →ₗ[F2] F) → ℝ) :
    energy weight (fun q S => linearCoeff (H q) S - linearCoeff (G q) S) =
      ∑ q, weight q * (𝔼 X, (H q X - G q X) ^ 2) := by
  simp only [← linearCoeff_sub, linear_energy_parseval]

/-- Equation (5.11) now for actual functions on a binary linear-map space,
using the actual restriction rank and trace Fourier coefficients. -/
theorem linear_deleted_energy_gt_eighth
    (weight : Q → ℝ) (C : Submodule F2 F) (r : ℕ)
    (H G : Q → (E →ₗ[F2] F) → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q)
    (hlarge : δ / 2 < cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun q S => linearCoeff (H q) S))
    (hsmall : cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun q S => linearCoeff (G q) S) ≤ δ / 8) :
    δ / 8 < ∑ q, weight q * (𝔼 X, (H q X - G q X) ^ 2) := by
  rw [← linear_difference_energy_parseval]
  exact deleted_energy_gt_eighth weight (fun _ S => linearRankOn C S ≤ r)
    (fun q S => linearCoeff (H q) S) (fun q S => linearCoeff (G q) S)
    δ hw hlarge hsmall

/-- Color indicator of one actual labeling. -/
noncomputable def colorIndicator {X Y : Type*} (label : X → Y) (y : Y) : X → ℝ := by
  classical
  exact fun x => if label x = y then 1 else 0

theorem colorIndicator_partition {X Y : Type*} [Fintype Y]
    (label : X → Y) (x : X) : ∑ y, colorIndicator label y x ^ 2 = 1 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Parseval for all color indicators sums to exactly one, with the correct
uniform primal normalization and counting measure on Fourier indices. -/
theorem colorIndicator_parseval {Y : Type*} [Fintype Y]
    (label : (E →ₗ[F2] F) → Y) :
    (∑ y, ∑ S : F →ₗ[F2] E, linearCoeff (colorIndicator label y) S ^ 2) = 1 := by
  simp_rw [linear_parseval]
  rw [← Finset.expect_sum_comm]
  simp_rw [colorIndicator_partition]
  exact Fintype.expect_const 1

/-- Fourier coefficient array for a family of labelings, including color as
part of the component index. -/
noncomputable def labelingCoeff {Y : Type*}
    (label : Q → (E →ₗ[F2] F) → Y) (qy : Q × Y) (S : F →ₗ[F2] E) : ℝ :=
  linearCoeff (colorIndicator (label qy.1) qy.2) S

theorem labelingCoeff_energy_one {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (hnorm : ∑ q, weight q = 1) :
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) = 1 := by
  classical
  calc
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) =
        ∑ q, weight q * (∑ y, ∑ S : F →ₗ[F2] E,
          linearCoeff (colorIndicator (label q) y) S ^ 2) := by
      simp only [energy, labelingCoeff, Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ q, weight q := by simp only [colorIndicator_parseval, mul_one]
    _ = 1 := hnorm

/-- The low-rank Fourier-energy conclusion (5.5), for genuine binary linear
maps and genuine labeling coefficients. The spectral premise can be obtained
from the noise diagonalization; the bound is on actual restriction rank. -/
theorem labeling_lowRank_energy {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (C : Submodule F2 F) (r : ℕ) (eigen : Q → (F →ₗ[F2] E) → ℝ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1) (hδ : 0 ≤ δ)
    (hone : ∀ q S, eigen q S ≤ 1)
    (hhigh : ∀ q S, r < linearRankOn C S → eigen q S ≤ δ / 2)
    (hvalue : δ < spectralEnergy (fun qy : Q × Y => weight qy.1)
      (fun qy S => eigen qy.1 S) (labelingCoeff label)) :
    δ / 2 < cutoffEnergy (fun qy : Q × Y => weight qy.1)
      (fun _ S => linearRankOn C S ≤ r) (labelingCoeff label) := by
  apply cutoffEnergy_gt_half _ _ _ _ δ
  · intro qy; exact hw qy.1
  · exact hδ
  · intro qy S; exact hone qy.1 S
  · intro qy S hS; exact hhigh qy.1 S (Nat.lt_of_not_ge hS)
  · exact labelingCoeff_energy_one weight label hnorm
  · exact hvalue

end LinearMaps

section DependentLinearMaps

open MatrixCharacters MatrixFourier

variable {J : Type*} [Fintype J] {E : J → Type*} {F : Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module F2 (E j)]
    [AddCommGroup F] [Module F2 F]
    [∀ j, FiniteDimensional F2 (E j)] [FiniteDimensional F2 F]
    [∀ j, Fintype (E j →ₗ[F2] F)] [∀ j, Fintype (F →ₗ[F2] E j)]

theorem dependent_linear_energy_parseval
    (weight : J → ℝ) (H : (j : J) → (E j →ₗ[F2] F) → ℝ) :
    energy weight (fun j S => linearCoeff (H j) S) =
      ∑ j, weight j * (𝔼 X, H j X ^ 2) := by
  unfold energy
  apply Finset.sum_congr rfl
  intro j _
  rw [linear_parseval]

omit [∀ j, FiniteDimensional F2 (E j)] [FiniteDimensional F2 F] in

theorem dependent_remainder_cutoff_le_eighth
    (weight : J → ℝ) (C : Submodule F2 F) (r : ℕ)
    (G : (j : J) → (E j →ₗ[F2] F) → ℝ) (κ δ : ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8)
    (hlevel : ∀ j, (∑ S : F →ₗ[F2] E j,
      if linearRankOn C S ≤ r then linearCoeff (G j) S ^ 2 else 0) ≤
        κ * (𝔼 X, G j X ^ 2))
    (hmass : (∑ j, weight j * (𝔼 X, G j X ^ 2)) ≤ 1) :
    cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (G j) S) ≤ δ / 8 := by
  classical
  have hs : cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (G j) S) ≤
      κ * (∑ j, weight j * (𝔼 X, G j X ^ 2)) := by
    calc
      _ ≤ ∑ j, weight j * (κ * (𝔼 X, G j X ^ 2)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        simpa using hlevel j
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hm := mul_le_mul_of_nonneg_left hmass hκ
  linarith

/-- The actual removed probability energy in Section 5.3, allowing the map
domain to depend on the complete question and color index. -/
theorem dependent_deleted_energy_from_level
    (weight : J → ℝ) (C : Submodule F2 F) (r : ℕ)
    (H G : (j : J) → (E j →ₗ[F2] F) → ℝ) (κ δ : ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hκ : 0 ≤ κ) (hκδ : κ ≤ δ / 8)
    (hlarge : δ / 2 < cutoffEnergy weight (fun _ S => linearRankOn C S ≤ r)
      (fun j S => linearCoeff (H j) S))
    (hlevel : ∀ j, (∑ S : F →ₗ[F2] E j,
      if linearRankOn C S ≤ r then linearCoeff (G j) S ^ 2 else 0) ≤
        κ * (𝔼 X, G j X ^ 2))
    (hmass : (∑ j, weight j * (𝔼 X, G j X ^ 2)) ≤ 1) :
    δ / 8 < ∑ j, weight j * (𝔼 X, (H j X - G j X) ^ 2) := by
  have hsmall := dependent_remainder_cutoff_le_eighth weight C r G κ δ
    hw hκ hκδ hlevel hmass
  have h := deleted_energy_gt_eighth weight (fun _ S => linearRankOn C S ≤ r)
    (fun j S => linearCoeff (H j) S) (fun j S => linearCoeff (G j) S)
    δ hw hlarge hsmall
  simpa only [← linearCoeff_sub, energy, linear_parseval, Pi.sub_apply] using h

end DependentLinearMaps

/-- Real value of a Boolean indicator. -/
def boolReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem boolReal_sq (b : Bool) : boolReal b ^ 2 = boolReal b := by
  cases b <;> norm_num [boolReal]

theorem boolReal_le_one (b : Bool) : boolReal b ≤ 1 := by
  cases b <;> norm_num [boolReal]

/-- Boolean indicator of one color of a labeling. -/
noncomputable def labelBool {X Y : Type*} (label : X → Y) (y : Y) : X → Bool := by
  classical
  exact fun x => decide (label x = y)

theorem labelBool_real {X Y : Type*} (label : X → Y) (y : Y) (x : X) :
    boolReal (labelBool label y x) = colorIndicator label y x := by
  classical
  simp [boolReal, labelBool, colorIndicator]

/-- Deletion's actual Boolean removed function is exactly the difference of
the original and remainder indicators. -/
theorem removed_boolReal {X Row Witness : Type*}
    (S : Deletion.RestrictionSystem X Row Witness) (H : X → Bool) (p d : ℕ) (x : X) :
    boolReal (Deletion.removed S H p d x) =
      boolReal (H x) - boolReal (Deletion.remainder S H p d x) := by
  classical
  by_cases hd : Deletion.DeletedSet S H p d x
  · simp [Deletion.removed, Deletion.remainder, hd, boolReal]
  · simp [Deletion.removed, Deletion.remainder, hd, boolReal]

theorem removed_difference_sq {X Row Witness : Type*}
    (S : Deletion.RestrictionSystem X Row Witness) (H : X → Bool) (p d : ℕ) (x : X) :
    (boolReal (H x) - boolReal (Deletion.remainder S H p d x)) ^ 2 =
      boolReal (Deletion.removed S H p d x) := by
  rw [← removed_boolReal, boolReal_sq]

section QuestionProbabilities

variable {Ω : Q → Type*} [∀ q, Fintype (Ω q)]
variable {Y A : Type*} [Fintype Y] [Fintype A]

/-- An event probability: first sample the question with the supplied weights,
then sample uniformly in its own finite space. -/
noncomputable def questionEventMass
    (weight : Q → ℝ) (B : (q : Q) → Ω q → Prop) : ℝ := by
  classical
  exact ∑ q, weight q * (𝔼 X, if B q X then (1 : ℝ) else 0)

theorem dependent_removed_union_bound
    (weight : Q → ℝ) (d : (q : Q) → Y → Ω q → ℝ)
    (B : (q : Q) → Y → A → Ω q → Prop)
    (hw : ∀ q, 0 ≤ weight q)
    (hd : ∀ q y X, d q y X ≤ 1)
    (hc : ∀ q y X, 0 < d q y X → ∃ a, B q y a X) :
    (∑ q, weight q * ∑ y, 𝔼 X, d q y X) ≤
      ∑ ya : Y × A, questionEventMass weight (fun q X => B q ya.1 ya.2 X) := by
  classical
  have hp (q : Q) (y : Y) (X : Ω q) :
      d q y X ≤ ∑ a, if B q y a X then (1 : ℝ) else 0 := by
    by_cases hpos : 0 < d q y X
    · obtain ⟨a, ha⟩ := hc q y X hpos
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun b : A => if B q y b X then (1 : ℝ) else 0)
        (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ a)
      exact le_trans (hd q y X) (by simpa [ha] using hi)
    · exact le_trans (le_of_not_gt hpos)
        (Finset.sum_nonneg (by intro a _; split_ifs <;> norm_num))
  calc
    _ ≤ ∑ q, weight q * ∑ y, 𝔼 X,
        ∑ a, if B q y a X then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (hw q)
      apply Finset.sum_le_sum
      intro y _
      exact Finset.expect_le_expect (fun X _ => hp q y X)
    _ = _ := by
      simp only [questionEventMass, Finset.expect_sum_comm,
        Finset.mul_sum, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm

/-- One target is fixed before sampling the question and its map. -/
theorem fixed_target_of_removed_mass
    (weight : Q → ℝ) (d : (q : Q) → Y → Ω q → ℝ)
    (B : (q : Q) → Y → A → Ω q → Prop)
    (hw : ∀ q, 0 ≤ weight q) (hd : ∀ q y X, d q y X ≤ 1)
    (hc : ∀ q y X, 0 < d q y X → ∃ a, B q y a X)
    (δ : ℝ) (N : ℕ) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hcount : Fintype.card (Y × A) ≤ N)
    (hremoved : δ / 8 < ∑ q, weight q * ∑ y, 𝔼 X, d q y X) :
    ∃ y a, δ / (8 * (N : ℝ)) <
      questionEventMass weight (fun q X => B q y a X) := by
  have hu := dependent_removed_union_bound weight d B hw hd hc
  obtain ⟨⟨y, a⟩, hya⟩ := exists_fixed_event_scaled
    (fun ya : Y × A => questionEventMass weight (fun q X => B q ya.1 ya.2 X))
    N δ hN hδ hcount (lt_of_lt_of_le hremoved hu)
  exact ⟨y, a, hya⟩

/-- A Boolean subpartition has total squared mass at most one. Colors are
summed with counting measure, not averaged. -/
theorem boolean_subpartition_energy_le_one [∀ q, Nonempty (Ω q)]
    (weight : Q → ℝ) (label : (q : Q) → Ω q → Y)
    (G : (q : Q) → Y → Ω q → Bool)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1)
    (hG : ∀ q y X, G q y X = true → label q X = y) :
    (∑ q, weight q * ∑ y, 𝔼 X, boolReal (G q y X) ^ 2) ≤ 1 := by
  classical
  have hp (q : Q) (X : Ω q) :
      (∑ y, boolReal (G q y X) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ y, colorIndicator (label q) y X ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hg : G q y X = true
        · have hl := hG q y X hg
          simp [hg, boolReal, colorIndicator, hl]
        · simpa [boolReal, hg] using sq_nonneg (colorIndicator (label q) y X)
      _ = 1 := colorIndicator_partition (label q) X
  have hq (q : Q) : (∑ y, 𝔼 X, boolReal (G q y X) ^ 2) ≤ 1 := by
    rw [← Finset.expect_sum_comm]
    calc
      _ ≤ 𝔼 _X : Ω q, (1 : ℝ) := Finset.expect_le_expect (fun X _ => hp q X)
      _ = 1 := Fintype.expect_const 1
  calc
    _ ≤ ∑ q, weight q * 1 :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hq q) (hw q))
    _ = 1 := by simpa using hnorm

/-- The actual whole-row remainder of labeling indicators satisfies the mass
bound needed in the deleted-energy argument, with no remaining mass hypothesis. -/
theorem remainder_subpartition_energy_le_one [∀ q, Nonempty (Ω q)]
    {Row Witness : Q → Type*}
    (S : (q : Q) → Deletion.RestrictionSystem (Ω q) (Row q) (Witness q))
    (weight : Q → ℝ) (label : (q : Q) → Ω q → Y) (p d : ℕ)
    (hw : ∀ q, 0 ≤ weight q) (hnorm : ∑ q, weight q = 1) :
    (∑ q, weight q * ∑ y, 𝔼 X,
      boolReal (Deletion.remainder (S q) (labelBool (label q) y) p d X) ^ 2) ≤ 1 := by
  apply boolean_subpartition_energy_le_one weight label _ hw hnorm
  intro q y X hG
  have h := Deletion.remainder_le_original (S q) (labelBool (label q) y) p d X hG
  simpa [labelBool] using h

end QuestionProbabilities

section ActualBadRows

open MatrixCharacters

variable {C : Type*} [AddCommGroup C] [Module F2 C]
    [FiniteDimensional F2 C] [Fintype C]
    {E : Q → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module F2 (E q)]
    [∀ q, Finite (E q)] [∀ q, Fintype (E q →ₗ[F2] C)]

/-- Equation (5.13) for the actual whole-row deletion system. Only the color
and target subspace are selected. Neither the question, row value, nor witness
vanishing subspace is part of the counted target. -/
theorem fixed_badRow_target_of_removed_mass
    (weight : Q → ℝ) (H : (q : Q) → C → (E q →ₗ[F2] C) → Bool)
    (r p d : ℕ) (δ : ℝ)
    (hw : ∀ q, 0 ≤ weight q) (hδ : 0 ≤ δ)
    (hremoved : δ / 8 < ∑ q, weight q * ∑ y, 𝔼 X,
      boolReal (Deletion.removed (MatrixRestrictions.system r) (H q y) p d X)) :
    ∃ (y : C) (C' : Submodule F2 C), Module.finrank F2 (C ⧸ C') ≤ r ∧
      δ / (8 * (Nat.card C : ℝ) * (2 : ℝ) ^
        (Module.finrank F2 C * Module.finrank F2 C)) <
      questionEventMass weight (fun q (X : E q →ₗ[F2] C) =>
        Deletion.BadRow (MatrixRestrictions.system r) (H q y) p d
          ⟨C', C'.mkQ.comp X⟩) := by
  classical
  let : Finite (C →ₗ[F2] C) := Finite.of_injective
    (fun f : C →ₗ[F2] C => (f : C → C)) DFunLike.coe_injective
  let : Finite (Submodule F2 C) := Finite.of_surjective
    (fun f : C →ₗ[F2] C => LinearMap.range f)
    MatrixSubspaceCount.endomorphism_range_surjective
  let A := {C' : Submodule F2 C // Module.finrank F2 (C ⧸ C') ≤ r}
  let : Fintype A := Fintype.ofFinite A
  let N := Nat.card C * 2 ^ (Module.finrank F2 C * Module.finrank F2 C)
  let value (q : Q) (y : C) (X : E q →ₗ[F2] C) : ℝ :=
    boolReal (Deletion.removed (MatrixRestrictions.system r) (H q y) p d X)
  let event (q : Q) (y : C) (a : A) (X : E q →ₗ[F2] C) : Prop :=
    Deletion.BadRow (MatrixRestrictions.system r) (H q y) p d
      ⟨a.val, a.val.mkQ.comp X⟩
  have hcover (q : Q) (y : C) (X : E q →ₗ[F2] C) (hpos : 0 < value q y X) :
      ∃ a : A, event q y a X := by
    have ht : Deletion.removed (MatrixRestrictions.system r) (H q y) p d X = true := by
      by_contra hn
      simp [value, boolReal, hn] at hpos
    have hdel : Deletion.DeletedSet (MatrixRestrictions.system r) (H q y) p d X := by
      by_contra hn
      simp [Deletion.removed, hn] at ht
    obtain ⟨C', hcodim, hbad⟩ :=
      (MatrixRestrictions.deletedSet_iff_exists_admissible_target (H q y) r p d X).mp hdel
    exact ⟨⟨C', hcodim⟩, hbad⟩
  have hcount : Fintype.card (C × A) ≤ N := by
    simpa only [A, N, Nat.card_eq_fintype_card] using
      (MatrixSubspaceCount.card_color_admissible_subspaces_le
        (fun C' : Submodule F2 C => Module.finrank F2 (C ⧸ C') ≤ r))
  have hN : 0 < N := by
    simpa only [N, Nat.card_eq_fintype_card] using
      (Nat.mul_pos (Fintype.card_pos : 0 < Fintype.card C)
        (pow_pos (by norm_num : 0 < (2 : ℕ)) (Module.finrank F2 C * Module.finrank F2 C)))
  obtain ⟨y, a, ha⟩ := fixed_target_of_removed_mass weight value event hw
    (fun _ _ _ => boolReal_le_one _) hcover δ N hδ hN hcount hremoved
  refine ⟨y, a.val, a.property, ?_⟩
  simpa only [N, event, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using ha

end ActualBadRows

end UniqueGamesTheorem.Fourier.MatrixEnergy

end

end OAI
