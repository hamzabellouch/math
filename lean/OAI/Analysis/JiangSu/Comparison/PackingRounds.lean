import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.LocalTools

namespace OAI

noncomputable section
namespace DirectPacking
open CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

structure PackingStepBounds (p z y t : D) (c η ε : ℝ) (K : Finset (unitary D)) : Prop where
  mass : ∀ τ : RestrictedTracialState D,
    |(τ.functional y).re - c * (τ.functional p).re| ≤ ε
  overlap : ∀ τ : RestrictedTracialState D,
    |(τ.functional (z * y)).re - c * (τ.functional (z * p)).re| ≤ ε
  inserted_mass_lower : ∀ τ : RestrictedTracialState D,
    (τ.functional y).re - 3 * (τ.functional (z * y)).re ≤ (τ.functional t).re
  inserted_mass_upper : ∀ τ : RestrictedTracialState D,
    (τ.functional t).re ≤ (τ.functional y).re
  inserted_distance : ∀ τ : RestrictedTracialState D,
    traceTwoNorm τ (t - y) ^ 2 ≤ 5 * (τ.functional (z * y)).re
  inserted_linear : ∀ τ : RestrictedTracialState D, ∀ x : D, ‖x‖ ≤ 1 →
    ‖τ.functional ((t - y) * x)‖ ≤
      2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y)
  sampled_linear : ∀ x ∈ K, ∀ τ : RestrictedTracialState D,
    ‖τ.functional (y * (x : D)) - (c : ℂ) * τ.functional (p * (x : D))‖ ≤
      η * ((τ.functional y).re + c * (τ.functional p).re) + 2 * ε
  sampled_energy : ∀ x ∈ K, ∀ τ : RestrictedTracialState D,
    traceTwoNorm τ ((x : D) * y - y * (x : D)) ^ 2 ≤
      c * traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2 +
        6 * η * ((τ.functional y).re + c * (τ.functional p).re) + 10 * ε

lemma re_difference_le_of_complex {a b : ℂ} {c ε : ℝ}
    (h : ‖a - (c : ℂ) * b‖ ≤ ε) : |a.re - c * b.re| ≤ ε := by
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using (Complex.abs_re_le_norm (a - (c : ℂ) * b)).trans h

lemma exists_packing_step {I : Type*} [Fintype I] {q z : D} (U : ProjectionRow I q)
    (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    (hz : IsStarProjection z) (K : Finset (unitary D)) {c η ε : ℝ}
    (hc : c ∈ Set.Icc 0 1) (hη : η < 1) (hε : 0 < ε)
    (happrox : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q H‖ < η) :
    ∃ y t : D, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧
      PackingStepBounds (U.sample q) z y t c η ε K := by
  obtain ⟨e, he, heq, hs⟩ := DirectPacking.sample_mass_overlap U hcoef z hc hε
  let y := U.sample e
  have hy : IsStarProjection y := U.sample_projection he
    ((he.le_iff_mul_eq_right U.projection).mp heq)
  obtain ⟨t, ht, htz, hmove⟩ := hinsert z y hz hy
  have hm (τ : RestrictedTracialState D) :
      |(τ.functional y).re - c * (τ.functional (U.sample q)).re| ≤ ε :=
    re_difference_le_of_complex (hs τ).1.le
  refine ⟨y, t, hy, ht, htz, {
    mass := hm
    overlap := fun τ => re_difference_le_of_complex (hs τ).2.le
    inserted_mass_lower := ?_
    inserted_mass_upper := fun τ => (hmove τ).1.2
    inserted_distance := ?_
    inserted_linear := fun τ => (hmove τ).2.2
    sampled_linear := ?_
    sampled_energy := ?_ }⟩
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).1.1
  · intro τ
    simpa only [τ.tracial y z] using (hmove τ).2.1
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).1
    exact hb.trans (by dsimp [y] at hm ⊢; linarith [hm τ])
  · intro x hx τ
    have hb := (U.matrix_block_sampling he heq x hη hc.1 (happrox x hx) τ).2
    have hb' := (abs_le.mp hb).2
    dsimp [y] at hm ⊢
    linarith [hm τ]

end DirectPacking

namespace DirectPacking
open CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]
variable {r : D}

structure SampledPackingRound (F : WeightedBlockFamily r) (z₀ : D)
    (K : Finset (unitary D)) (η δ : ℝ) where
  final : D
  occupied : F.Index × Bool → D
  sampled : F.Index × Bool → D
  inserted : F.Index × Bool → D
  final_projection : IsStarProjection final
  occupied_projection : ∀ a, IsStarProjection (occupied a)
  sampled_projection : ∀ a, IsStarProjection (sampled a)
  inserted_projection : ∀ a, IsStarProjection (inserted a)
  occupied_le_final : ∀ a, occupied a ≤ final
  inserted_orthogonal : Pairwise (fun a b => inserted a * inserted b = 0)
  initial_orthogonal : ∀ a, z₀ * inserted a = 0
  final_eq : final = z₀ + ∑ a, inserted a
  bounds : ∀ a, PackingStepBounds (F.range a.1) (occupied a) (sampled a) (inserted a)
    (η * F.weight a.1 / 2) η δ K

lemma exists_sampled_packing_round (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    {z₀ : D} (hz₀ : IsStarProjection z₀) (F : WeightedBlockFamily r)
    (K : Finset (unitary D)) {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
    (happrox : ∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) :
    Nonempty (SampledPackingRound F z₀ K η δ) := by
  classical
  let e := Fintype.equivFin (F.Index × Bool)
  let Q := fun (a : Fin (Fintype.card (F.Index × Bool))) (z y t : D) =>
    PackingStepBounds (F.range (e.symm a).1) z y t (η * F.weight (e.symm a).1 / 2) η δ K
  have hstep (a : Fin (Fintype.card (F.Index × Bool))) (z : D) (hz : IsStarProjection z) :
      ∃ y t, IsStarProjection y ∧ IsStarProjection t ∧ t ≤ 1 - z ∧ Q a z y t := by
    have hc : η * F.weight (e.symm a).1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      have hw := F.weight_le_one (e.symm a).1
      have hw0 := F.weight_pos (e.symm a).1
      constructor
      · positivity
      · nlinarith
    exact exists_packing_step (F.row (e.symm a).1) hcoef hinsert hz K hc hη1 hδ (happrox _)
  obtain ⟨S, hS⟩ := exists_projection_insertion _ hz₀ Q hstep
  refine ⟨{
    final := S.occupied (Fin.last _)
    occupied := fun a => S.occupied (e a).castSucc
    sampled := fun a => S.sampled (e a)
    inserted := fun a => S.inserted (e a)
    final_projection := S.occupied_projection _
    occupied_projection := fun a => S.occupied_projection _
    sampled_projection := fun a => S.sampled_projection _
    inserted_projection := fun a => S.inserted_projection _
    occupied_le_final := fun a => S.monotone (Fin.le_last _)
    inserted_orthogonal := fun a b hab => S.orthogonal (e.injective.ne hab)
    initial_orthogonal := fun a => S.initial_orthogonal _
    final_eq := ?_
    bounds := ?_ }⟩
  · rw [e.sum_comp S.inserted]
    exact S.final_eq
  · intro a
    simpa only [Q, Equiv.symm_apply_apply] using hS (e a)

omit [StarOrderedRing D] [TraceFamily D] in
lemma signed_weighted_sum (F : WeightedBlockFamily r) (η : ℝ) (f : F.Index → ℝ) :
    (∑ a : F.Index × Bool, (η * F.weight a.1 / 2) * f a.1) =
      η * ∑ j, F.weight j * f j := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  ring

namespace SampledPackingRound
variable {F : WeightedBlockFamily r} {z₀ : D} {K : Finset (unitary D)} {η δ : ℝ}
variable (R : SampledPackingRound F z₀ K η δ)

def sampledMass (τ : RestrictedTracialState D) : ℝ := ∑ a, (τ.functional (R.sampled a)).re
def targetMass (_R : SampledPackingRound F z₀ K η δ) (τ : RestrictedTracialState D) : ℝ :=
  η * ∑ j, F.weight j * (τ.functional (F.range j)).re
def overlap (τ : RestrictedTracialState D) : ℝ :=
  ∑ a, (τ.functional (R.occupied a * R.sampled a)).re

def totalError (_R : SampledPackingRound F z₀ K η δ) : ℝ := Fintype.card (F.Index × Bool) * δ

lemma sampledMass_nonneg (τ : RestrictedTracialState D) : 0 ≤ R.sampledMass τ :=
  Finset.sum_nonneg fun a _ => (τ.functional.map_nonneg (R.sampled_projection a).nonneg).1

lemma overlap_nonneg (τ : RestrictedTracialState D) : 0 ≤ R.overlap τ :=
  Finset.sum_nonneg fun a _ => (trace_mul_nonneg τ
    (R.occupied_projection a).nonneg (R.sampled_projection a).nonneg).1

lemma sampledMass_error (τ : RestrictedTracialState D) :
    |R.sampledMass τ - R.targetMass τ| ≤ R.totalError := by
  rw [sampledMass, targetMass, ← signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, |(τ.functional (R.sampled a)).re -
        (η * F.weight a.1 / 2) * (τ.functional (F.range a.1)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : F.Index × Bool, δ := Finset.sum_le_sum fun a _ => (R.bounds a).mass τ
    _ = R.totalError := by simp [totalError, nsmul_eq_mul]

lemma totalError_nonneg (hδ : 0 ≤ δ) : 0 ≤ R.totalError := mul_nonneg (Nat.cast_nonneg _) hδ

lemma insertedMass_bounds (τ : RestrictedTracialState D) :
    R.sampledMass τ - 3 * R.overlap τ ≤
      (τ.functional R.final).re - (τ.functional z₀).re ∧
    (τ.functional R.final).re - (τ.functional z₀).re ≤ R.sampledMass τ := by
  have hm : (τ.functional R.final).re - (τ.functional z₀).re =
      ∑ a, (τ.functional (R.inserted a)).re := by
    rw [R.final_eq, map_add, map_sum, Complex.add_re, Complex.re_sum]
    abel
  rw [hm]
  constructor
  · have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_mass_lower τ
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sampledMass, overlap] using h
  · exact Finset.sum_le_sum fun a _ => (R.bounds a).inserted_mass_upper τ

lemma initial_le_final : z₀ ≤ R.final := by
  conv_rhs => rw [R.final_eq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => (R.inserted_projection a).nonneg)

lemma overlap_le_target (τ : RestrictedTracialState D) (hη : 0 ≤ η) :
    R.overlap τ ≤ R.totalError + η * ∑ j, F.weight j * (τ.functional (R.final * F.range j)).re := by
  have hb (a : F.Index × Bool) : (τ.functional (R.occupied a * R.sampled a)).re ≤
      (η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ := by
    have h := (abs_le.mp ((R.bounds a).overlap τ)).2
    have hm := trace_mul_mono_left τ (F.range_projection a.1).nonneg (R.occupied_le_final a)
    have hc : 0 ≤ η * F.weight a.1 / 2 := by
      have hw := F.weight_pos a.1
      positivity
    nlinarith
  calc
    _ ≤ ∑ a, ((η * F.weight a.1 / 2) * (τ.functional (R.final * F.range a.1)).re + δ) :=
      Finset.sum_le_sum fun a _ => hb a
    _ = _ := by
      rw [Finset.sum_add_distrib, signed_weighted_sum F η (fun j => (τ.functional (R.final * F.range j)).re)]
      simp [totalError, nsmul_eq_mul, add_comm]

lemma sampled_linear_sum (τ : RestrictedTracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
      ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_linear x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma sampled_energy_sum (τ : RestrictedTracialState D) (x : unitary D) (hx : x ∈ K) :
    (∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2) ≤
      η * ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 +
      6 * η * (R.sampledMass τ + R.targetMass τ) + 10 * R.totalError := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).sampled_energy x hx τ
  apply h.trans_eq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sampledMass, targetMass, totalError]
  rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2),
    signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

lemma inserted_energy_sum (τ : RestrictedTracialState D) (x : unitary D) :
    (∑ a, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      2 * ∑ a, traceTwoNorm τ ((x : D) * R.sampled a - R.sampled a * (x : D)) ^ 2 +
        40 * R.overlap τ := by
  have hx : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have he := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    commutator_perturb_sq τ hx (R.inserted a) (R.sampled a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hd he
  dsimp [overlap]
  linarith

end SampledPackingRound
end DirectPacking

namespace DirectPacking
open CurrentMain
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

lemma trace_mass_difference_abs_le (τ : RestrictedTracialState D) {a : D} (ha : IsSelfAdjoint a) :
    |(τ.functional a).re| ≤ traceOneNorm τ a := by
  apply abs_le.mpr
  constructor
  · have h := trace_re_le_oneNorm τ ha.neg
    simp only [map_neg, Complex.neg_re, traceOneNorm_neg] at h
    linarith
  · exact trace_re_le_oneNorm τ ha

lemma trace_projected_mass_perturb (τ : RestrictedTracialState D) {p b h : D}
    (hp : IsStarProjection p) (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) {ε : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε) :
    (τ.functional (p * b)).re ≤ (τ.functional (p * h)).re + ε := by
  have ht := (trace_selfAdjoint_contraction_mul_le τ hp.isSelfAdjoint (hb.sub hh) hp.norm_le).trans hclose
  simp only [mul_sub, map_sub, Complex.sub_re] at ht
  linarith

namespace WeightedBlockFamily
variable {r : D} (F : WeightedBlockFamily r)

lemma trace_weightedSum (τ : RestrictedTracialState D) :
    (τ.functional F.weightedSum).re = ∑ j, F.weight j * (τ.functional (F.range j)).re := by
  simp only [CurrentMain.WeightedBlockFamily.weightedSum, map_sum, τ.functional.map_smul_of_tower, Complex.re_sum,
    Complex.smul_re, smul_eq_mul]

lemma trace_mul_weightedSum (τ : RestrictedTracialState D) (z : D) :
    (τ.functional (z * F.weightedSum)).re =
      ∑ j, F.weight j * (τ.functional (z * F.range j)).re := by
  simp only [CurrentMain.WeightedBlockFamily.weightedSum, Finset.mul_sum, mul_smul_comm, map_sum,
    τ.functional.map_smul_of_tower, Complex.re_sum, Complex.smul_re, smul_eq_mul]

end WeightedBlockFamily
namespace SampledPackingRound
variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}
variable (R : SampledPackingRound F z₀ K η δ)

lemma targetMass_eq (τ : RestrictedTracialState D) :
    R.targetMass τ = η * (τ.functional F.weightedSum).re := by
  rw [targetMass, F.trace_weightedSum]

structure Estimates (E : ℝ) : Prop where
  target_upper : ∀ τ : RestrictedTracialState D, R.targetMass τ ≤ 2 * η
  sampled_upper : ∀ τ : RestrictedTracialState D, R.sampledMass τ ≤ 3 * η
  sampled_lower : ∀ τ : RestrictedTracialState D, η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ
  overlap_upper : ∀ τ : RestrictedTracialState D, R.overlap τ ≤ 4 * η * E + 5 * η ^ 2
  overlap_incr : ∀ τ : RestrictedTracialState D, R.overlap τ ≤ 1000 * η * (E + η)
  linear_sum : ∀ x : unitary D, x ∈ K → ∀ τ : RestrictedTracialState D, (∑ a : F.Index × Bool, ‖τ.functional (R.sampled a * (x : D)) -
    ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤ 7 * η ^ 2
  inserted_energy : ∀ x : unitary D, x ∈ K → ∀ τ : RestrictedTracialState D,
    (∑ a : F.Index × Bool, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      1000 * η * (E + η)
  remaining : ∀ τ : RestrictedTracialState D, (τ.functional (1 - R.final)).re ≤
    (1 - η) * (τ.functional (1 - z₀)).re + 3 * η ^ 2 + 3 * R.overlap τ

lemma estimates_of_average (hz₀ : IsStarProjection z₀) (hη : 0 < η) (hη1 : η < 1)
    {E : ℝ} (hE : 0 ≤ E) {b : D} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (herror : R.totalError ≤ η ^ 2)
    (hmass : ∀ τ : RestrictedTracialState D,
      (τ.functional (1 - z₀)).re - η ^ 2 ≤ (τ.functional b).re ∧
      (τ.functional b).re ≤ (τ.functional (1 - z₀)).re)
    (hclose : ∀ τ : RestrictedTracialState D, traceOneNorm τ (F.weightedSum - b) ≤ η ^ 2)
    (henergy : ∀ x : unitary D, x ∈ K → ∀ τ : RestrictedTracialState D,
      ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤ 6 * η)
    (hold : ∀ τ : RestrictedTracialState D, (τ.functional (z₀ * b)).re ≤ 4 * E) : R.Estimates E := by
  have hηsq : η ^ 2 ≤ η := by nlinarith
  have hηcube : η ^ 3 ≤ η ^ 2 := by nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hη1.le)]
  have hc (τ : RestrictedTracialState D) :
      η * (τ.functional (1 - z₀)).re - 2 * η ^ 3 ≤ R.targetMass τ ∧ R.targetMass τ ≤ 2 * η := by
    have herr := (trace_mass_difference_abs_le τ
      (F.weightedSum_nonneg.isSelfAdjoint.sub hb.isSelfAdjoint)).trans (hclose τ)
    simp only [map_sub, Complex.sub_re] at herr
    obtain ⟨hl, hu⟩ := abs_le.mp herr
    have hbnds := hmass τ
    have hr := trace_projection_le_one τ hz₀.one_sub
    rw [R.targetMass_eq τ]
    constructor <;> nlinarith
  have hy (τ : RestrictedTracialState D) :
      η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ ∧ R.sampledMass τ ≤ 3 * η := by
    have herr := abs_le.mp ((R.sampledMass_error τ).trans herror)
    have ht := hc τ
    constructor <;> nlinarith
  have hl (τ : RestrictedTracialState D) : R.overlap τ ≤ 4 * η * E + 5 * η ^ 2 := by
    have hh := trace_projected_mass_perturb τ R.final_projection F.weightedSum_nonneg.isSelfAdjoint
      hb.isSelfAdjoint (hclose τ)
    rw [F.trace_mul_weightedSum] at hh
    have hdiff : 0 ≤ R.final - z₀ := sub_nonneg.mpr R.initial_le_final
    have hm := trace_mul_mono_right τ hdiff hb1
    simp only [mul_one, sub_mul, map_sub, Complex.sub_re] at hm
    have him := (R.insertedMass_bounds τ).2
    have ha := R.overlap_le_target τ hη.le
    have hY := (hy τ).2
    nlinarith [hold τ]
  have hincr (τ : RestrictedTracialState D) : R.overlap τ ≤ 1000 * η * (E + η) := by
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith [hl τ, sq_nonneg η]
  refine {
    target_upper := fun τ => (hc τ).2
    sampled_upper := fun τ => (hy τ).2
    sampled_lower := fun τ => (hy τ).1
    overlap_upper := hl
    overlap_incr := hincr
    linear_sum := ?_
    inserted_energy := ?_
    remaining := ?_ }
  · intro x hx τ
    have hs := R.sampled_linear_sum τ x hx
    have hY := (hy τ).2
    have hC := (hc τ).2
    nlinarith
  · intro x hx τ
    have hs := R.sampled_energy_sum τ x hx
    have ht := R.inserted_energy_sum τ x
    have hY := (hy τ).2
    have hC := (hc τ).2
    have hB := henergy x hx τ
    have hL := hl τ
    have hηE : 0 ≤ η * E := mul_nonneg hη.le hE
    nlinarith
  · intro τ
    have hm := (R.insertedMass_bounds τ).1
    have hY := (hy τ).1
    simp only [map_sub, τ.normalized, Complex.sub_re, Complex.one_re] at hY ⊢
    nlinarith

end SampledPackingRound

omit [StarOrderedRing D] [PartialOrder D] in
lemma projection_finset_sum {I : Type*} (s : Finset I) (t : I → D)
    (ht : ∀ i ∈ s, IsStarProjection (t i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0) :
    IsStarProjection (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsStarProjection.zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, IsStarProjection (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hso : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0 :=
      fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hao : t a * ∑ i ∈ s, t i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact ho a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha]
    exact (ht a (Finset.mem_insert_self a s)).add (ih hs hso) hao

lemma signed_sum {I M : Type*} [Fintype I] [AddCommMonoid M] (f : I × Bool → M) :
    ∑ a, f a = (∑ j, f (j, false)) + ∑ j, f (j, true) := by
  simp [Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

lemma paired_sum_norm_sub_le {I : Type*} [Fintype I] (f : I × Bool → ℂ) (t : I → ℂ) :
    ‖(∑ j, f (j, false)) - ∑ j, f (j, true)‖ ≤ ∑ a, ‖f a - t a.1‖ := by
  calc
    _ = ‖(∑ j, (f (j, false) - t j)) - ∑ j, (f (j, true) - t j)‖ := by
      simp only [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ ‖∑ j, (f (j, false) - t j)‖ + ‖∑ j, (f (j, true) - t j)‖ := norm_sub_le _ _
    _ ≤ (∑ j, ‖f (j, false) - t j‖) + ∑ j, ‖f (j, true) - t j‖ :=
      add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ = _ := (signed_sum (fun a => ‖f a - t a.1‖)).symm

namespace SampledPackingRound
variable {r z₀ : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}
variable (R : SampledPackingRound F z₀ K η δ)

def signSum (σ : Bool) : D := ∑ j, R.inserted (j, σ)

lemma signSum_projection (σ : Bool) : IsStarProjection (R.signSum σ) :=
  projection_finset_sum _ _ (fun _ _ => R.inserted_projection _)
    (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1))

lemma signSum_orthogonal : R.signSum false * R.signSum true = 0 := by
  simp only [signSum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  exact R.inserted_orthogonal (by simp)

lemma initial_signSum_orthogonal (σ : Bool) : z₀ * R.signSum σ = 0 := by
  simp only [signSum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun _ _ => R.initial_orthogonal _

lemma subinitial_signSum_orthogonal {p : D} (hp : IsStarProjection p)
    (hz₀ : IsStarProjection z₀) (hpz : p ≤ z₀) (σ : Bool) : p * R.signSum σ = 0 := by
  calc
    _ = (p * z₀) * R.signSum σ := by rw [(hp.le_iff_mul_eq_left hz₀).mp hpz]
    _ = 0 := by rw [mul_assoc, R.initial_signSum_orthogonal, mul_zero]

lemma final_eq_signSum : R.final = z₀ + (R.signSum false + R.signSum true) := by
  rw [R.final_eq, signed_sum]
  rfl

lemma signSum_energy (τ : RestrictedTracialState D) (x : D) :
    traceTwoNorm τ (x * R.signSum false - R.signSum false * x) ^ 2 +
      traceTwoNorm τ (x * R.signSum true - R.signSum true * x) ^ 2 ≤
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  rw [signed_sum]
  apply add_le_add
  all_goals
    exact (orthogonal_sum_energy_le Finset.univ _ (fun _ _ => R.inserted_projection _)
      (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1)) τ x).2

lemma displacement_sum_le (τ : RestrictedTracialState D) (x : D) (hx : ‖x‖ ≤ 1) :
    (∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * x)‖) ≤
      2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hs (a : F.Index × Bool) : 0 ≤ (τ.functional (R.sampled a)).re :=
    (τ.functional.map_nonneg (R.sampled_projection a).nonneg).1
  have hd := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => (R.bounds a).inserted_distance τ
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (F.Index × Bool))
    (fun a => Real.sqrt (τ.functional (R.sampled a)).re)
    (fun a => traceTwoNorm τ (R.inserted a - R.sampled a))
  simp only [Real.sq_sqrt (hs _)] at hcs
  calc
    _ ≤ ∑ a, 2 * Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) :=
      Finset.sum_le_sum fun a _ => (R.bounds a).inserted_linear τ x hx
    _ = 2 * ∑ a, Real.sqrt (τ.functional (R.sampled a)).re *
        traceTwoNorm τ (R.inserted a - R.sampled a) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ 2 * (Real.sqrt (R.sampledMass τ) *
        Real.sqrt (∑ a, traceTwoNorm τ (R.inserted a - R.sampled a) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      simpa only [← Finset.mul_sum, overlap] using hd

lemma signSum_balance (τ : RestrictedTracialState D) (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError +
        2 * Real.sqrt (R.sampledMass τ) * Real.sqrt (5 * R.overlap τ) := by
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have h := paired_sum_norm_sub_le
    (fun a : F.Index × Bool => τ.functional (R.inserted a * (x : D)))
    (fun j => ((η * F.weight j / 2 : ℝ) : ℂ) * τ.functional (F.range j * (x : D)))
  simp only [signSum, Finset.sum_mul, map_sum]
  apply h.trans
  calc
    _ ≤ (∑ a, ‖τ.functional (R.sampled a * (x : D)) -
        ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) +
        ∑ a, ‖τ.functional ((R.inserted a - R.sampled a) * (x : D))‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a _
      have he : τ.functional (R.inserted a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D)) =
          (τ.functional (R.sampled a * (x : D)) -
          ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))) +
          τ.functional ((R.inserted a - R.sampled a) * (x : D)) := by
        simp only [sub_mul, map_sub]; abel
      rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (R.sampled_linear_sum τ x hx) (R.displacement_sum_le τ _ hxu)

end SampledPackingRound

namespace SampledPackingRound
variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}
variable (R : SampledPackingRound F z₀ K η δ)

lemma Estimates.balance {E : ℝ} (H : R.Estimates E) (hη : 0 < η)
    (herror : R.totalError ≤ η ^ 2) (τ : RestrictedTracialState D)
    (x : unitary D) (hx : x ∈ K) :
    ‖τ.functional (R.signSum false * (x : D)) - τ.functional (R.signSum true * (x : D))‖ ≤
      7 * η ^ 2 + 2 * η * Real.sqrt (60 * E + 75 * η) := by
  have hid : Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) =
      η * Real.sqrt (60 * E + 75 * η) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 3 * η)]
    rw [show 3 * η * (5 * (4 * η * E + 5 * η ^ 2)) = η ^ 2 * (60 * E + 75 * η) by ring]
    rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη.le]
  apply (R.signSum_balance τ x hx).trans
  have hlin : η * (R.sampledMass τ + R.targetMass τ) + 2 * R.totalError ≤ 7 * η ^ 2 := by
    nlinarith [H.sampled_upper τ, H.target_upper τ]
  calc
    _ ≤ 7 * η ^ 2 + 2 * Real.sqrt (3 * η) * Real.sqrt (5 * (4 * η * E + 5 * η ^ 2)) := by
      apply add_le_add hlin
      gcongr
      · exact H.sampled_upper τ
      · exact H.overlap_upper τ
    _ = _ := by rw [mul_assoc, hid, ← mul_assoc]

end SampledPackingRound

structure OrthogonalProjectionPair (D : Type*) [CStarAlgebra D] where
  left : D
  right : D
  left_projection : IsStarProjection left
  right_projection : IsStarProjection right
  orthogonal : left * right = 0

namespace OrthogonalProjectionPair
variable (Q : OrthogonalProjectionPair D)
def total : D := Q.left + Q.right
def energy (τ : RestrictedTracialState D) (x : D) : ℝ :=
  traceTwoNorm τ (x * Q.left - Q.left * x) ^ 2 + traceTwoNorm τ (x * Q.right - Q.right * x) ^ 2
def balance (τ : RestrictedTracialState D) (x : D) : ℝ :=
  ‖τ.functional (Q.left * x) - τ.functional (Q.right * x)‖
def remaining (τ : RestrictedTracialState D) : ℝ := (τ.functional (1 - Q.total)).re

omit [PartialOrder D] [StarOrderedRing D] in
lemma total_projection : IsStarProjection Q.total :=
  Q.left_projection.add Q.right_projection Q.orthogonal

omit [TraceFamily D] in
lemma left_le_total : Q.left ≤ Q.total := le_add_of_nonneg_right Q.right_projection.nonneg
omit [TraceFamily D] in
lemma right_le_total : Q.right ≤ Q.total := le_add_of_nonneg_left Q.left_projection.nonneg

lemma total_energy_le (τ : RestrictedTracialState D) (x : D) :
    traceTwoNorm τ (x * Q.total - Q.total * x) ^ 2 ≤ Q.energy τ x :=
  orthogonal_pair_energy_le τ Q.left_projection Q.right_projection Q.orthogonal x

lemma energy_nonneg (τ : RestrictedTracialState D) (x : D) : 0 ≤ Q.energy τ x :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

variable {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}
variable (R : SampledPackingRound F Q.total K η δ)

lemma right_signSum_orthogonal (σ : Bool) : Q.right * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.right_projection Q.total_projection Q.right_le_total σ

lemma left_signSum_orthogonal (σ : Bool) : Q.left * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.left_projection Q.total_projection Q.left_le_total σ

lemma signSum_right_orthogonal (σ : Bool) : R.signSum σ * Q.right = 0 := by
  have h := congrArg star (Q.right_signSum_orthogonal R σ)
  simpa only [star_mul, (R.signSum_projection σ).isSelfAdjoint.star_eq,
    Q.right_projection.isSelfAdjoint.star_eq, star_zero] using h

def appendRound : OrthogonalProjectionPair D where
  left := Q.left + R.signSum false
  right := Q.right + R.signSum true
  left_projection := Q.left_projection.add (R.signSum_projection false) (Q.left_signSum_orthogonal R false)
  right_projection := Q.right_projection.add (R.signSum_projection true) (Q.right_signSum_orthogonal R true)
  orthogonal := by
    simp only [add_mul, mul_add, Q.orthogonal, Q.left_signSum_orthogonal R true,
      Q.signSum_right_orthogonal R false, R.signSum_orthogonal, add_zero]

lemma appendRound_total : (Q.appendRound R).total = R.final := by
  rw [R.final_eq_signSum]
  dsimp [appendRound, total]
  abel

lemma appendRound_energy (τ : RestrictedTracialState D) (x : D) :
    (Q.appendRound R).energy τ x ≤ Q.energy τ x +
      ∑ a, traceTwoNorm τ (x * R.inserted a - R.inserted a * x) ^ 2 := by
  have hp := orthogonal_pair_energy_le τ Q.left_projection (R.signSum_projection false)
    (Q.left_signSum_orthogonal R false) x
  have hs := orthogonal_pair_energy_le τ Q.right_projection (R.signSum_projection true)
    (Q.right_signSum_orthogonal R true) x
  have hr := R.signSum_energy τ x
  dsimp [energy, appendRound]
  linarith

lemma appendRound_balance (τ : RestrictedTracialState D) (x : D) :
    (Q.appendRound R).balance τ x ≤ Q.balance τ x +
      ‖τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x)‖ := by
  dsimp [balance, appendRound]
  simp only [add_mul, map_add]
  calc
    _ = ‖(τ.functional (Q.left * x) - τ.functional (Q.right * x)) +
          (τ.functional (R.signSum false * x) - τ.functional (R.signSum true * x))‖ := by
      congr 1; abel
    _ ≤ _ := norm_add_le _ _

end OrthogonalProjectionPair
end DirectPacking
end

end OAI
