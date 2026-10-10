import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCompatibilityScaling

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

private theorem exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityRateLimit {K : Type*} [Fintype K]
    (δ : K → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ δ k := by
  classical
  have aux : ∀ s : Finset K, ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ s, ε ≤ δ k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert k s hk ih =>
        obtain ⟨ε, hε, hb⟩ := ih
        refine ⟨min (δ k) ε, lt_min (hδ k) hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hb j hj)
  obtain ⟨ε, hε, hb⟩ := aux Finset.univ
  exact ⟨ε, hε, fun k => hb k (Finset.mem_univ k)⟩

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

def totalBase (base : ∀ c, Shape c → ℕ) : ℕ := ∑ c, baseSize base c

def pairReferenceEntropy (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ) : ℝ :=
  ∑ c, (baseSize base c : ℝ) * finiteEntropy (q c)

def projectedReferenceEntropy (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (H : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  ∑ g : Σ c, Option (Shape c), (baseGroupSize base d g : ℝ) * H g

def compatibilityRate (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  baseEntropy base - pairReferenceEntropy base q +
    projectedReferenceEntropy base designatedLeft HL +
    projectedReferenceEntropy base designatedRight HR

omit [DecidableEq C] in
theorem projectedReferenceEntropy_add_const (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (H : (Σ c, Option (Shape c)) → ℝ) (δ : ℝ) :
    projectedReferenceEntropy base d (fun g => H g + δ) =
      projectedReferenceEntropy base d H + (totalBase base : ℝ) * δ := by
  simp only [projectedReferenceEntropy, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Nat.cast_sum, sum_baseGroupSize, totalBase, baseTotal]

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem compatibilityRate_add_caps (base : ∀ c, Shape c → ℕ)
    (q : ∀ c, Pair c → ℝ) (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ) (δ : ℝ) :
    compatibilityRate base q designatedLeft designatedRight
      (fun g => HL g + δ) (fun g => HR g + δ) =
      compatibilityRate base q designatedLeft designatedRight HL HR +
        2 * (totalBase base : ℝ) * δ := by
  simp only [compatibilityRate, projectedReferenceEntropy_add_const]
  ring

def PairWindow (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (Pos : C → Type*) [∀ c, Fintype (Pos c)]
    (pairCounts : ∀ c, Pair c → ℕ) (η : ℝ) : Prop :=
  ∀ c, 0 < baseSize base c → ∀ a,
    |(pairCounts c a : ℝ) / Fintype.card (Pos c) - q c a| ≤ η

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem exists_pair_entropy_window (q : ∀ c, Pair c → ℝ)
    {κ ηMax : ℝ} (hκ : 0 < κ) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧ ∀ c (r : Pair c → ℝ),
      (∀ a, |r a - q c a| ≤ η) → finiteEntropy (q c) - κ ≤ finiteEntropy r := by
  have hex : ∀ c, ∃ δ : ℝ, 0 < δ ∧ ∀ r : Pair c → ℝ,
      (∀ a, |r a - q c a| ≤ δ) → |finiteEntropy r - finiteEntropy (q c)| < κ :=
    fun c => exists_entropy_window (q c) hκ
  choose δ hδ hw using hex
  obtain ⟨η₀, hη₀, hsmall⟩ := exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityRateLimit δ hδ
  refine ⟨min ηMax η₀, lt_min hηMax hη₀, min_le_left _ _, ?_⟩
  intro c r hr
  have h := (abs_lt.mp (hw c r (fun a =>
    (hr a).trans ((min_le_right _ _).trans (hsmall c))))).1
  linarith

omit [Fintype C] [DecidableEq C] in
theorem repeated_positions_card
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card (Pos c) = t * baseSize base c := by
  rw [fixedClassWords_size Pos Shape _ w c]
  simp only [baseSize, Finset.mul_sum]

omit [DecidableEq C] in
theorem repeated_positions_card_le
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card (Pos c) ≤ t * totalBase base := by
  rw [repeated_positions_card Pos base t w c]
  exact Nat.mul_le_mul_left _
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem pair_classEntropy_lower
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ) (t : ℕ)
    (pairCounts : ∀ c, Pair c → ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    {η κ : ℝ}
    (hwindow : ∀ c (r : Pair c → ℝ), (∀ a, |r a - q c a| ≤ η) →
      finiteEntropy (q c) - κ ≤ finiteEntropy r)
    (hpair : PairWindow base q Pos pairCounts η) :
    (t : ℝ) * (pairReferenceEntropy base q - (totalBase base : ℝ) * κ) ≤
      classEntropy Pos Pair pairCounts := by
  have hc (c : C) :
      (t : ℝ) * (baseSize base c : ℝ) * (finiteEntropy (q c) - κ) ≤
        (Fintype.card (Pos c) : ℝ) *
          finiteEntropy (fun a => (pairCounts c a : ℝ) / Fintype.card (Pos c)) := by
    by_cases hz : baseSize base c = 0
    · simp only [repeated_positions_card Pos base t w c, hz, mul_zero,
        Nat.cast_zero, zero_mul, le_refl]
    · have he := hwindow c (fun a => (pairCounts c a : ℝ) / Fintype.card (Pos c))
        (hpair c (Nat.pos_of_ne_zero hz))
      have hh := mul_le_mul_of_nonneg_left he
        (mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg (baseSize base c)))
      simpa only [repeated_positions_card Pos base t w c, Nat.cast_mul] using hh
  calc
    (t : ℝ) * (pairReferenceEntropy base q - (totalBase base : ℝ) * κ) =
        ∑ c, (t : ℝ) * (baseSize base c : ℝ) * (finiteEntropy (q c) - κ) := by
      simp only [pairReferenceEntropy, totalBase, Nat.cast_sum, Finset.mul_sum,
        Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    _ ≤ classEntropy Pos Pair pairCounts := Finset.sum_le_sum fun c _ => hc c

def errorCoefficient (Shape Pair Left Right : C → Type*)
    [∀ c, Fintype (Shape c)] [∀ c, Fintype (Pair c)]
    [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] : ℝ :=
  classErrorCoefficient Shape + classErrorCoefficient Pair +
    groupErrorCoefficient Shape Left + groupErrorCoefficient Shape Right

omit [DecidableEq C] in
theorem compatibilityExponent_le_rate_add
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (t : ℕ) (ht : 0 < t) (pairCounts : ∀ c, Pair c → ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    {η κ : ℝ}
    (hwindow : ∀ c (r : Pair c → ℝ), (∀ a, |r a - q c a| ≤ η) →
      finiteEntropy (q c) - κ ≤ finiteEntropy r)
    (hpair : PairWindow base q Pos pairCounts η) :
    compatibilityExponent Pos Shape Pair Left Right (fun c u => t * base c u)
      pairCounts designatedLeft designatedRight HL HR w ≤
      (t : ℝ) * (compatibilityRate base q designatedLeft designatedRight HL HR +
        (totalBase base : ℝ) * κ) +
        errorCoefficient Shape Pair Left Right * typeErrorFactor (totalBase base) t := by
  have hsize := repeated_positions_card Pos base t w
  have hsizele := repeated_positions_card_le Pos base t w
  have hs := classEntropy_repeated Pos base t ht hsize
  have hl := groupedEntropy_repeated Pos base designatedLeft t HL w
  have hr := groupedEntropy_repeated Pos base designatedRight t HR w
  have hp := pair_classEntropy_lower Pos base q t pairCounts w hwindow hpair
  have e₁ := classTypeError_le Pos Shape (totalBase base) t hsizele
  have e₂ := classTypeError_le Pos Pair (totalBase base) t hsizele
  have e₃ := groupedTypeError_le Pos Left (fun c u => t * base c u)
    designatedLeft w (totalBase base) t hsizele
  have e₄ := groupedTypeError_le Pos Right (fun c u => t * base c u)
    designatedRight w (totalBase base) t hsizele
  unfold compatibilityExponent
  rw [hs, hl, hr]
  dsimp only [compatibilityRate, projectedReferenceEntropy, baseGroupedEntropy,
    errorCoefficient] at *
  nlinarith

omit [DecidableEq C] in
theorem exists_window_eventually_exponent_le
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (w : FixedClassWords Pos Shape (fun c u => t * base c u)),
          PairWindow base q Pos pairCounts η →
          compatibilityExponent Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts designatedLeft designatedRight HL HR w ≤
            (t : ℝ) * (compatibilityRate base q designatedLeft designatedRight HL HR + ε) := by
  let κ : ℝ := ε / (2 * ((totalBase base : ℝ) + 1))
  have hden : 0 < 2 * ((totalBase base : ℝ) + 1) := by positivity
  have hκ : 0 < κ := div_pos hε hden
  have hκeq : (2 * ((totalBase base : ℝ) + 1)) * κ = ε :=
    mul_div_cancel₀ _ hden.ne'
  have hκbound : (totalBase base : ℝ) * κ ≤ ε / 2 := by
    nlinarith [(Nat.cast_nonneg (totalBase base) : (0 : ℝ) ≤ totalBase base)]
  obtain ⟨η, hη, hηMax', hwindow⟩ := exists_pair_entropy_window q hκ hηMax
  refine ⟨η, hη, hηMax', ?_⟩
  have herr := tendsto_mul_typeErrorFactor_div
    (errorCoefficient Shape Pair Left Right) (totalBase base)
  filter_upwards [(tendsto_order.1 herr).2 (ε / 2) (half_pos hε),
    eventually_ge_atTop (1 : ℕ)] with t he ht
  intro Pos _ _ pairCounts w hp
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
  have htr : (0 : ℝ) < t := Nat.cast_pos.mpr htpos
  have he' := (div_lt_iff₀ htr).mp he
  have hκ' := mul_le_mul_of_nonneg_left hκbound htr.le
  have hb := compatibilityExponent_le_rate_add (Left := Left) (Right := Right)
    Pos base q designatedLeft designatedRight HL HR t htpos pairCounts w hwindow hp
  nlinarith

theorem exists_window_eventually_count_le
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (leftLaw : ∀ c, Shape c → Left c → ℝ)
    (rightLaw : ∀ c, Shape c → Right c → ℝ)
    (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (w : FixedClassWords Pos Shape (fun c u => t * base c u))
          (z : FixedClassWords Pos Pair pairCounts) (χ : ℝ),
          PairWindow base q Pos pairCounts η →
          SideEntropyControl Pos Shape Pair Left (fun c u => t * base c u) pairCounts
            leftPart designatedLeft leftLaw χ HL w →
          SideEntropyControl Pos Shape Pair Right (fun c u => t * base c u) pairCounts
            rightPart designatedRight rightLaw χ HR w →
          (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
            Real.exp ((t : ℝ) *
              (compatibilityRate base q designatedLeft designatedRight HL HR + ε)) ∧
          (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
            Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
              pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
              (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight HL HR + ε) := by
  obtain ⟨η, hη, hηMax', hbound⟩ := exists_window_eventually_exponent_le
    (Left := Left) (Right := Right) base q designatedLeft designatedRight HL HR hε hηMax
  refine ⟨η, hη, hηMax', ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with t hb ht
  intro Pos _ _ pairCounts w z χ hp hL hR
  have he := hb Pos pairCounts w hp
  have hc := compatibleCandidateCount_le_exp Pos Shape Pair Left Right
    (fun c u => t * base c u) pairCounts leftPart rightPart
    designatedLeft designatedRight leftLaw rightLaw χ w z hparts HL HR hL hR
  refine ⟨hc.trans (Real.exp_le_exp.mpr he), ?_⟩
  intro hpos
  have hl := log_compatibleCandidateCount_le Pos Shape Pair Left Right
    (fun c u => t * base c u) pairCounts leftPart rightPart
    designatedLeft designatedRight leftLaw rightLaw χ w z hparts HL HR hL hR hpos
  have htr : (0 : ℝ) < t :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one ht)
  exact (div_le_iff₀ htr).mpr (by simpa only [mul_comm] using hl.trans he)

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
