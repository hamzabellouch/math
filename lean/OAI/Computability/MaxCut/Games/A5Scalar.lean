import Mathlib
import OAI.Computability.MaxCut.Games.OperatorNorm
import OAI.Computability.MaxCut.Games.LevelInequality

namespace OAI

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace MaxCutGames.Appendix.A5Scalar

theorem absorption {d : ℕ} (hd : 1 ≤ d) :
    (162 : ℝ) * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
      ((2 : ℝ) ^ (31 * d - 1))⁻¹) ≤ 1 := by
  have hdd : 1 ≤ d * d := hd.trans (Nat.le_mul_self d)
  have he₁ : 9 ≤ 94 * d * d := by nlinarith
  have he₂ : 9 ≤ 31 * d - 1 := by omega
  have hp₁ : (512 : ℝ) ≤ (2 : ℝ) ^ (94 * d * d) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₁
  have hp₂ : (512 : ℝ) ≤ (2 : ℝ) ^ (31 * d - 1) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₂
  have hb₁ : (512 : ℝ) * ((2 : ℝ) ^ (94 * d * d))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₁
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (94 * d * d)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (94 * d * d) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  have hb₂ : (512 : ℝ) * ((2 : ℝ) ^ (31 * d - 1))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₂
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (31 * d - 1)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (31 * d - 1) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  linarith

theorem geometric_sum_le (q : ℝ) (n : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    (∑ i ∈ Finset.range n, q ^ i) ≤ 4 / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ, pow_zero, ← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right ih hq₀]

def positiveSum (q : ℝ) (n m k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    if 1 ≤ i + j + k then q ^ (i + j + k) else 0

theorem pair_sum_factor (q : ℝ) (n m k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), q ^ (i + j + k)) =
      ((∑ i ∈ Finset.range (n + 1), q ^ i) *
        (∑ j ∈ Finset.range (m + 1), q ^ j)) * q ^ k := by
  simp only [pow_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The exact decomposition with the origin deleted. -/
theorem positiveSum_zero_eq (q : ℝ) (n m : ℕ) :
    positiveSum q n m 0 =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) +
        q * (∑ j ∈ Finset.range m, q ^ j) := by
  have htail : (∑ j ∈ Finset.range (m + 1), if 1 ≤ j then q ^ j else 0) =
      q * (∑ j ∈ Finset.range m, q ^ j) := by
    rw [Finset.sum_range_succ']
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have hshift : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (m + 1), q ^ (i + 1 + j)) =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) := by
    simp only [pow_add, pow_one, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos : ∀ i j : ℕ, 1 ≤ i + 1 + j := by
    intro i j
    omega
  unfold positiveSum
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.zero_add, hpos, ↓reduceIte]
  rw [htail, hshift]

theorem positiveSum_zero_le (q : ℝ) (n m : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    positiveSum q n m 0 ≤ 4 * q := by
  have hn := geometric_sum_le q n hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm' := geometric_sum_le q m hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  rw [positiveSum_zero_eq]
  have h₁ := mul_le_mul_of_nonneg_left hp hq₀
  have h₂ := mul_le_mul_of_nonneg_left hm' hq₀
  nlinarith

theorem positiveSum_pos_le (q : ℝ) (n m k : ℕ) (hq₀ : 0 ≤ q)
    (hq : q ≤ 1 / 4) (hk : 1 ≤ k) : positiveSum q n m k ≤ 2 * q ^ k := by
  have hpos : ∀ i j : ℕ, 1 ≤ i + j + k := by
    intro i j
    omega
  simp only [positiveSum, hpos, ↓reduceIte]
  rw [pair_sum_factor]
  have hn := geometric_sum_le q (n + 1) hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  calc
    _ ≤ ((4 / 3 : ℝ) * (4 / 3)) * q ^ k :=
      mul_le_mul_of_nonneg_right hp (pow_nonneg hq₀ k)
    _ ≤ 2 * q ^ k := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hq₀ k)

/-- The original positive-order geometric bound in (A.16), with independent
finite truncations. No upper bound on `k` is required. -/
theorem a16_finite_geometric (d n m k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (63 * d)
  have hq₀ : 0 ≤ q := pow_nonneg (by norm_num) _
  have hq : q ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ ((2 : ℝ)⁻¹) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have heq : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) =
        positiveSum q n m k := by
    simp only [positiveSum, q, pow_mul]
  rw [heq]
  by_cases hk : k = 0
  · subst k
    calc
      _ ≤ 4 * q := positiveSum_zero_le q n m hq₀ hq
      _ ≤ 4 * ((2 : ℝ)⁻¹) ^ (31 * d + 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (0 + 1)) := by
        norm_num [pow_add] ; ring
  · have hkpos : 1 ≤ k := by omega
    have hs := Induction.positive_rank_geometric_slack d k hkpos
    have hex : 31 * d * (k + 1) + 1 ≤ 63 * d * k := by nlinarith
    calc
      _ ≤ 2 * q ^ k := positiveSum_pos_le q n m k hq₀ hq hkpos
      _ = 2 * ((2 : ℝ)⁻¹) ^ (63 * d * k) := by
        dsimp only [q]
        rw [← pow_mul]
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1) + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hex) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
        norm_num [pow_add] ; ring

theorem a16_original_range (d k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) :=
  a16_finite_geometric d d d k hd

end MaxCutGames.Appendix.A5Scalar
end

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

noncomputable section

namespace MaxCutGames.Appendix.A5Passage

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev OuterIndex (X : F →ₗ[F2] E) (e : Nat) :=
  HybridIndex (E := E ⧸ X.range) (F := X.ker) e

def LiftedA (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 E :=
  s.val.1.comap X.range.mkQ

def LiftedB (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 F :=
  s.val.2.map X.ker.subtype

abbrev Pair (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :=
  OperatorPartitions.A5GeometricIndex X (LiftedA X s) (LiftedB X s)

abbrev Passage (X : F →ₗ[F2] E) (e : Nat) :=
  Σ s : OuterIndex X e, Pair X s

theorem comap_mkQ_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 (E ⧸ P) => A.comap P.mkQ) := by
  intro A B h
  change A.comap P.mkQ = B.comap P.mkQ at h
  ext z
  obtain ⟨v, rfl⟩ := P.mkQ_surjective z
  change v ∈ A.comap P.mkQ ↔ v ∈ B.comap P.mkQ
  rw [h]

theorem map_subtype_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 P => A.map P.subtype) := by
  intro A B h
  change A.map P.subtype = B.map P.subtype at h
  ext z
  constructor
  · intro hz
    have hm : (z : E) ∈ A.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv
  · intro hz
    have hm : (z : E) ∈ B.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv

theorem outer_eq_of_lifted (X : F →ₗ[F2] E) {e : Nat} (s t : OuterIndex X e)
    (hA : LiftedA X s = LiftedA X t) (hB : LiftedB X s = LiftedB X t) : s = t := by
  apply Subtype.ext
  exact Prod.ext (comap_mkQ_injective X.range hA) (map_subtype_injective X.ker hB)

theorem recover_liftedA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    LiftedA X q.1 = q.2.val.1 ⊔ X.range := q.2.property.2.1.symm

theorem recover_liftedB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    LiftedB X q.1 = q.2.val.2 ⊓ X.ker := q.2.property.2.2.2.symm

def forget (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    Submodule F2 E × Submodule F2 F := q.2.val

theorem forget_injective (X : F →ₗ[F2] E) (e : Nat) :
    Function.Injective (forget X e) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  change p.val = q.val at h
  have hA : LiftedA X s = LiftedA X t := by
    calc
      LiftedA X s = p.val.1 ⊔ X.range := p.property.2.1.symm
      _ = q.val.1 ⊔ X.range := congrArg (fun A => A ⊔ X.range) (congrArg Prod.fst h)
      _ = LiftedA X t := q.property.2.1
  have hB : LiftedB X s = LiftedB X t := by
    calc
      LiftedB X s = p.val.2 ⊓ X.ker := p.property.2.2.2.symm
      _ = q.val.2 ⊓ X.ker := congrArg (fun B => B ⊓ X.ker) (congrArg Prod.snd h)
      _ = LiftedB X t := q.property.2.2.2
  have hst := outer_eq_of_lifted X s t hA hB
  cases hst
  have hpq : p = q := Subtype.ext h
  cases hpq
  rfl

@[simp] theorem forget_val (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    forget X e q = q.2.val := rfl

variable [Finite E] [Finite F]

instance pairFintype (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :
    Fintype (Pair X s) := by
  letI : Finite (Submodule F2 E) :=
    Finite.of_injective (fun A : Submodule F2 E => (A : Set E)) SetLike.coe_injective
  letI : Finite (Submodule F2 F) :=
    Finite.of_injective (fun B : Submodule F2 F => (B : Set F)) SetLike.coe_injective
  exact Fintype.ofFinite _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dim_pairA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 q.2.val.1 = Module.finrank F2 q.1.val.1 := by
  have hsup := q.2.val.1.finrank_sup_add_finrank_inf_eq X.range
  rw [q.2.property.2.1, q.2.property.1.eq_bot, finrank_bot, add_zero] at hsup
  have hcomap := HybridComposition.finrank_comap_mkQ X.range q.1.val.1
  change Module.finrank F2 (LiftedA X q.1) =
    Module.finrank F2 X.range + Module.finrank F2 q.1.val.1 at hcomap
  omega

omit [Finite E] [Finite F] [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem codim_pairB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (F ⧸ q.2.val.2) =
      Module.finrank F2 (X.ker ⧸ q.1.val.2) := by
  have hsup := q.2.val.2.finrank_sup_add_finrank_inf_eq X.ker
  rw [q.2.property.2.2.1, q.2.property.2.2.2, finrank_top] at hsup
  have hmap := Submodule.finrank_map_subtype_eq X.ker q.1.val.2
  change Module.finrank F2 (LiftedB X q.1) = Module.finrank F2 q.1.val.2 at hmap
  have hF := q.2.val.2.finrank_quotient_add_finrank
  have hK := q.1.val.2.finrank_quotient_add_finrank
  change Module.finrank F2 (X.ker ⧸ q.1.val.2) + Module.finrank F2 q.1.val.2 =
    Module.finrank F2 X.ker at hK
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    MaxCutGames.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 =
      MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 := by
  unfold MaxCutGames.Fourier.MatrixRestrictions.order
  rw [dim_pairA X q, codim_pairB X q]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order_le (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    MaxCutGames.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 ≤ e := by
  rw [pair_order]
  exact q.1.property

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] in
theorem pair_rank (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (LinearIdentities.compress X q.2.val.1 q.2.val.2).range =
      Module.finrank F2 X.range :=
  LinearIdentities.compress_rank_preserved X q.2.val.1 q.2.val.2
    q.2.property.1 q.2.property.2.2.1

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
omit [FiniteDimensional F2 E] in
theorem descendant_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
      (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      Module.finrank F2 X.range := by
  rw [NaturalTransport.dualFactor_rank]
  exact pair_rank X q

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    MaxCutGames.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      MaxCutGames.Fourier.MatrixRestrictions.order A B +
        MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 +
        Module.finrank F2 X.range := by
  rw [HybridComposition.order_effective, NaturalTransport.dualFactor_rank,
    pair_order, pair_rank]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_le (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (d : Nat)
    (h : MaxCutGames.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range ≤ d)
    (q : Passage X (d - (MaxCutGames.Fourier.MatrixRestrictions.order A B +
      Module.finrank F2 X.range))) :
    MaxCutGames.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range ≤ d := by
  rw [effective_order_rank]
  have hq := q.1.property
  change MaxCutGames.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 ≤
    d - (MaxCutGames.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range) at hq
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_pos (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat}
    (h : 0 < MaxCutGames.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range)
    (q : Passage X e) :
    0 < MaxCutGames.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range := by
  rw [effective_order_rank]
  omega

def descendantSum (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ q : Passage X e,
    𝔼 U, (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2) ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem descendantSum_nonneg (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ descendantSum A B X e f := by
  exact Finset.sum_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => sq_nonneg _

end MaxCutGames.Appendix.A5Passage
end

/-! Finite Gram-energy estimates used in Lemma A.1. The witness relation and
frequency-count instantiations are separate obligations. -/
namespace MaxCutGames.Appendix.F1Gram
open scoped BigOperators

/-- The squared entries of a Gram matrix are bounded by the squared total
energy of its underlying rows. This is a pairwise Cauchy–Schwarz argument. -/
theorem gram_energy_le {R C : Type*} [Fintype R] [Fintype C] (p : R → C → ℝ) :
    (∑ r, ∑ s, (∑ c, p r c * p s c)^2) ≤
      (∑ r, ∑ c, p r c^2)^2 := by
  classical
  let e : R → ℝ := fun r => ∑ c, p r c^2
  calc
    _ ≤ ∑ r, ∑ s, e r * e s := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p r) (p s)
    _ = (∑ r, e r) * (∑ s, e s) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ r, ∑ c, p r c^2)^2 := (pow_two _).symm

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end MaxCutGames.Appendix.F1Gram

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace MaxCutGames.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def horizontal (B : Submodule K V) : Submodule K (V × K) := B.prod ⊥
def hKernel (S : Submodule K (V × K)) : Submodule K V := S.comap (LinearMap.inl K V K)

def scalarMap {Q : Type*} [AddCommGroup Q] [Module K Q] (q : Q) : K →ₗ[K] Q where
  toFun t := t • q
  map_add' a b := add_smul a b q
  map_smul' a b := by change (a*b) • q = a • (b • q); exact mul_smul a b q

def extension (B : Submodule K V) (q : V ⧸ B) : Submodule K (V × K) :=
  LinearMap.ker (B.mkQ.comp (LinearMap.fst K V K) -
    (scalarMap q).comp (LinearMap.snd K V K))

theorem extension_mem (B : Submodule K V) (q : V ⧸ B) (x : V) (t : K) :
    (x,t) ∈ extension B q ↔ B.mkQ x = t • q := by
  change B.mkQ x - t • q = 0 ↔ _
  exact sub_eq_zero

theorem mkQ_eq_smul_iff (B : Submodule K V) (x v : V) (t : K) :
    B.mkQ x = t • B.mkQ v ↔ x - t • v ∈ B := by
  have he : B.mkQ (x-t•v) = B.mkQ x - t•B.mkQ v := by simp only [map_sub, map_smul]
  rw [← sub_eq_zero, ← he]
  change (x-t•v ∈ LinearMap.ker B.mkQ) ↔ _
  rw [Submodule.ker_mkQ]

@[simp] theorem hKernel_horizontal (B : Submodule K V) : hKernel (horizontal B) = B := by
  ext x
  change (x ∈ B ∧ (0:K) = 0) ↔ x ∈ B
  simp

@[simp] theorem hKernel_extension (B : Submodule K V) (q : V ⧸ B) : hKernel (extension B q) = B := by
  ext x
  change (x,0) ∈ extension B q ↔ x ∈ B
  rw [extension_mem, zero_smul]
  change (x ∈ LinearMap.ker B.mkQ) ↔ x ∈ B
  rw [Submodule.ker_mkQ]

theorem exists_one_extension (B : Submodule K V) (q : V ⧸ B) : ∃ v, (v,1) ∈ extension B q := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  exact ⟨v, (extension_mem B q v 1).mpr (by simpa only [one_smul] using hv)⟩

theorem eq_extension_of_one_mem (S : Submodule K (V × K)) (v : V)
    (hv : (v,1) ∈ S) : S = extension (hKernel S) ((hKernel S).mkQ v) := by
  ext p
  rcases p with ⟨x,t⟩
  rw [extension_mem, mkQ_eq_smul_iff]
  change (x,t) ∈ S ↔ (x-t•v,0) ∈ S
  have hz : (x-t•v,0) = (x,t)-t•(v,1) := by ext <;> simp
  rw [hz]
  constructor
  · intro hx; exact S.sub_mem hx (S.smul_mem t hv)
  · intro hx
    have h := S.add_mem hx (S.smul_mem t hv)
    simpa only [sub_add_cancel] using h

theorem eq_horizontal_of_no_one (S : Submodule K (V × K))
    (hn : ¬ ∃ v, (v,1) ∈ S) : S = horizontal (hKernel S) := by
  have last_zero : ∀ x t, (x,t) ∈ S → t = 0 := by
    intro x t hxt
    by_contra ht
    have h := S.smul_mem t⁻¹ hxt
    have h' : (t⁻¹ • x,1) ∈ S := by simpa [smul_eq_mul, ht] using h
    exact hn ⟨_,h'⟩
  ext p
  rcases p with ⟨x,t⟩
  change (x,t) ∈ S ↔ (x ∈ hKernel S ∧ t = 0)
  constructor
  · intro hp
    have ht := last_zero x t hp
    subst t
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact hx

theorem horizontal_ne_extension (A B : Submodule K V) (q : V ⧸ B) : horizontal A ≠ extension B q := by
  intro h
  obtain ⟨v,hv⟩ := exists_one_extension B q
  have hv' : (v,1) ∈ horizontal A := h.symm ▸ hv
  change v ∈ A ∧ (1:K) = 0 at hv'
  exact one_ne_zero hv'.2

theorem extension_injective (B : Submodule K V) : Function.Injective (extension B) := by
  intro q r h
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have hp : (v,1) ∈ extension B q := (extension_mem B q v 1).mpr (by simpa using hv)
  have hp' : (v,1) ∈ extension B r := h ▸ hp
  have hr := (extension_mem B r v 1).mp hp'
  simpa only [one_smul, hv] using hr

def encode : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) → Submodule K (V × K)
  | .inl B => horizontal B
  | .inr ⟨B,q⟩ => extension B q

theorem encode_injective : Function.Injective (encode (K:=K) (V:=V)) := by
  intro a b h
  cases a with
  | inl A =>
    cases b with
    | inl B =>
      have hAB : A = B := by simpa only [encode,hKernel_horizontal] using congrArg hKernel h
      subst B
      rfl
    | inr b =>
      rcases b with ⟨B,q⟩
      exact False.elim (horizontal_ne_extension A B q h)
  | inr a =>
    rcases a with ⟨A,q⟩
    cases b with
    | inl B => exact False.elim (horizontal_ne_extension B A q h.symm)
    | inr b =>
      rcases b with ⟨B,r⟩
      have hAB : A = B := by simpa only [encode,hKernel_extension] using congrArg hKernel h
      cases hAB
      have hqr : q = r := extension_injective A h
      cases hqr
      rfl

theorem encode_surjective : Function.Surjective (encode (K:=K) (V:=V)) := by
  intro S
  by_cases h : ∃ v, (v,1) ∈ S
  · obtain ⟨v,hv⟩ := h
    exact ⟨.inr ⟨hKernel S,(hKernel S).mkQ v⟩, (eq_extension_of_one_mem S v hv).symm⟩
  · exact ⟨.inl (hKernel S), (eq_horizontal_of_no_one S h).symm⟩

def splitEquiv : Submodule K (V × K) ≃ (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B) :=
  (Equiv.ofBijective encode ⟨encode_injective,encode_surjective⟩).symm

def horizontalEquiv (B : Submodule K V) : B ≃ₗ[K] horizontal B where
  toFun b := ⟨((b:V),0),⟨b.property,rfl⟩⟩
  invFun p := ⟨p.val.1,p.property.1⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hp : p.val.2 = 0 := p.property.2
      exact hp.symm
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

def extensionEquiv (B : Submodule K V) (q : V ⧸ B) (v : V) (hv : B.mkQ v = q) :
    (B × K) ≃ₗ[K] extension B q where
  toFun p := ⟨((p.1:V)+p.2•v,p.2), by
    apply (extension_mem B q _ _).mpr
    have hb : B.mkQ (p.1:V) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact p.1.property
    simp only [map_add,map_smul,hb,hv,zero_add]⟩
  invFun p := (⟨p.val.1-p.val.2•v, by
    apply (mkQ_eq_smul_iff B _ v _).mp
    rw [hv]
    exact (extension_mem B q _ _).mp p.property⟩,p.val.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((p.1:V)+p.2•v)-p.2•v = (p.1:V)
      exact add_sub_cancel_right _ _
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.val.1-p.val.2•v)+p.val.2•v = p.val.1
      exact sub_add_cancel _ _
    · rfl
  map_add' p r := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1:V)+(r.1:V))+(p.2+r.2)•v =
        ((p.1:V)+p.2•v)+((r.1:V)+r.2•v)
      rw [add_smul]
      abel
    · rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · change c•(p.1:V)+(c*p.2)•v = c•((p.1:V)+p.2•v)
      rw [smul_add,mul_smul]
    · rfl

theorem finrank_horizontal [FiniteDimensional K V] (B : Submodule K V) :
    Module.finrank K (horizontal B) = Module.finrank K B := (horizontalEquiv B).finrank_eq.symm

theorem finrank_extension [FiniteDimensional K V] (B : Submodule K V) (q : V ⧸ B) :
    Module.finrank K (extension B q) = Module.finrank K B + 1 := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have h := (extensionEquiv B q v hv).finrank_eq.symm
  simpa only [Module.finrank_prod,Module.finrank_self] using h

local instance subspaceFintype [Finite V] : Fintype (Submodule K V) := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.ofInjective (fun B : Submodule K V => (B : Set V)) SetLike.coe_injective
local instance quotientFintype [Finite V] (B : Submodule K V) : Fintype (V ⧸ B) := by
  letI : Finite (V ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  exact Fintype.ofFinite _

def weightedTotal [Finite V] (w : Nat → ℤ) : ℤ := ∑ B : Submodule K V, w (Module.finrank K B)

theorem card_eq_pow_finrank [Finite K] [Finite V] [FiniteDimensional K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  have h := Fintype.card_congr (Module.finBasis K V).equivFun.toEquiv
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card] using h

theorem quotient_card_mul_pow [Finite K] [Finite V] [FiniteDimensional K V] (B : Submodule K V) :
    (Nat.card (V ⧸ B) : ℤ) * (Nat.card K : ℤ)^Module.finrank K B =
      (Nat.card K : ℤ)^Module.finrank K V := by
  rw [card_eq_pow_finrank (K:=K) (V:=V ⧸ B)]
  simp only [Nat.cast_pow]
  rw [← pow_add, B.finrank_quotient_add_finrank]

theorem weightedTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V × K) w =
      ∑ B : Submodule K V, (w (Module.finrank K B) +
        (Nat.card (V ⧸ B) : ℤ) * w (Module.finrank K B + 1)) := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ a : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B),
        w (Module.finrank K (encode a)) :=
      (Equiv.sum_comp ((splitEquiv (K:=K) (V:=V)).symm) _).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_sigma,encode,Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro B _
        exact congrArg w (finrank_horizontal B)
      · apply Finset.sum_congr rfl
        intro B _
        calc
          _ = ∑ _q : V ⧸ B, w (Module.finrank K B + 1) := by
            apply Finset.sum_congr rfl
            intro q _
            exact congrArg w (finrank_extension B q)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Nat.card_eq_fintype_card]

def mobiusWeight (q : Nat) : Nat → ℤ
  | 0 => 1
  | n+1 => -(q:ℤ)^n * mobiusWeight q n

def mobiusTotal [Finite K] [Finite V] : ℤ :=
  weightedTotal (K:=K) (V:=V) (mobiusWeight (Nat.card K))

theorem mobiusTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V × K) =
      (1 - (Nat.card K : ℤ)^Module.finrank K V) * mobiusTotal (K:=K) (V:=V) := by
  classical
  unfold mobiusTotal
  rw [weightedTotal_prod]
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, (1-(Nat.card K:ℤ)^Module.finrank K V) *
        mobiusWeight (Nat.card K) (Module.finrank K B) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [mobiusWeight]
      have hcard := quotient_card_mul_pow (K:=K) B
      calc
        _ = mobiusWeight (Nat.card K) (Module.finrank K B) -
            ((Nat.card (V ⧸ B):ℤ)*(Nat.card K:ℤ)^Module.finrank K B) *
              mobiusWeight (Nat.card K) (Module.finrank K B) := by ring
        _ = _ := by rw [hcard]; ring
    _ = _ := by rw [Finset.mul_sum]

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem map_inverse (e : V ≃ₗ[K] W) (B : Submodule K V) :
    (B.map e.toLinearMap).map e.symm.toLinearMap = B := by
  have hc : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [← Submodule.map_comp,hc,Submodule.map_id]

def subspaceEquiv (e : V ≃ₗ[K] W) : Submodule K V ≃ Submodule K W where
  toFun B := B.map e.toLinearMap
  invFun C := C.map e.symm.toLinearMap
  left_inv := map_inverse e
  right_inv := map_inverse e.symm

def subspaceMapEquiv (e : V ≃ₗ[K] W) (B : Submodule K V) : B ≃ₗ[K] B.map e.toLinearMap where
  toFun b := ⟨e b,Submodule.mem_map.mpr ⟨b,b.property,rfl⟩⟩
  invFun c := ⟨e.symm c,by
    rcases Submodule.mem_map.mp c.property with ⟨b,hb,hbc⟩

    rw [← hbc]
    simpa using hb⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp
  map_smul' c b := by apply Subtype.ext; simp

theorem finrank_map_equiv (e : V ≃ₗ[K] W) (B : Submodule K V) :
    Module.finrank K (B.map e.toLinearMap) = Module.finrank K B := (subspaceMapEquiv e B).finrank_eq.symm

theorem weightedTotal_equiv [Finite V] [Finite W] (e : V ≃ₗ[K] W) (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V) w = weightedTotal (K:=K) (V:=W) w := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, w (Module.finrank K (B.map e.toLinearMap)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [finrank_map_equiv]
    _ = _ := by
      change (∑ B : Submodule K V, w (Module.finrank K (subspaceEquiv e B))) = _
      exact Equiv.sum_comp (subspaceEquiv e) (fun B : Submodule K W => w (Module.finrank K B))

theorem mobiusTotal_equiv [Finite K] [Finite V] [Finite W] (e : V ≃ₗ[K] W) :
    mobiusTotal (K:=K) (V:=V) = mobiusTotal (K:=K) (V:=W) :=
  weightedTotal_equiv e _

def coordinateSplit (n : Nat) :
    (Fin (n+1) → K) ≃ₗ[K] ((Fin n → K) × K) where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i; simp
    · simp
  map_add' f g := rfl
  map_smul' c f := rfl

theorem mobiusTotal_subsingleton [Finite K] [Finite V] [Subsingleton V] :
    mobiusTotal (K:=K) (V:=V) = 1 := by
  classical
  have hB : ∀ B : Submodule K V, B = ⊥ := by
    intro B
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  unfold mobiusTotal weightedTotal
  rw [Finset.sum_eq_single ⊥]
  · simp [mobiusWeight]
  · intro B _ hne
    exact (hne (hB B)).elim
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem coordinate_total_succ [Finite K] (n : Nat) :
    mobiusTotal (K:=K) (V:=Fin (n+1) → K) = 0 := by
  induction n with
  | zero =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) 0),mobiusTotal_prod]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) (n+1)),mobiusTotal_prod,ih,mul_zero]

theorem mobiusTotal_eq_if [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V) = if Module.finrank K V = 0 then 1 else 0 := by
  rw [mobiusTotal_equiv (Module.finBasis K V).equivFun]
  cases hd : Module.finrank K V with
  | zero => simpa [hd] using (mobiusTotal_subsingleton (K:=K) (V:=Fin 0 → K))
  | succ n => simpa [hd] using (coordinate_total_succ (K:=K) n)

theorem mobiusWeight_closed (q n : Nat) :
    mobiusWeight q n = (-1:ℤ)^n * (q:ℤ)^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    rw [mobiusWeight,ih,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,pow_add,pow_succ]
    ring

theorem binary_subspace_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] :
    weightedTotal (K:=ZMod 2) (V:=E) (fun d => (-1:ℤ)^d * 2^(d.choose 2)) =
      if Module.finrank (ZMod 2) E = 0 then 1 else 0 := by
  have h := mobiusTotal_eq_if (K:=ZMod 2) (V:=E)
  have hq : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [mobiusTotal,weightedTotal,mobiusWeight_closed,hq,Nat.cast_ofNat] using h

end
end MaxCutGames.Appendix.SubspaceExtensions

end OAI
