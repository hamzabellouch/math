import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.CompressionCountLemmas
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.SubspaceCountingLemmas

namespace OAI

section

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A13Index

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev Triple := LinearIdentities.A4Index (K := F2) (W := F) (V := E)

def weakA (q : Triple (E := E) (F := F)) : Submodule F2 E :=
  q.2.2.range.comap q.1.mkQ

def weakB (q : Triple (E := E) (F := F)) : Submodule F2 F :=
  q.2.2.ker.map q.2.1.subtype

theorem recover_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakA p.val = A := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.range.comap A0.mkQ = A
  rw [hR]
  ext a
  change A0.mkQ a ∈ A.map A0.mkQ ↔ a ∈ A
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨v, hv, he⟩
    have hm : a - v ∈ A0 := by
      apply (Submodule.Quotient.mk_eq_zero A0).mp
      change A0.mkQ (a - v) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using A.add_mem (hA hm) hv
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

theorem recover_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakB p.val = B := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.ker.map B0.subtype = B
  rw [hK]
  ext b
  constructor
  · intro hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem canonicalValid (q : Triple (E := E) (F := F)) :
    A4IndexCount.Valid (weakA q) (weakB q) q := by
  rcases q with ⟨A0, B0, X⟩
  change A0 ≤ X.range.comap A0.mkQ ∧ X.ker.map B0.subtype ≤ B0 ∧
    X.ker = (X.ker.map B0.subtype).comap B0.subtype ∧
    X.range = (X.range.comap A0.mkQ).map A0.mkQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change A0.mkQ a ∈ X.range
    have hz : A0.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero A0).mpr ha
    rw [hz]
    exact X.range.zero_mem
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact v.property
  · ext b
    constructor
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro hb
      change (b : F) ∈ X.ker.map B0.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨v, hv, he⟩
      have h : v = b := Subtype.ext he
      simpa only [h] using hv
  · ext z
    constructor
    · intro hz
      obtain ⟨v, rfl⟩ := A0.mkQ_surjective z
      exact Submodule.mem_map.mpr ⟨v, hz, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hv

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem dim_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 A = finrank F2 p.val.1 + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 A = finrank F2 A0 + finrank F2 X.range
  let Q := A4IndexCount.quotientRestriction A0 A
  have hQR : Q.range = X.range := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, he⟩
  have hQK : finrank F2 Q.ker = finrank F2 A0 := by
    rw [A4IndexCount.ker_quotientRestriction]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv A ⟨A0, hA⟩).finrank_eq.symm
  have h := Q.finrank_range_add_finrank_ker
  rw [hQR, hQK] at h
  omega

omit [FiniteDimensional F2 E] in
theorem codim_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 (F ⧸ B) =
      finrank F2 (F ⧸ p.val.2.1) + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 (F ⧸ B) = finrank F2 (F ⧸ B0) + finrank F2 X.range
  have hKB : finrank F2 X.ker = finrank F2 B := by
    rw [hK]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv B0 ⟨B, hB⟩).finrank_eq.symm
  have h := X.finrank_range_add_finrank_ker
  rw [hKB] at h
  have hBdim := B.finrank_quotient_add_finrank
  have hB0dim := B0.finrank_quotient_add_finrank
  omega

def size (q : Triple (E := E) (F := F)) : Nat :=
  order q.1 q.2.1 + finrank F2 q.2.2.range

theorem weak_order {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    order A B = order p.val.1 p.val.2.1 + 2 * finrank F2 p.val.2.2.range := by
  have ha := dim_weakA p
  have hb := codim_weakB p
  dsimp only [order]
  omega

theorem order_eq_zero_iff (A : Submodule F2 E) (B : Submodule F2 F) :
    order A B = 0 ↔ A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    change finrank F2 A + finrank F2 (F ⧸ B) = 0 at h
    have ha : finrank F2 A = 0 := by omega
    have hb : finrank F2 (F ⧸ B) = 0 := by omega
    refine ⟨Submodule.finrank_eq_zero.mp ha, ?_⟩
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hq := B.finrank_quotient_add_finrank
    omega
  · rintro ⟨rfl, rfl⟩
    simpa [order] using
      (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem valid_positive_iff {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    (A, B) ≠ (⊥, ⊤) ↔ 0 < size p.val := by
  have h := weak_order p
  constructor
  · intro hp
    by_contra ht
    have hz : order A B = 0 := by
      dsimp only [size] at ht
      omega
    rcases (order_eq_zero_iff A B).mp hz with ⟨hA, hB⟩
    exact hp (Prod.ext hA hB)
  · intro ht hp
    have hAB : A = ⊥ ∧ B = ⊤ := Prod.mk.inj hp
    have hz := (order_eq_zero_iff A B).mpr hAB
    dsimp only [size] at ht
    omega

abbrev WeakPositive :=
  {p : Submodule F2 E × Submodule F2 F // p ≠ (⊥, ⊤)}

abbrev PositiveWitness :=
  Σ p : WeakPositive (E := E) (F := F), A4IndexCount.Index p.val.1 p.val.2

abbrev PositiveTriple := {q : Triple (E := E) (F := F) // 0 < size q}

abbrev BoundedPositiveTriple (d : Nat) :=
  {q : Triple (E := E) (F := F) // 0 < size q ∧ size q ≤ d}

def positiveMap (p : PositiveWitness (E := E) (F := F)) :
    PositiveTriple (E := E) (F := F) :=
  ⟨p.2.val, (valid_positive_iff p.2).mp p.1.property⟩

theorem positiveMap_injective :
    Function.Injective (positiveMap (E := E) (F := F)) := by
  rintro ⟨⟨⟨A, B⟩, hp⟩, p⟩ ⟨⟨⟨A', B'⟩, hp'⟩, p'⟩ he
  have hraw : p.val = p'.val := congrArg Subtype.val he
  have hA : A = A' := by
    calc
      A = weakA p.val := (recover_weakA p).symm
      _ = weakA p'.val := congrArg weakA hraw
      _ = A' := recover_weakA p'
  have hB : B = B' := by
    calc
      B = weakB p.val := (recover_weakB p).symm
      _ = weakB p'.val := congrArg weakB hraw
      _ = B' := recover_weakB p'
  cases hA
  cases hB
  have hpp : p = p' := Subtype.ext hraw
  cases hpp
  rfl

def positiveInverse (q : PositiveTriple (E := E) (F := F)) :
    PositiveWitness (E := E) (F := F) :=
  ⟨⟨(weakA q.val, weakB q.val),
      (valid_positive_iff ⟨q.val, canonicalValid q.val⟩).mpr q.property⟩,
    ⟨q.val, canonicalValid q.val⟩⟩

def positiveEquiv : PositiveWitness (E := E) (F := F) ≃
    PositiveTriple (E := E) (F := F) :=
  Equiv.ofBijective positiveMap ⟨positiveMap_injective, by
    intro q
    refine ⟨positiveInverse q, ?_⟩
    exact Subtype.ext rfl⟩

@[simp] theorem positiveMap_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveMap p).val = p.2.val := rfl

@[simp] theorem positiveEquiv_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveEquiv p).val = p.2.val := rfl

@[instance_reducible]
def tripleFintype [Finite E] [Finite F] :
    Fintype (Triple (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  letI (A : Submodule F2 E) : Finite (E ⧸ A) :=
    Finite.of_surjective A.mkQ A.mkQ_surjective
  letI (A : Submodule F2 E) (B : Submodule F2 F) :
      Fintype (B →ₗ[F2] (E ⧸ A)) := by
    letI : Fintype B := Fintype.ofFinite _
    letI : Fintype (E ⧸ A) := Fintype.ofFinite _
    exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) =>
      (L : B → E ⧸ A)) DFunLike.coe_injective
  exact inferInstance

@[instance_reducible]
def weakPositiveFintype [Finite E] [Finite F] :
    Fintype (WeakPositive (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  exact inferInstance

@[instance_reducible]
def geometricIndexFintype [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (A4IndexCount.Index A B) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def positiveWitnessFintype [Finite E] [Finite F] :
    Fintype (PositiveWitness (E := E) (F := F)) := by
  classical
  letI := weakPositiveFintype (E := E) (F := F)
  letI (A : Submodule F2 E) (B : Submodule F2 F) := geometricIndexFintype A B
  exact inferInstance

@[instance_reducible]
def positiveTripleFintype [Finite E] [Finite F] :
    Fintype (PositiveTriple (E := E) (F := F)) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def boundedPositiveTripleFintype [Finite E] [Finite F] (d : Nat) :
    Fintype (BoundedPositiveTriple (E := E) (F := F) d) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

end UniqueGamesTheorem.Appendix.A13Index

end

end

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsBoolean (f : α → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

omit [Fintype α] in
theorem boolean_nonneg {f : α → ℝ} (hf : IsBoolean f) (x : α) : 0 ≤ f x := by
  rcases hf x with h | h <;> simp [h]

omit [Fintype α] in
theorem boolean_sq {f : α → ℝ} (hf : IsBoolean f) (x : α) : f x ^ 2 = f x := by
  rcases hf x with h | h <;> simp [h]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

theorem boolean_four_thirds_moment {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, |f x| ^ ((4 : ℝ) / 3)) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> norm_num [h]

theorem boolean_holder_fourth {f : α → ℝ} (hf : IsBoolean f) (h : α → ℝ) :
    (𝔼 x, h x * f x) ^ 4 ≤ (𝔼 x, h x ^ 4) * (𝔼 x, f x) ^ 3 := by
  have hfirst := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x * f x) f
  have eleft : (𝔼 x, (h x * f x) * f x) = 𝔼 x, h x * f x := by
    apply Finset.expect_congr rfl
    intro x _
    calc
      _ = h x * (f x ^ 2) := by ring
      _ = _ := by rw [boolean_sq hf]
  have eright : (𝔼 x, (h x * f x) ^ 2) = 𝔼 x, h x ^ 2 * f x := by
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_pow, boolean_sq hf]
  rw [eleft, eright, boolean_squared_norm_eq_density hf] at hfirst
  have hsecond := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => h x ^ 2) f
  have epow : (𝔼 x, (h x ^ 2) ^ 2) = 𝔼 x, h x ^ 4 := by
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [epow, boolean_squared_norm_eq_density hf] at hsecond
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hweighted : 0 ≤ 𝔼 x, h x ^ 2 * f x :=
    Finset.expect_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (boolean_nonneg hf x))
  have hsquare := mul_self_le_mul_self (sq_nonneg (𝔼 x, h x * f x)) hfirst
  have hscaled := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (𝔼 x, f x))
  nlinarith only [hsquare, hscaled]

/-- The fourth-root conversion used in the final displayed inequality.
This is an elementary real estimate, independent of Fourier analysis. -/
theorem fourth_power_le_implies_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hpow : b ^ 4 < a ^ 4 := pow_lt_pow_left₀ hba hb (by decide : (4 : ℕ) ≠ 0)
  exact (not_lt_of_ge h) hpow

/-- Once the genuine fourth-moment estimate has been established, this
proves the final Boolean Hölder implication. The fourth-moment estimate is
an explicit hypothesis here; this lemma itself is not Theorem 2.3. -/
theorem boolean_level_bound_of_fourth_moment {f h : α → ℝ}
    (hf : IsBoolean f) (d : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hprojection : (𝔼 x, h x ^ 2) = 𝔼 x, h x * f x)
    (hfourth : (𝔼 x, h x ^ 4) ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x)) :
    (𝔼 x, h x ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 x, f x ^ 2) := by
  have hμ : 0 ≤ 𝔼 x, f x :=
    Finset.expect_nonneg (fun x _ => boolean_nonneg hf x)
  have hh : 0 ≤ 𝔼 x, h x ^ 2 := Finset.expect_nonneg (fun x _ => sq_nonneg _)
  have hηroot : 0 ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hη _
  have hroot : (η ^ ((1 : ℝ) / 4)) ^ 4 = η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
    norm_num
  have hslack : 113 * d * d ≤ (30 * d * d) * 4 := by
    calc
      113 * d * d = 113 * (d * d) := by ring
      _ ≤ 120 * (d * d) := Nat.mul_le_mul_right _ (by decide)
      _ = (30 * d * d) * 4 := by ring
  have htwo : (2 : ℝ) ^ (113 * d * d) ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hslack
  have hholder := boolean_holder_fourth hf h
  rw [← hprojection] at hholder
  have hscale := mul_le_mul_of_nonneg_right hfourth (pow_nonneg hμ 3)
  have hlarge := mul_le_mul_of_nonneg_right htwo (mul_nonneg hη (pow_nonneg hμ 4))
  rw [boolean_squared_norm_eq_density hf]
  apply fourth_power_le_implies_le hh
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hηroot) hμ)
  calc
    _ ≤ (2 : ℝ) ^ (113 * d * d) * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hholder, hscale]
    _ ≤ ((2 : ℝ) ^ (30 * d * d)) ^ 4 * η * (𝔼 x, f x) ^ 4 := by
      nlinarith only [hlarge]
    _ = _ := by rw [mul_pow, mul_pow, hroot]

end UniqueGamesTheorem.Appendix.LevelInequality

noncomputable section

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual rank of a Fourier index `S : F → E`. -/
def frequencyRank (S : F →ₗ[F2] E) : ℕ := Module.finrank F2 (LinearMap.range S)

def rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S with frequencyRank S = d,
    linearCoeff f S • (fun X => (linearTraceCharacter S X).re)

theorem linearCoeff_rankLevel (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) :
    linearCoeff (rankLevel d f) S = if frequencyRank S = d then linearCoeff f S else 0 := by
  classical
  unfold rankLevel
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

/-- The selected rank mass equals the normalized squared norm of the actual
rank projection. -/
theorem rankLevel_energy (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) =
      ∑ S with frequencyRank S = d, linearCoeff f S ^ 2 := by
  classical
  rw [← linear_parseval]
  simp only [linearCoeff_rankLevel]
  simp [Finset.sum_filter]

/-- Orthogonal-projection identity used in the final Hölder step. -/
theorem rankLevel_inner_self (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) = 𝔼 X, rankLevel d f X * f X := by
  classical
  rw [← linear_parseval, ← linear_parseval_inner]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearCoeff_rankLevel]
  split_ifs <;> ring

/-- Rank projection contracts the normalized L2 norm. -/
theorem rankLevel_energy_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, rankLevel d f X ^ 2) ≤ 𝔼 X, f X ^ 2 := by
  classical
  rw [rankLevel_energy, ← linear_parseval]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun S _ _ => sq_nonneg _)

theorem rankLevel_degree_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (S : F →ₗ[F2] E) (hS : d < frequencyRank S) :
    linearCoeff (rankLevel d f) S = 0 := by
  rw [linearCoeff_rankLevel, ite_eq_right (Nat.ne_of_gt hS)]

theorem rankLevel_bound_of_fourth_moment (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (η : ℝ) (hη : 0 ≤ η)
    (hfourth : (𝔼 X, rankLevel d f X ^ 4) ≤
      (2 : ℝ) ^ (113 * d * d) * η * (𝔼 X, f X)) :
    (𝔼 X, rankLevel d f X ^ 2) ≤
      (2 : ℝ) ^ (30 * d * d) * η ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2) :=
  boolean_level_bound_of_fourth_moment hf d η hη (rankLevel_inner_self d f) hfourth

variable [Finite E] [Finite F]

def IsRestrictionGlobal (f : (E →ₗ[F2] F) → ℝ) (d : ℕ) (η : ℝ) : Prop :=
  ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
      (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N ^ 2) ≤ η

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (UniqueGamesTheorem.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- On Boolean functions the restriction-global norm bound is exactly the
restriction-density hypothesis in Theorem 2.3. -/
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

def Theorem23 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ρ : ℝ), 0 < ρ → ρ < 1 →
    ∀ (f : (E →ₗ[F2] F) → ℝ), IsBoolean f →
      (∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ ρ) →
      (𝔼 X, rankLevel d f X ^ 2) ≤
        (2 : ℝ) ^ (30 * d * d) * ρ ^ ((1 : ℝ) / 4) * (𝔼 X, f X ^ 2)

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

section

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5Scalar

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
          norm_num [pow_add]
          ring
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
          norm_num [pow_add]
          ring

theorem a16_original_range (d k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) :=
  a16_finite_geometric d d d k hd

end UniqueGamesTheorem.Appendix.A5Scalar

end

end

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

theorem exponent_weight_le (d t k : ℕ) (ht : t ≤ d) (hk : k ≤ t) :
    (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have he : (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) +
      (63 * d * t + 4 * d * k) ≤ 100 * d * d := by
    simpa only [pow_two, Nat.mul_assoc, Nat.add_assoc] using
      Induction.induction_exponent_budget d t k ht hk
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  rw [pow_add] at hp
  have hn : (2 : ℝ) ^ (63 * d * t + 4 * d * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (63 * d * t + 4 * d * k)))
  rw [mul_assoc, mul_inv_cancel₀ hn, mul_one] at hm
  simpa only [inv_pow] using hm

theorem counted_weight_le (d t k c : ℕ) (ht : t ≤ d) (hk : k ≤ t)
    (hc : c ≤ 2 ^ (3 * d * t)) :
    (c : ℝ) * (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have hc' : (c : ℝ) ≤ (2 : ℝ) ^ (3 * d * t) := by exact_mod_cast hc
  calc
    _ ≤ (2 : ℝ) ^ (3 * d * t) *
        (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) :=
      mul_le_mul_of_nonneg_right hc' (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) := by
      rw [← pow_add]
      congr 1
      ring
    _ ≤ _ := exponent_weight_le d t k ht hk

variable {α β : Type*} [Fintype α] [Fintype β]

def fiber (result : α → β) (i j : α → ℕ) (b : β) (r s : ℕ) : Finset α :=
  Finset.univ.filter (fun a => result a = b ∧ i a = r ∧ j a = s)

/-- Exact finite grouping by the actual result and both dimension indices. -/
theorem sum_grouped (d : ℕ) (result : α → β) (i j : α → ℕ)
    (hbound : ∀ a, i a ≤ d ∧ j a ≤ d) (C : β → ℕ → ℕ → ℝ) :
    (∑ a, C (result a) (i a) (j a)) =
      ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        ((fiber result i j b r s).card : ℝ) * C b r s := by
  classical
  let key : α → β × ℕ × ℕ := fun a => (result a, i a, j a)
  let target : Finset (β × ℕ × ℕ) :=
    Finset.univ ×ˢ (Finset.range (d + 1) ×ˢ Finset.range (d + 1))
  let G : β × ℕ × ℕ → ℝ := fun p => C p.1 p.2.1 p.2.2
  have hmap : ∀ a ∈ (Finset.univ : Finset α), key a ∈ target := by
    intro a _
    simp only [target, key, Finset.mem_product, Finset.mem_univ,
      Finset.mem_range, true_and]
    exact ⟨Nat.lt_succ_iff.mpr (hbound a).1, Nat.lt_succ_iff.mpr (hbound a).2⟩
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := target)
    (g := key) hmap G
  simpa only [target, Finset.sum_product, G, key, Prod.mk.injEq,
    Finset.sum_const, nsmul_eq_mul, fiber] using h.symm

theorem weighted_reindex (d : ℕ) (hd : 1 ≤ d)
    (result : α → β) (i j : α → ℕ) (k : β → ℕ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (horder : ∀ a, 1 ≤ i a + j a + k (result a) ∧ i a + j a + k (result a) ≤ d)
    (hcard : ∀ b r s,
      Nat.card {a : α // result a = b ∧ i a = r ∧ j a = s} ≤
        2 ^ (3 * d * (r + s + k b))) :
    (∑ a, (2 : ℝ) ^ (100 * (d - (i a + j a + k (result a))) ^ 2 +
        24 * d * (i a + j a + k (result a)) + 6 * d * k (result a)) * w (result a)) ≤
      (2 : ℝ) ^ (100 * d * d) *
        ∑ b, ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1) + 4 * d * k b) * w b := by
  classical
  let C : β → ℕ → ℕ → ℝ := fun b r s =>
    (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
      24 * d * (r + s + k b) + 6 * d * k b) * w b
  let envelope : β → ℝ := fun b =>
    (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (4 * d * k b) * w b
  have henvelope : ∀ b, 0 ≤ envelope b := by
    intro b
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (by norm_num) _)) (hw b)
  have hbound : ∀ a, i a ≤ d ∧ j a ≤ d := by
    intro a
    have h := (horder a).2
    omega
  have hfiber : ∀ b r s,
      ((fiber result i j b r s).card : ℝ) * C b r s ≤
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
    intro b r s
    by_cases hne : (fiber result i j b r s).Nonempty
    · obtain ⟨a, ha⟩ := hne
      rcases Finset.mem_filter.mp ha with ⟨_, hr, hi, hj⟩
      have ht := horder a
      rw [hr, hi, hj] at ht
      have hc : (fiber result i j b r s).card ≤ 2 ^ (3 * d * (r + s + k b)) := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, fiber] using hcard b r s
      have hweight := counted_weight_le d (r + s + k b) (k b)
        (fiber result i j b r s).card ht.2 (by omega) hc
      rw [ite_eq_left ht.1]
      calc
        _ = (((fiber result i j b r s).card : ℝ) *
            (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
              24 * d * (r + s + k b) + 6 * d * k b)) * w b := by
          dsimp only [C]
          ring
        _ ≤ ((2 : ℝ) ^ (100 * d * d) *
            ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b) + 4 * d * k b)) * w b :=
          mul_le_mul_of_nonneg_right hweight (hw b)
        _ = envelope b * ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) := by
          dsimp only [envelope]
          rw [pow_add]
          ring
    · have hz : (fiber result i j b r s).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      rw [hz, Nat.cast_zero, zero_mul]
      apply mul_nonneg (henvelope b)
      split_ifs <;> positivity
  change (∑ a, C (result a) (i a) (j a)) ≤ _
  rw [sum_grouped d result i j hbound C]
  calc
    _ ≤ ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun s _ => hfiber b r s)
    _ = ∑ b, envelope b *
        (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
          if 1 ≤ r + s + k b then ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ b, envelope b * ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (A5Scalar.a16_original_range d (k b) hd) (henvelope b)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [envelope]
      rw [pow_add]
      ring

end UniqueGamesTheorem.Appendix.A5WeightedReindex

end

end

end OAI
