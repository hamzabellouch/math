import Mathlib
import OAI.Computability.MaxCut.Games.MatrixCharacters

namespace OAI

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace MaxCutGames.Fourier.MatrixParity

open MaxCutGames.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

/-- The rank-one shift `c τ` paired against `S` evaluates the functional `τ S`
at `c`, exactly the parity appearing in the decoding condition. -/
theorem trace_rankOne {m n : Nat} (c : Vector n) (τ : Vector m)
    (S : Matrix (Fin m) (Fin n) F2) :
    Matrix.trace (Matrix.vecMulVec c τ * S) = τ ⬝ᵥ (S *ᵥ c) := by
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

/-- Coordinate form of the requirement `τ ∘ T ≠ 0`. -/
def MatrixValid {m n : Nat} (τ : Vector m) (S : Matrix (Fin m) (Fin n) F2) : Prop :=
  τ ᵥ* S ≠ 0

theorem matrixValid_iff_exists {m n : Nat} (τ : Vector m)
    (S : Matrix (Fin m) (Fin n) F2) :
    MatrixValid τ S ↔ ∃ c : Vector n, τ ⬝ᵥ (S *ᵥ c) = 1 := by
  constructor
  · intro h
    have he : ∃ i, (τ ᵥ* S) i ≠ 0 := by
      by_contra he
      apply h
      funext i
      by_contra hi
      exact he ⟨i, hi⟩
    obtain ⟨i, hi⟩ := he
    have hone : (τ ᵥ* S) i = 1 := (scalar_cases _).resolve_left hi
    exact ⟨Pi.single i 1, by rw [Matrix.dotProduct_mulVec, dotProduct_single_one, hone]⟩
  · rintro ⟨c, hc⟩ hzero
    rw [Matrix.dotProduct_mulVec, hzero] at hc
    simp at hc

theorem exists_matrixValid {m n : Nat} (τ : Vector m) (hτ : τ ≠ 0) (hn : 0 < n) :
    ∃ S : Matrix (Fin m) (Fin n) F2, MatrixValid τ S := by
  classical
  have he : ∃ i, τ i ≠ 0 := by
    by_contra he
    apply hτ
    funext i
    by_contra hi
    exact he ⟨i, hi⟩
  obtain ⟨i, hi⟩ := he
  have hone : τ i = 1 := (scalar_cases _).resolve_left hi
  let j : Fin n := ⟨0, hn⟩
  refine ⟨Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1), ?_⟩
  unfold MatrixValid
  rw [Matrix.vecMul_vecMulVec, dotProduct_single_one, hone, one_smul]
  intro hz
  have := congrFun hz j
  simp at this

/-- Abstract linear-map form of the nonzero-parity condition. -/
theorem comp_ne_zero_iff_exists {E C : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup C] [Module F2 C]
    (τ : E →ₗ[F2] F2) (T : C →ₗ[F2] E) :
    τ.comp T ≠ 0 ↔ ∃ c, τ (T c) = 1 := by
  constructor
  · intro h
    have he : ∃ c, τ (T c) ≠ 0 := by
      by_contra he
      apply h
      ext c
      by_contra hc
      exact he ⟨c, hc⟩
    obtain ⟨c, hc⟩ := he
    exact ⟨c, (scalar_cases _).resolve_left hc⟩
  · rintro ⟨c, hc⟩ hz
    have hv := LinearMap.congr_fun hz c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hc] at hv
    exact one_ne_zero hv

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def Valid (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) : Prop := τ.comp S ≠ 0

theorem valid_iff_exists (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    Valid τ S ↔ ∃ c, τ (S c) = 1 := comp_ne_zero_iff_exists τ S

/-- Any nonzero parity functional admits a parity-valid map out of a nontrivial
binary vector space. This also proves the candidate family is nonempty. -/
theorem exists_valid [Nontrivial C] (τ : E →ₗ[F2] F2) (hτ : τ ≠ 0) :
    ∃ S : C →ₗ[F2] E, Valid τ S := by
  classical
  have he : ∃ e, τ e ≠ 0 := by
    by_contra he
    apply hτ
    ext e
    by_contra he'
    exact he ⟨e, he'⟩
  obtain ⟨e, he⟩ := he
  obtain ⟨c, hc⟩ := exists_ne (0 : C)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F2 hc
  refine ⟨φ.smulRight e, (valid_iff_exists τ _).mpr ⟨c, ?_⟩⟩
  rw [LinearMap.smulRight_apply, hφ, one_smul]
  exact (scalar_cases _).resolve_left he

/-- Generic trace pairing of a rank-one color shift. -/
theorem trace_smulRight_comp [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (c : C) (S : C →ₗ[F2] E) :
    LinearMap.trace F2 C ((τ.smulRight c).comp S) = τ (S c) := by
  have heq : (τ.smulRight c).comp S = (τ.comp S).smulRight c := by
    ext x
    rfl
  rw [heq, LinearMap.trace_smulRight, LinearMap.comp_apply]

/-- The exact number of binary linear maps, supplying the count in (5.20).
Taking `E` to be the subspace `W` counts precisely maps whose image lies in `W`. -/
theorem card_linearMaps [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] :
    Fintype.card (C →ₗ[F2] E) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 E) := by
  classical
  let bC := Module.finBasis F2 C
  let bE := Module.finBasis F2 E
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (LinearMap.toMatrix bC bE).toEquiv]
  change Nat.card (Fin (Module.finrank F2 E) → Fin (Module.finrank F2 C) → F2) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [F2, Integration.BinaryLinear.F2, Nat.card_eq_fintype_card, ← pow_mul,
    Nat.mul_comm]

theorem card_linearMaps_le [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] (r s : Nat)
    (hE : Module.finrank F2 E ≤ r) (hC : Module.finrank F2 C ≤ s) :
    Fintype.card (C →ₗ[F2] E) ≤ 2 ^ (r * s) := by
  rw [card_linearMaps]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  calc
    Module.finrank F2 C * Module.finrank F2 E ≤ s * r := Nat.mul_le_mul hC hE
    _ = r * s := Nat.mul_comm s r

end LinearMaps

section Folding

variable {E C D : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype C]
  [AddCommGroup D] [Module F2 D]

/-- A folded map hits a fixed color at most once along its `C`-shift orbit.
The injection models the inclusion of the subspace `C'` in the full color space. -/
theorem folded_indicator_sum_le_one (τ : E →ₗ[F2] F2)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (X : E →ₗ[F2] C) (y : D) :
    (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) ≤ 1 := by
  classical
  let hits : Finset C := Finset.univ.filter fun c => F (X + τ.smulRight c) = y
  have hcard : hits.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : F (X + τ.smulRight a) = y := (Finset.mem_filter.mp ha).2
    have hb' : F (X + τ.smulRight b) = y := (Finset.mem_filter.mp hb).2
    apply inclusion_injective
    apply add_left_cancel (a := F X)
    simpa only [folded] using ha'.trans hb'.symm
  have hsum : (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) =
      (hits.card : ℝ) := by
    simp only [hits, Finset.sum_boole]
  rw [hsum]
  exact_mod_cast hcard

/-- Equation (5.19)'s first bound, with the actual finite folded shift average. -/
theorem folded_indicator_average_le (τ : E →ₗ[F2] F2)
    (inclusion : C →ₗ[F2] D) (inclusion_injective : Function.Injective inclusion)
    (F : (E →ₗ[F2] C) → D)
    (folded : ∀ X c, F (X + τ.smulRight c) = F X + inclusion c)
    (X : E →ₗ[F2] C) (y : D) :
    (∑ c : C, if F (X + τ.smulRight c) = y then (1 : ℝ) else 0) /
        Fintype.card C ≤ 1 / (Fintype.card C : ℝ) := by
  exact div_le_div_of_nonneg_right
    (folded_indicator_sum_le_one τ inclusion inclusion_injective F folded X y)
    (Nat.cast_nonneg _)

end Folding

open MatrixCharacters hiding F2

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- The character of the color-shift group indexed by the functional `τ S`. -/
def parityCharacter (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) : AddChar C ℂ where
  toFun c := binarySign (τ (S c))
  map_zero_eq_one' := by simp
  map_add_eq_mul' c d := by simp only [map_add, binarySign_add]

theorem parityCharacter_eq_zero_iff (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    parityCharacter τ S = 0 ↔ τ.comp S = 0 := by
  constructor
  · intro h
    ext c
    apply binarySign_injective
    have hc := congrArg (fun ψ : AddChar C ℂ => ψ c) h
    simpa [parityCharacter] using hc
  · intro h
    ext c
    have hc := LinearMap.congr_fun h c
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hc
    simp [parityCharacter, hc]

/-- Unnormalized annihilator identity for exactly the `c τ` shift subgroup. -/
theorem linearTrace_shift_sum [Fintype C] [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    (∑ c : C, linearTraceCharacter S (τ.smulRight c)) =
      if τ.comp S = 0 then (Fintype.card C : ℂ) else 0 := by
  classical
  simp only [linearTraceCharacter_apply, linearTracePair, trace_smulRight_comp]
  change (∑ c : C, parityCharacter τ S c) = _
  rw [AddChar.sum_eq_ite]
  simp only [parityCharacter_eq_zero_iff]

/-- Averaging the Fourier character in the folding directions kills precisely
the indices with nonzero `τ S`, the multiplier used in Equation (5.19). -/
theorem linearTrace_shift_average [Fintype C] [FiniteDimensional F2 C]
    (τ : E →ₗ[F2] F2) (S : C →ₗ[F2] E) :
    (∑ c : C, linearTraceCharacter S (τ.smulRight c)) / (Fintype.card C : ℂ) =
      if τ.comp S = 0 then 1 else 0 := by
  classical
  rw [linearTrace_shift_sum]
  split <;> simp [Fintype.card_ne_zero]

end MaxCutGames.Fourier.MatrixParity
end

end OAI
