import Mathlib
import OAI.Computability.MaxCut.Games.BaseDetection

namespace OAI

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace MaxCutGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

noncomputable def average {A : Type*} [Finite A] (f : A → ℚ) : ℚ :=
  letI := Fintype.ofFinite A
  𝔼 a, f a

theorem average_eq_expect {A : Type*} [Fintype A] (f : A → ℚ) :
    average f = 𝔼 a, f a := by
  have he : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  unfold average
  rw [he]

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

/-- Uniform finite input and the stage's actual uniform finite noise choices. -/
noncomputable def error (s : Stage k B) : ℚ := by
  classical
  exact average (fun n : s.Noise => average (fun u : s.Input =>
    if s.output (u + s.noise n) ≠ s.output u then 1 else 0))

theorem error_eq_expect [DecidableEq B] (s : Stage k B) [Fintype s.Input] [Fintype s.Noise] :
    error s = 𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0 := by
  classical
  simp only [error, average_eq_expect]
  apply Finset.expect_congr rfl
  intro n _
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

variable [Fintype B] [DecidableEq B]

theorem base_error : error (Stage.base (k := k) (B := B)) =
    1 - 1 / (Fintype.card B : ℚ) := by
  classical
  let : Fintype (Stage.base (k := k) (B := B)).Input := ‹Fintype B›
  let : Fintype (Stage.base (k := k) (B := B)).Noise := ‹Fintype B›
  rw [error_eq_expect]
  change (𝔼 a : B, 𝔼 u : B, if u + a ≠ u then (1 : ℚ) else 0) = _
  have hpoint (a u : B) : (u + a ≠ u) ↔ a ≠ 0 := by
    constructor
    · intro h ha
      exact h (by rw [ha, add_zero])
    · intro ha h
      apply ha
      exact add_left_cancel (show u + a = u + 0 by simpa only [add_zero] using h)
  simp_rw [hpoint, Fintype.expect_const]
  calc
    (𝔼 a : B, if a ≠ 0 then (1 : ℚ) else 0) =
        𝔼 a : B, (1 - if a = 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    _ = 1 - (𝔼 a : B, if a = 0 then (1 : ℚ) else 0) := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
    _ = _ := by simp []

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X] [Fintype X]

/-- The exact one-level law for the actual stage constructor. -/
theorem next_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (s : Stage k B) : error (Stage.next J hJ Q s) = ρ * error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let : Fintype (Stage.next J hJ Q s).Input := inferInstanceAs (Fintype (I → s.Input))
  let : Fintype (Stage.next J hJ Q s).Noise := inferInstanceAs (Fintype (I × s.Noise))
  simp only [error_eq_expect]
  change (𝔼 t : I × s.Noise, 𝔼 u : I → s.Input,
    if parentOutput J s.output Q (u + (Pi.single t.1 (s.noise t.2) : I → s.Input)) ≠
      parentOutput J s.output Q u then (1 : ℚ) else 0) =
    ρ * (𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0)
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact NonlinearRecurrence.parent_change_recurrence J hJ s.embed s.logical
    s.logical_surjective s.output s.equivariant (fun p => p.2 + Q p.1) s.noise ρ hk

/-- Solving the proved recurrence, with the actual height-zero probability. -/
theorem iterate_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (n : ℕ) : error (Stage.iterate J hJ Q n) =
      (1 - 1 / (Fintype.card B : ℚ)) * ρ ^ n := by
  induction n with
  | zero => simp [Stage.iterate_zero, base_error]
  | succ n ih =>
    rw [Stage.iterate_succ, next_error J hJ Q ρ hk, ih, pow_succ]
    ac_rfl

/-- The quotient uses the original noise choices and preserves their full
uniform-input change probability. -/
theorem quotient_error (s : Stage k B) : error (StageQuotient.toStage s) = error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let := Fintype.ofFinite (StageQuotient.Space s)
  let : Fintype (StageQuotient.toStage s).Input := inferInstanceAs (Fintype (StageQuotient.Space s))
  let : Fintype (StageQuotient.toStage s).Noise := inferInstanceAs (Fintype s.Noise)
  simp only [error_eq_expect]
  change (𝔼 n : s.Noise, 𝔼 x : StageQuotient.Space s,
    if StageQuotient.output s (x + StageQuotient.noise s n) ≠
      StageQuotient.output s x then (1 : ℚ) else 0) =
    𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0
  apply Finset.expect_congr rfl
  intro n _
  calc
    _ = 𝔼 u : s.Input,
      if StageQuotient.output s (StageQuotient.projection s u + StageQuotient.noise s n) ≠
        StageQuotient.output s (StageQuotient.projection s u) then (1 : ℚ) else 0 :=
      (EmbeddedConditional.expect_linear_surjective (StageQuotient.projection s)
        (StageQuotient.projection_surjective s)
        (fun x : StageQuotient.Space s =>
          if StageQuotient.output s (x + StageQuotient.noise s n) ≠
            StageQuotient.output s x then (1 : ℚ) else 0)).symm
    _ = _ := by simp only [StageQuotient.noise_change_iff]

end MaxCutGames.Gadget.StageNoiseRecurrence

/-!
The spanning clause of v2 Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F]

/-- The three standard coordinate vectors of the quadratic block. -/
def basisCoord (i : Fin 3) : Vec F := Pi.single i 1

theorem basisCoord_ne_zero (i : Fin 3) : (basisCoord i : Vec F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisCoord] at hi

@[simp] theorem Q_smul_basisCoord (t : F) (i : Fin 3) :
    Q (t • (basisCoord i : Vec F)) = 0 := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [Q, basisCoord]

theorem dot_smul_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    dot (basisCoord j : Vec F) (t • (basisCoord i : Vec F)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot, basisCoord]

/-- The explicit coordinate decomposition, over the field rather than only
over the binary scalars of the block spaces. -/
theorem basisCoord_decomposition (x : Vec F) :
    x = x 0 • basisCoord 0 + x 1 • basisCoord 1 + x 2 • basisCoord 2 := by
  ext i
  fin_cases i <;> simp [basisCoord]

variable [CharP F 2] [Algebra (ZMod 2) F]

theorem horizontal_mem_U_basisCoord (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈ U (basisCoord i) := by
  refine ⟨(mem_line_iff _ _).mpr ⟨t, rfl⟩, ?_⟩
  change dot (basisCoord i) (0 + Q (t • basisCoord i)) = 0
  simp

theorem vertical_mem_U_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    ((0 : Vec F), t • basisCoord i) ∈ U (basisCoord j) := by
  refine ⟨(line _).zero_mem, ?_⟩
  change dot (basisCoord j) (t • basisCoord i + Q 0) = 0
  simpa using dot_smul_basisCoord_of_ne t i j hij

/-- The binary span of the three coordinate block spaces. -/
def coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F) :=
  (U (basisCoord 0) ⊔ U (basisCoord 1)) ⊔ U (basisCoord 2)

theorem U_basisCoord_le_coordinateBlockSpan (i : Fin 3) :
    U (basisCoord i) ≤ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  fin_cases i
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right

theorem horizontal_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
  U_basisCoord_le_coordinateBlockSpan i (horizontal_mem_U_basisCoord t i)

theorem vertical_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    ((0 : Vec F), t • basisCoord i) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  have h (j : Fin 3) (hij : i ≠ j) :
      ((0 : Vec F), t • basisCoord i) ∈
        (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
    U_basisCoord_le_coordinateBlockSpan j (vertical_mem_U_basisCoord_of_ne t i j hij)
  fin_cases i
  · exact h 1 (by decide)
  · exact h 0 (by decide)
  · exact h 0 (by decide)

/-- Every pair is a sum of three horizontal and three vertical coordinate
pairs, all already in the sum of the coordinate blocks. -/
theorem mem_coordinateBlockSpan (p : Vec F × Vec F) :
    p ∈ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  let S : Submodule (ZMod 2) (Vec F × Vec F) := coordinateBlockSpan
  have hh : (p.1, (0 : Vec F)) ∈ S := by
    have h := S.add_mem
      (S.add_mem (horizontal_mem_coordinateBlockSpan (p.1 0) 0)
        (horizontal_mem_coordinateBlockSpan (p.1 1) 1))
      (horizontal_mem_coordinateBlockSpan (p.1 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have hv : ((0 : Vec F), p.2) ∈ S := by
    have h := S.add_mem
      (S.add_mem (vertical_mem_coordinateBlockSpan (p.2 0) 0)
        (vertical_mem_coordinateBlockSpan (p.2 1) 1))
      (vertical_mem_coordinateBlockSpan (p.2 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have h := S.add_mem hh hv
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using h

theorem coordinateBlockSpan_eq_top :
    (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) = ⊤ := by
  apply top_unique
  intro p _
  exact mem_coordinateBlockSpan p

/-- The block spaces for all nonzero line generators span the whole ambient
binary vector space.  The proof uses just the three coordinate generators. -/
theorem iSup_U_nonzero_eq_top :
    (⨆ v : {v : Vec F // v ≠ 0}, U v.1) = ⊤ := by
  apply top_unique
  rw [← coordinateBlockSpan_eq_top (F := F)]
  unfold coordinateBlockSpan
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 0, basisCoord_ne_zero 0⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 1, basisCoord_ne_zero 1⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 2, basisCoord_ne_zero 2⟩

end MaxCutGames.Quadratic

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

noncomputable section

open scoped BigOperators

namespace MaxCutGames.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [Fintype (BlockOrientationIndex F)]

def blockEmbedding (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def blockAggregate : (BlockOrientationIndex F → Vec F) →ₗ[ZMod 2] Vec F × Vec F :=
  Gadget.aggregate (blockEmbedding (F := F))

theorem blockAggregate_single [DecidableEq (BlockOrientationIndex F)]
    (i : BlockOrientationIndex F) (b : Vec F) :
    blockAggregate (Pi.single i b) = blockEmbedding i b := by
  classical
  change (∑ j : BlockOrientationIndex F,
    blockEmbedding j ((Pi.single i b : BlockOrientationIndex F → Vec F) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fieldLine_block_le_range_aggregate (A : FieldLine F) :
    U (lineGenerator A) ≤ LinearMap.range (blockAggregate (F := F)) := by
  classical
  intro p hp
  let J := chosenBlockOrientation A
  let i : BlockOrientationIndex F := ⟨A, J⟩
  obtain ⟨b, hb⟩ := J.surjective ⟨p, hp⟩
  refine ⟨Pi.single i b, ?_⟩
  rw [blockAggregate_single]
  change ((J b : U (lineGenerator A)) : Vec F × Vec F) = p
  exact congrArg Subtype.val hb

/-- All blocks occur in the actual pair-indexed aggregate.  Their already
proved span is the entire horizontal/vertical space, so the aggregate is
surjective, as required by the recursive shift construction. -/
theorem blockAggregate_surjective : Function.Surjective (blockAggregate (F := F)) := by
  have hspan : (⨆ v : {v : Vec F // v ≠ 0}, U v.1) ≤
      LinearMap.range (blockAggregate (F := F)) := by
    apply iSup_le
    intro v
    let A : FieldLine F := Projectivization.mk F v.1 v.2
    have hl : line (lineGenerator A) = line v.1 := by
      simpa only [A, Projectivization.submodule_mk, line] using line_lineGenerator A
    have hm : lineGenerator A ∈ line v.1 := by
      rw [← hl]
      exact (mem_line_iff _ _).mpr ⟨1, one_smul _ _⟩
    have hu := U_eq_of_nonzero_mem_line (lineGenerator_ne_zero A) hm
    simpa only [hu] using fieldLine_block_le_range_aggregate A
  rw [iSup_U_nonzero_eq_top] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem aggregate_blockEmbedding_surjective :
    Function.Surjective (Gadget.aggregate (blockEmbedding (F := F))) :=
  blockAggregate_surjective

end MaxCutGames.Quadratic
end

noncomputable section

namespace MaxCutGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance automorphismFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
noncomputable local instance automorphismFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Fintype.ofFinite _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

theorem actual_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      NonlinearRecurrence.change (fun z => z.2 + Q z.1) p (blockEmbedding i d)) =
      rate F := by
  classical
  exact OrientedBlockKernel.mean_oriented_block_kernel d hd

/-- The actual recursive spaces, shifts, outputs and finite leaf-noise sampler. -/
noncomputable def stage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  Stage.iterate (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n

theorem stage_error (n : ℕ) :
    StageNoiseRecurrence.error (stage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  have he := StageNoiseRecurrence.iterate_error (blockEmbedding (F := F))
    aggregate_blockEmbedding_surjective Q (rate F) actual_kernel n
  simpa only [stage, Vec, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.card_eq_fintype_card] using he

/-- The logical alphabet is an actual injected shift subspace after quotient. -/
noncomputable def quotientStage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  StageQuotient.toStage (stage (F := F) n)

theorem quotientStage_error (n : ℕ) :
    StageNoiseRecurrence.error (quotientStage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  rw [quotientStage, StageNoiseRecurrence.quotient_error, stage_error]

end MaxCutGames.Gadget.QuadraticStageNoise
end

namespace MaxCutGames.Gadget.Parameters

open Harmonic
open scoped BigOperators

/-- Every block from `n+1` through `2n` adds at least one half. -/
theorem harmonic_double (n : ℕ) (hn : 0 < n) :
    MaxCutGames.Gadget.Harmonic.harmonic n + 1 / 2 ≤ MaxCutGames.Gadget.Harmonic.harmonic (2 * n) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hsplit : MaxCutGames.Gadget.Harmonic.harmonic (2 * n) = MaxCutGames.Gadget.Harmonic.harmonic n +
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    rw [harmonic_eq_sum, show 2 * n = n + n by omega, Finset.sum_range_add]
    rw [← harmonic_eq_sum n]
  have hs : (∑ _i ∈ Finset.range n, (2 * (n : ℚ))⁻¹) ≤
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply inv_anti₀ (by positivity)
    exact_mod_cast (show n + i + 1 ≤ 2 * n by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (n : ℚ) * (2 * (n : ℚ))⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt hnq]
  rw [he] at hs
  rw [hsplit]
  linarith

theorem harmonic_pow_two (k : ℕ) : (k : ℚ) / 2 ≤ MaxCutGames.Gadget.Harmonic.harmonic (2 ^ k) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_div, pow_zero] using harmonic_nonneg 1
  | succ k ih =>
    have hd := harmonic_double (2 ^ k) (pow_pos (by decide) _)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    linarith

/-- Computable rank exceeding any prescribed rational MaxCutGames.Gadget.Harmonic.harmonic level. -/
def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

theorem rankFor_pos (level : ℚ) : 0 < rankFor level := by
  unfold rankFor
  positivity

theorem le_harmonic_rankFor (level : ℚ) : level ≤ MaxCutGames.Gadget.Harmonic.harmonic (rankFor level) := by
  have hc := Nat.le_ceil (2 * level)
  have hh := harmonic_pow_two ⌈2 * level⌉₊
  change level ≤ MaxCutGames.Gadget.Harmonic.harmonic (2 ^ ⌈2 * level⌉₊)
  linarith

theorem harmonic_unbounded (level : ℚ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ level ≤ MaxCutGames.Gadget.Harmonic.harmonic r₀ :=
  ⟨rankFor level, rankFor_pos level, le_harmonic_rankFor level⟩

/-- Strictly positive genericity error meeting the MaxCutGames.Gadget.Harmonic.harmonic bad-rank budget. -/
def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

theorem genericityError_pos (r₀ : ℕ) : 0 < genericityError r₀ := by
  unfold genericityError
  have := badRankCoefficient_nonneg r₀
  positivity

theorem genericityError_lt_one (r₀ : ℕ) : genericityError r₀ < 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem genericityError_budget (r₀ : ℕ) :
    badRankCoefficient r₀ * genericityError r₀ ≤ 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  rw [← mul_div_assoc, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith

/-- The geometric decay has an elementary reciprocal upper bound. -/
theorem geometric_reciprocal_bound (θ : ℚ) (_hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (n : ℕ) : (1 - θ) ^ n * (1 + (n : ℚ) * θ) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (1 - θ) ^ n := pow_nonneg (sub_nonneg.mpr hθone) _
    have hn : (0 : ℚ) ≤ n := by positivity
    have hstep : (1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ) ≤
        1 + (n : ℚ) * θ := by
      push_cast
      nlinarith [sq_nonneg θ, mul_nonneg hn (sq_nonneg θ)]
    calc
      (1 - θ) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℚ) * θ) =
          (1 - θ) ^ n * ((1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - θ) ^ n * (1 + (n : ℚ) * θ) :=
        mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

/-- The chosen MaxCutGames.Gadget.Harmonic.harmonic depth works uniformly for every subsequent
`0 < θ ≤ 1`. Thus the rank can be selected before the field/noise parameter. -/
theorem geometric_at_depth_le (p θ : ℚ) (r₀ : ℕ) (hp : 0 < p)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hlarge : 8 * (p⁻¹ + 1) ≤ MaxCutGames.Gadget.Harmonic.harmonic r₀) :
    (1 - θ) ^ depth r₀ θ ≤ p := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.lt_floor_add_one (MaxCutGames.Gadget.Harmonic.harmonic r₀ / (8 * θ))
  have hf' := (div_lt_iff₀ hden).mp hf
  change MaxCutGames.Gadget.Harmonic.harmonic r₀ < ((depth r₀ θ : ℚ) + 1) * (8 * θ) at hf'
  have hnθ : p⁻¹ ≤ (depth r₀ θ : ℚ) * θ := by nlinarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have hm := mul_le_mul_of_nonneg_left hnθ (le_of_lt hp)
  simp only [mul_inv_cancel₀ hpne] at hm
  have hr := geometric_reciprocal_bound θ (le_of_lt hθ) hθone (depth r₀ θ)
  have hb : 1 ≤ p * (1 + (depth r₀ θ : ℚ) * θ) := by nlinarith
  have hpositive : 0 < 1 + (depth r₀ θ : ℚ) * θ := by positivity
  exact (mul_le_mul_iff_left₀ hpositive).mp (by simpa only [mul_comm] using hr.trans hb)

/-- Explicit threshold depending only on the requested nonlinear error. -/
def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

theorem initialRank_pos (p : ℚ) : 0 < initialRank p := rankFor_pos _

theorem initialRank_large (p : ℚ) :
    8 * (p⁻¹ + 1) ≤ MaxCutGames.Gadget.Harmonic.harmonic (initialRank p) := le_harmonic_rankFor _

/-- All scalar choices needed before the field dimension is selected. -/
theorem effective_parameters (p : ℚ) (hp : 0 < p) :
    ∃ r₀ : ℕ, ∃ ε : ℚ,
      0 < r₀ ∧ 0 < ε ∧ ε < 1 ∧ badRankCoefficient r₀ * ε ≤ 1 ∧
      ∀ θ : ℚ, 0 < θ → θ ≤ 1 → (1 - θ) ^ depth r₀ θ ≤ p := by
  refine ⟨initialRank p, genericityError (initialRank p), initialRank_pos p,
    genericityError_pos _, genericityError_lt_one _, genericityError_budget _, ?_⟩
  intro θ hθ hθone
  exact geometric_at_depth_le p θ (initialRank p) hp hθ hθone (initialRank_large p)

end MaxCutGames.Gadget.Parameters

end OAI
