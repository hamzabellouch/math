import Mathlib
import OAI.Computability.MaxCut.Games.StageNoiseRecurrence
import OAI.Computability.MaxCut.Games.SeparationCertificate

namespace OAI

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

namespace MaxCutGames.Quadratic

/-- The degree-`d` binary Galois field.  Cardinality statements below require
`d > 0`; the degenerate exponent zero is deliberately excluded. -/
abbrev BinaryField (d : ℕ) := GaloisField 2 d

theorem card_binaryField (d : ℕ) (hd : 0 < d) :
    Nat.card (BinaryField d) = 2 ^ d :=
  GaloisField.card 2 d (Nat.ne_of_gt hd)

theorem finrank_binaryField (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (BinaryField d) = d :=
  GaloisField.finrank 2 (Nat.ne_of_gt hd)

theorem finrank_binaryField_triple (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (Fin 3 → BinaryField d) = 3 * d := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (BinaryField d) (Fin 3 → BinaryField d),
    finrank_binaryField d hd, Module.finrank_fin_fun, mul_comm]

/-- A deliberately simple explicit upper choice; optimization of the field
size is irrelevant because these thresholds are fixed before the input. -/
def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

theorem fieldDegree_pos (N r : ℕ) : 0 < fieldDegree N r := by
  simp [fieldDegree]

theorem threshold_lt_two_pow_fieldDegree (N r : ℕ) : N < 2 ^ fieldDegree N r := by
  have h : N ≤ fieldDegree N r := by unfold fieldDegree; omega
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem rankThreshold_le_triple_fieldDegree (N r : ℕ) : r ≤ 3 * fieldDegree N r := by
  unfold fieldDegree
  omega

theorem exists_binary_field_degree (N r : ℕ) :
    ∃ d : ℕ, 0 < d ∧ N < 2 ^ d ∧ r ≤ 3 * d :=
  ⟨fieldDegree N r, fieldDegree_pos N r, threshold_lt_two_pow_fieldDegree N r,
    rankThreshold_le_triple_fieldDegree N r⟩

/-- Simultaneous cardinality and rank threshold attainment by the same field. -/
theorem chosen_binaryField_thresholds (N r : ℕ) :
    N < Nat.card (BinaryField (fieldDegree N r)) ∧
      r ≤ Module.finrank (ZMod 2) (Fin 3 → BinaryField (fieldDegree N r)) := by
  rw [card_binaryField _ (fieldDegree_pos N r),
    finrank_binaryField_triple _ (fieldDegree_pos N r)]
  exact ⟨threshold_lt_two_pow_fieldDegree N r, rankThreshold_le_triple_fieldDegree N r⟩

end MaxCutGames.Quadratic

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

namespace MaxCutGames.Quadratic

open scoped BigOperators
open MaxCutGames.Gadget.Orientation

noncomputable section

noncomputable instance binaryFieldFintype (d : ℕ) : Fintype (BinaryField d) :=
  Fintype.ofFinite _

/-- Simultaneous quantitative genericity, with the precise threshold order
used by the latent gadget.  The conclusion covers rank zero as well. -/
theorem exists_uniform_generic_field (r₀ : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ r₀ ≤ 3 * d ∧
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction (BinaryField d) r ≤ ε) ∧
      (∃ S : RankSpace (ZMod 2) (Fin 3 → BinaryField d) r₀, IsGeneric S.1) := by
  classical
  have hex (r : ℕ) := exists_generic_subspace_error_numerator (Fin r)
  choose D hD hbound using hex
  let M : ℕ := ∑ r ∈ Finset.range (r₀ + 1), D r
  have hDM (r : ℕ) (hr : r ≤ r₀) : D r ≤ M := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (M : ℚ)) (2 * (M : ℚ) / ε))
  let d := fieldDegree N r₀
  have hd : 0 < d := fieldDegree_pos N r₀
  have hqN : (N : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        (chosen_binaryField_thresholds N r₀).1)
  have hq : (0 : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast Fintype.card_pos
  have hqM : 2 * (M : ℚ) < Fintype.card (BinaryField d) :=
    (le_max_left _ _).trans_lt (hN.trans hqN)
  have hqε : 2 * (M : ℚ) / ε < Fintype.card (BinaryField d) :=
    (le_max_right _ _).trans_lt (hN.trans hqN)
  have hεq : 2 * (M : ℚ) < (Fintype.card (BinaryField d) : ℚ) * ε :=
    (div_lt_iff₀ hε).mp hqε
  have hsmall (r : ℕ) (hr : r ≤ r₀) :
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ 1 / 2 ∧
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ ε / 2 := by
    have hDr : (D r : ℚ) ≤ M := by exact_mod_cast hDM r hr
    constructor
    · apply (div_le_iff₀ hq).mpr
      nlinarith
    · apply (div_le_iff₀ hq).mpr
      nlinarith
  have hready (r : ℕ) (hr : r ≤ r₀) :=
    hbound r (BinaryField d) (show (D r : ℚ) / Fintype.card (BinaryField d) < 1 by
      have := (hsmall r hr).1
      linarith)
  refine ⟨d, hd, rankThreshold_le_triple_fieldDegree N r₀, ?_, ?_⟩
  · intro r hr
    have hb := (hready r hr).2
    simp only [Fintype.card_fin] at hb
    apply hb.trans
    exact conditional_error_le_of_small _ _
      (div_nonneg (Nat.cast_nonneg _) hq.le) (hsmall r hr).1 (hsmall r hr).2
  · obtain ⟨S, hS⟩ := (hready r₀ le_rfl).1
    refine ⟨⟨S.1, ?_⟩, hS⟩
    simpa only [Fintype.card_fin] using S.2

end

end MaxCutGames.Quadratic

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

namespace MaxCutGames.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem theta_le_one : fieldLineTheta F ≤ 1 := by
  have hc : (1 : ℚ) ≤ Nat.card (FieldLine F) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_FieldLine_pos (F := F)))
  exact (inv_anti₀ (by norm_num : (0 : ℚ) < 1) hc).trans_eq (by norm_num)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rate_eq_one_sub_theta : rate F = 1 - fieldLineTheta F := by
  rw [rate, fieldLineTheta_eq, one_div]

/-- Detection for the actual quotient, with every whole-recursion estimate
discharged by the adaptive harmonic argument. -/
theorem quotient_detection
    (r₀ : ℕ) (ε : ℚ) (hr₀ : 0 < r₀)
    (hbudget : badRankCoefficient r₀ * ε ≤ 1)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
    (S₀ : Submodule (ZMod 2) (Vec F))
    (hrank : Module.finrank (ZMod 2) S₀ = r₀) (hS₀ : IsGeneric S₀)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (T : (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).Input →ₗ[ZMod 2] E)
    (hinj : Function.Injective
      (T.comp (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).embed)) :
    (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
      if T ((quotientStage (F := F) (depth r₀ (fieldLineTheta F))).noise t) ≠ 0
      then 1 else 0) := by
  classical
  let n := depth r₀ (fieldLineTheta F)
  let : Fintype (stage (F := F) n).Noise := DescentProbability.noiseFintype
    (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n
  have hJ : Function.Surjective
      (aggregate (OrientedBlockKernel.orientedBlockLinear (F := F))) := by
    exact aggregate_blockEmbedding_surjective (F := F)
  have hfull : ∀ L : Lift (stage (F := F) n)
      (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Vec F))),
      (1 / 4 : ℚ) ≤ probability (fun t => ∃ z, L.family z ((stage n).noise t) ≠ 0) := by
    intro L
    exact BaseDetection.full_lift_detection hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  have h := QuotientDetection.target_detection_after_quotient
    (stage (F := F) n) T (1 / 4) hfull hinj
  change (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average
    (fun t : (stage (F := F) n).Noise =>
      if T (StageQuotient.noise (stage (F := F) n) t) ≠ 0 then 1 else 0)
  rw [StageNoiseRecurrence.average_eq_expect]
  exact h

/-- The exact nonlinear recurrence satisfies the scalar budget fixed before
the field was selected. -/
theorem quotient_error_le (p : ℚ) (r₀ : ℕ)
    (hgeom : (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) ≤ p) :
    StageNoiseRecurrence.error
      (quotientStage (F := F) (depth r₀ (fieldLineTheta F))) ≤ p := by
  rw [quotientStage_error, rate_eq_one_sub_theta]
  have hpow : 0 ≤ (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) :=
    pow_nonneg (sub_nonneg.mpr theta_le_one) _
  have hcoef : 1 - 1 / (Nat.card F : ℚ) ^ 3 ≤ 1 :=
    sub_le_self _ (by positivity)
  exact (mul_le_of_le_one_left hpow hcoef).trans hgeom

/-- The unconditional finite base endpoint. All choices depend only on `p`;
the larger logical alphabet used by the final enlargement is absent here. -/
theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  obtain ⟨r₀, ε, hr₀, hε, _hεone, hbudget, hgeom⟩ := effective_parameters p hp
  obtain ⟨d, hd, _hdim, hgeneric, S₀, hS₀⟩ :=
    exists_uniform_generic_field r₀ ε hε
  refine ⟨d, hd, depth r₀ (fieldLineTheta (BinaryField d)), ?_, ?_⟩
  · exact quotient_error_le p r₀
      (hgeom _ BaseDetection.theta_pos theta_le_one)
  · intro E _ _ T hinj
    exact quotient_detection r₀ ε hr₀ hbudget hgeneric S₀.1 S₀.2 hS₀ T hinj

end

end MaxCutGames.Gadget.BaseConstruction

namespace MaxCutGames.Gadget.Enlargement

open scoped BigOperators Classical

noncomputable section

/-- Uniform finite probability, kept rational because the gadget noise is a
pushforward of finite uniform choices. -/
def probability {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℚ :=
  (Nat.card {x : Ω // p x} : ℚ) / (Nat.card Ω : ℚ)

/-- A union bound without independence assumptions. -/
theorem probability_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (p : I → Ω → Prop) :
    probability (fun x => ∃ i, p i x) ≤ ∑ i, probability (p i) := by
  classical
  have heq : (Finset.univ.filter fun x => ∃ i, p i x) =
      Finset.univ.biUnion (fun i => Finset.univ.filter (p i)) := by
    ext x
    simp
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [heq, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset I))
    (t := fun i => Finset.univ.filter (p i)))

/-- Equal-size fibers determine the exact probability of every target event. -/
theorem probability_preimage_of_fibers {Ω T : Type*} [Fintype Ω] [Fintype T]
    [Nonempty Ω] [Nonempty T] (f : Ω → T)
    (hf : ∀ x y : T, Nat.card {a : Ω // f a = x} = Nat.card {a : Ω // f a = y})
    (p : T → Prop) : probability (fun a => p (f a)) = probability p := by
  classical
  let t₀ : T := Classical.choice inferInstance
  let c := (Finset.univ.filter fun a => f a = t₀).card
  have hfc (x : T) : (Finset.univ.filter fun a => f a = x).card = c := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hf x t₀
  have hΩ : Fintype.card Ω = Fintype.card T * c := by
    calc
      Fintype.card Ω = ∑ t : T, (Finset.univ.filter fun a => f a = t).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = Fintype.card T * c := by simp_rw [hfc]; simp
  have hp : (Finset.univ.filter fun a => p (f a)).card =
      (Finset.univ.filter p).card * c := by
    calc
      _ = ∑ t ∈ Finset.univ.filter p,
          (Finset.univ.filter fun a => f a = t).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset Ω) (Finset.univ.filter p) f
      _ = _ := by simp_rw [hfc]; simp
  have hc : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by
      intro hc
      have := Fintype.card_pos (α := Ω)
      simp [hc] at hΩ
    exact_mod_cast this
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hp, hΩ]
  push_cast
  exact mul_div_mul_right _ _ hc

/-- Automorphisms act transitively on the nonzero vectors. This follows by
extending an isomorphism between the two one-dimensional spans. -/
theorem exists_equiv_map_nonzero {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[F] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton F V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton F V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

abbrev LinearInjection (F B K : Type*) [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K] :=
  {L : B →ₗ[F] K // Function.Injective L}

theorem linearInjection_nonempty_of_finrank_le {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K) :
    Nonempty (LinearInjection F B K) := by
  obtain ⟨L, hL⟩ := finrank_le_iff_exists_linearMap.mp h
  exact ⟨⟨L, hL⟩⟩

/-- Postcomposition permutes all linear injections, including their uniform
finite distribution. -/
def postcompose {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] (e : K ≃ₗ[F] K) :
    LinearInjection F B K ≃ LinearInjection F B K where
  toFun L := ⟨e.toLinearMap.comp L.1, e.injective.comp L.2⟩
  invFun L := ⟨e.symm.toLinearMap.comp L.1, e.symm.injective.comp L.2⟩
  left_inv L := by
    apply Subtype.ext
    ext x
    exact e.symm_apply_apply (L.1 x)
  right_inv L := by
    apply Subtype.ext
    ext x
    exact e.apply_symm_apply (L.1 x)

theorem injection_eval_ne_zero {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    (L : LinearInjection F B K) {b : B} (hb : b ≠ 0) : L.1 b ≠ 0 := by
  intro h
  apply hb
  apply L.2
  simpa using h

/-- Every nonzero target vector is hit by an injection at any prescribed
nonzero base vector. This is the surjectivity ingredient of the product-shift
map used before taking the quotient. -/
theorem exists_injection_hitting_nonzero {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ L : LinearInjection F B K, L.1 b = x := by
  obtain ⟨L⟩ := linearInjection_nonempty_of_finrank_le h
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) (L.1 b) x
    (injection_eval_ne_zero L hb) hx
  exact ⟨postcompose e L, he⟩

/-- The product-shift map before the final quotient. -/
def productShift {F B K : Type*} [Field F] [AddCommGroup B] [Module F B]
    [AddCommGroup K] [Module F K] [Fintype (LinearInjection F B K)] :
    (LinearInjection F B K → B) →ₗ[F] K where
  toFun b := ∑ L : LinearInjection F B K, L.1 (b L)
  map_add' b c := by simp [map_add, Finset.sum_add_distrib]
  map_smul' t b := by simp [map_smul, Finset.smul_sum]

theorem productShift_surjective {F B K : Type*} [Field F]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    [AddCommGroup K] [Module F K] [FiniteDimensional F K]
    [Fintype (LinearInjection F B K)]
    (h : Module.finrank F B ≤ Module.finrank F K)
    (b : B) (hb : b ≠ 0) :
    Function.Surjective (productShift (F := F) (B := B) (K := K)) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, map_zero _⟩
  · obtain ⟨L, hL⟩ := exists_injection_hitting_nonzero h b hb x hx
    refine ⟨fun L' => if L' = L then b else 0, ?_⟩
    simpa [productShift, apply_ite] using hL

/-- Sum of the injectively relabeled base outputs before quotienting. -/
def enlargedOutput {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) : K := ∑ L : LinearInjection F B K, L.1 (C (x L))

/-- Equivariance of the nonlinear sum under the full product of base shifts. -/
theorem enlargedOutput_shift {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Module F V] [Fintype (LinearInjection F B K)]
    (C : V → B) (i : B →ₗ[F] V)
    (hC : ∀ x b, C (x + i b) = C x + b)
    (x : LinearInjection F B K → V) (b : LinearInjection F B K → B) :
    enlargedOutput C (fun L => x L + i (b L)) =
      enlargedOutput C x + productShift b := by
  simp [enlargedOutput, productShift, hC, map_add, Finset.sum_add_distrib]

/-- Updating only one copy changes the output by its relabeled base-output
difference. This identity retains all summands and does not assume they are
independent. -/
theorem enlargedOutput_update {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) =
      enlargedOutput C x + L.1 (C y - C (x L)) := by
  classical
  have hfun : (fun J => J.1 (C (Function.update x L y J))) =
      Function.update (fun J : LinearInjection F B K => J.1 (C (x J))) L (L.1 (C y)) := by
    funext J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  unfold enlargedOutput
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ L)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ L)]
  rw [map_sub]
  abel

/-- Injectivity of the selected relabeling makes the enlargement output
change exactly when that copy's base output changes. -/
theorem enlargedOutput_update_ne_iff {F B K V : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [Fintype (LinearInjection F B K)] (C : V → B)
    (x : LinearInjection F B K → V) (L : LinearInjection F B K) (y : V) :
    enlargedOutput C (Function.update x L y) ≠ enlargedOutput C x ↔ C y ≠ C (x L) := by
  rw [enlargedOutput_update, ne_eq, add_eq_left, map_eq_zero_iff _ L.2,
    sub_eq_zero, ne_eq]

theorem injection_eval_uniform {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [AddCommGroup K] [Module F K]
    [Fintype K] [Fintype (LinearInjection F B K)]
    [Nonempty (LinearInjection F B K)] (b : B) (hb : b ≠ 0)
    (p : {x : K // x ≠ 0} → Prop) :
    probability (fun L : LinearInjection F B K =>
      p ⟨L.1 b, injection_eval_ne_zero L hb⟩) = probability p := by
  classical
  let : Nonempty {x : K // x ≠ 0} :=
    ⟨⟨(Classical.choice inferInstance : LinearInjection F B K).1 b,
      injection_eval_ne_zero _ hb⟩⟩
  let f : LinearInjection F B K → {x : K // x ≠ 0} :=
    fun L => ⟨L.1 b, injection_eval_ne_zero L hb⟩
  apply probability_preimage_of_fibers f
  intro x y
  obtain ⟨e, he⟩ := exists_equiv_map_nonzero (F := F) x.1 y.1 x.2 y.2
  let ee : {L : LinearInjection F B K // f L = x} ≃
      {L : LinearInjection F B K // f L = y} :=
    (postcompose e).subtypeEquiv (fun L => by
      change f L = x ↔ f (postcompose e L) = y
      constructor
      · intro h
        apply Subtype.ext
        change e (L.1 b) = y.1
        rw [show L.1 b = x.1 from congrArg Subtype.val h, he]
      · intro h
        apply Subtype.ext
        apply e.injective
        exact (congrArg Subtype.val h).trans he.symm)
  exact Nat.card_congr ee

/-- Failure of the pullback family to span the full dual has a nonzero vector
witness in its common annihilator. -/
theorem pullback_ne_top_iff {F B K : Type*} [Field F] [AddCommGroup B]
    [Module F B] [FiniteDimensional F B] [AddCommGroup K] [Module F K]
    (L : B →ₗ[F] K) (S : Submodule F (Module.Dual F K)) :
    S.map L.dualMap ≠ ⊤ ↔ ∃ b : B, b ≠ 0 ∧ L b ∈ S.dualCoannihilator := by
  let W := S.map L.dualMap
  have hann : W.dualCoannihilator = S.dualCoannihilator.comap L := by
    ext b
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap,
      ]
    constructor
    · intro h z hz
      exact h (z.comp L) ⟨z, hz, rfl⟩
    · intro h z ⟨w, hw, hwz⟩
      subst z
      exact h w hw
  constructor
  · intro hW
    have hn : W.dualCoannihilator ≠ ⊥ := by
      intro hz
      have hh := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
      rw [hz, Submodule.dualAnnihilator_bot] at hh
      exact hW hh.symm
    obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).1 hn
    exact ⟨b, hb0, by simpa [hann] using hb⟩
  · rintro ⟨b, hb0, hb⟩ htop
    have hz : b ∈ W.dualCoannihilator := by simpa [hann] using hb
    change b ∈ (S.map L.dualMap).dualCoannihilator at hz
    rw [htop] at hz
    have hall : ∀ z : Module.Dual F B, z b = 0 := by
      simpa only [Submodule.mem_dualCoannihilator, Submodule.mem_top,
        forall_true_left] using hz
    obtain ⟨z, hz'⟩ := Module.Projective.exists_dual_ne_zero F hb0
    exact hz' (hall z)

/-- The nonzero part of a codimension-`r` subspace has density at most `2⁻ʳ`
among all nonzero ambient vectors. The dimensions are written additively to
avoid truncated subtraction. -/
theorem nonzero_density_le (d r : ℕ) (h : 0 < d + r) :
    ((2 : ℚ) ^ d - 1) / ((2 : ℚ) ^ (d + r) - 1) ≤ 1 / (2 : ℚ) ^ r := by
  have hpow : 1 < (2 : ℚ) ^ (d + r) := one_lt_pow₀ (by norm_num) (by omega)
  have hr : (1 : ℚ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  rw [pow_add]
  nlinarith

/-- Cardinality of all nonzero vectors in a finite binary vector space. -/
theorem card_nonzero_binary (K : Type*) [AddCommGroup K] [Module (ZMod 2) K]
    [Fintype K] :
    Nat.card {x : K // x ≠ 0} = 2 ^ Module.finrank (ZMod 2) K - 1 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Exact density of the nonzero part of a binary subspace. -/
theorem probability_nonzero_subspace (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] (W : Submodule (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ W) =
      ((2 : ℚ) ^ Module.finrank (ZMod 2) W - 1) /
        ((2 : ℚ) ^ Module.finrank (ZMod 2) K - 1) := by
  classical
  let : Fintype W := Fintype.ofFinite _
  let e : {x : {x : K // x ≠ 0} // x.1 ∈ W} ≃ {x : W // x ≠ 0} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, by
        intro h
        exact x.1.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨⟨x.1.1, by
        intro h
        apply x.2
        exact Subtype.ext h⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold probability
  rw [Nat.card_congr e,
    card_nonzero_binary W, card_nonzero_binary K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)),
    Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
  push_cast ; rfl

/-- The annihilator dimension identity gives precisely the exponent needed
by the enlargement, without any loss depending on the ambient dimension. -/
theorem probability_annihilator_le (K : Type*) [AddCommGroup K]
    [Module (ZMod 2) K] [Fintype K] [FiniteDimensional (ZMod 2) K]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator) ≤
      1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  rw [probability_nonzero_subspace]
  have hr := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  rw [← hr, add_comm (Module.finrank (ZMod 2) S)]
  apply nonzero_density_le
  omega

/-- The threshold `b + 2` is chosen before the ambient dimension. -/
theorem union_bound_le_quarter (b r : ℕ) (hr : b + 2 ≤ r) :
    ((2 : ℚ) ^ b - 1) / (2 : ℚ) ^ r ≤ 1 / 4 := by
  have hpow : (2 : ℚ) ^ (b + 2) ≤ (2 : ℚ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  rw [pow_add] at hpow
  norm_num at hpow
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ r)).2
  nlinarith [show (0 : ℚ) ≤ 2 ^ b by positivity]

/-- The enlargement's uniform-injection union bound, including its actual
linear-algebraic bad event. -/
theorem pullback_failure_probability_le {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hK : 0 < Module.finrank (ZMod 2) K) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      ((2 : ℚ) ^ Module.finrank (ZMod 2) B - 1) /
        (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
  classical
  calc
    _ = probability (fun L : LinearInjection (ZMod 2) B K =>
        ∃ b : {b : B // b ≠ 0}, L.1 b.1 ∈ S.dualCoannihilator) := by
      congr 1
      funext L
      apply propext
      rw [pullback_ne_top_iff]
      exact ⟨fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩,
        fun ⟨b, h⟩ => ⟨b.1, b.2, h⟩⟩
    _ ≤ ∑ b : {b : B // b ≠ 0}, probability
        (fun L : LinearInjection (ZMod 2) B K => L.1 b.1 ∈ S.dualCoannihilator) :=
      probability_exists_le_sum _
    _ ≤ ∑ _b : {b : B // b ≠ 0},
        1 / (2 : ℚ) ^ Module.finrank (ZMod 2) S := by
      apply Finset.sum_le_sum
      intro b _
      rw [injection_eval_uniform b.1 b.2
        (fun x : {x : K // x ≠ 0} => x.1 ∈ S.dualCoannihilator)]
      exact probability_annihilator_le K S hK
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, card_nonzero_binary B,
        Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
      push_cast
      ring

/-- At least three quarters of the injection copies restrict onto the full
base dual when the restriction rank is at least `dim B + 2`. -/
theorem pullback_failure_probability_le_quarter {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S) :
    probability (fun L : LinearInjection (ZMod 2) B K => S.map L.1.dualMap ≠ ⊤) ≤
      1 / 4 := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq S
  exact (pullback_failure_probability_le S (by omega)).trans
    (union_bound_le_quarter _ _ hr)

theorem probability_not {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) : probability (fun x => ¬ p x) = 1 - probability p := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω)) p
  have h' : ((Finset.univ.filter p).card : ℚ) +
      ((Finset.univ.filter fun x => ¬p x).card : ℚ) = Fintype.card Ω := by
    exact_mod_cast h
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply (eq_sub_iff_add_eq).2
  rw [← add_div, add_comm, h', div_self hcard]

/-- Averaging a nonnegative detection rate which is at least one quarter on
each good copy. This is the last finite probability step of enlargement. -/
theorem average_detection_lower_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (bad : Ω → Prop) (detected : Ω → ℚ)
    (hnonneg : ∀ x, 0 ≤ detected x)
    (hgood : ∀ x, ¬bad x → 1 / 4 ≤ detected x) :
    (1 - probability bad) * (1 / 4) ≤
      (∑ x, detected x) / (Fintype.card Ω : ℚ) := by
  classical
  have hs : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) ≤ ∑ x, detected x := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : bad x
    · simpa [hx] using hnonneg x
    · simpa [hx] using hgood x hx
  have heq : ∑ x : Ω, (if bad x then (0 : ℚ) else 1 / 4) =
      ((Finset.univ.filter fun x => ¬bad x).card : ℚ) * (1 / 4) := by
    rw [Finset.sum_ite]
    simp
  rw [heq] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Fintype.card Ω) :
    (0 : ℚ) ≤ Fintype.card Ω)
  rw [← probability_not]
  unfold probability
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [div_mul_eq_mul_div] using hd

/-- The enlargement retains `3/16` detection, and hence the advertised `1/8`.
The hypotheses are the bad-copy probability and the average lower bound from
the base gadget; they make no independence assertion. -/
theorem detection_constants {bad detected : ℚ} (hbad : bad ≤ 1 / 4)
    (hdetected : (1 - bad) * (1 / 4) ≤ detected) :
    3 / 16 ≤ detected ∧ 1 / 8 ≤ detected := by
  constructor <;> linarith

theorem enlarged_detection {B K : Type*}
    [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
    [FiniteDimensional (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
    [FiniteDimensional (ZMod 2) K]
    [Fintype (LinearInjection (ZMod 2) B K)]
    [Nonempty (LinearInjection (ZMod 2) B K)]
    (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) K))
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2) S)
    (detected : LinearInjection (ZMod 2) B K → ℚ)
    (hnonneg : ∀ L, 0 ≤ detected L)
    (hbase : ∀ L, S.map L.1.dualMap = ⊤ → 1 / 4 ≤ detected L) :
    3 / 16 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) ∧
    1 / 8 ≤ (∑ L, detected L) / (Fintype.card (LinearInjection (ZMod 2) B K) : ℚ) := by
  apply detection_constants (pullback_failure_probability_le_quarter S hr)
  apply average_detection_lower_bound _ detected hnonneg
  intro L hL
  exact hbase L (not_not.mp hL)

end

end MaxCutGames.Gadget.Enlargement

noncomputable section

namespace MaxCutGames.Gadget.EnlargementConstruction

open scoped BigOperators Classical
open Enlargement

theorem probability_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p : Ξ → Prop) :
    probability (fun x : Ω => p (e x)) = probability p := by
  classical
  unfold probability
  rw [Nat.card_congr (Equiv.subtypeEquivOfSubtype (p := p) e), Nat.card_congr e]

theorem probability_eq_sum_indicator {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) :
    probability p =
      (∑ x : Ω, if p x then (1 : ℚ) else 0) / (Fintype.card Ω : ℚ) := by
  classical
  simp only [probability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- Uniform probability on a product is the average of the second-coordinate
probabilities. No nonemptiness hypotheses are needed for this identity. -/
theorem probability_prod_average {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ x : Ω, probability (p x)) / (Fintype.card Ω : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

/-- The same product identity, averaging in the other order. -/
theorem probability_prod_average_right {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Ξ → Prop) :
    probability (fun z : Ω × Ξ => p z.1 z.2) =
      (∑ y : Ξ, probability (fun x : Ω => p x y)) /
        (Fintype.card Ξ : ℚ) := by
  classical
  simp_rw [probability_eq_sum_indicator]
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type_right,
    ← Finset.sum_div, div_div]

/-- Every coordinate of a uniformly chosen function has the uniform marginal.
Pointwise transpositions biject the evaluation fibers. -/
theorem probability_coordinate {I X : Type*} [Fintype I] [Fintype X]
    (i : I) (p : X → Prop) :
    probability (fun g : I → X => p (g i)) = probability p := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      let : IsEmpty (I → X) := ⟨fun g => isEmptyElim (g i)⟩
      simp [probability]
  | inr hX =>
      let : Nonempty X := hX
      let : Nonempty (I → X) := ⟨fun _ => Classical.choice hX⟩
      apply probability_preimage_of_fibers (fun g : I → X => g i)
      intro x y
      let e : (I → X) ≃ (I → X) :=
        Equiv.piCongrRight (fun _ : I => Equiv.swap x y)
      let ee : {g : I → X // g i = x} ≃
          {g : I → X // g i = y} :=
        e.subtypeEquiv (fun g => by
          change g i = x ↔ Equiv.swap x y (g i) = y
          constructor
          · intro h
            rw [h, Equiv.swap_apply_left]
          · intro h
            apply (Equiv.swap x y).injective
            exact h.trans (Equiv.swap_apply_left x y).symm)
      exact Nat.card_congr ee

/-- Coordinate projection preserves the joint uniform law with an independent
finite noise sample. -/
theorem probability_coordinate_prod {I X N : Type*}
    [Fintype I] [Fintype X] [Fintype N] (i : I) (p : X → N → Prop) :
    probability (fun z : (I → X) × N => p (z.1 i) z.2) =
      probability (fun z : X × N => p z.1 z.2) := by
  rw [probability_prod_average_right (fun (g : I → X) n => p (g i) n),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact probability_coordinate i (fun x => p x n)

/-- Grouping the same three uniform choices in another order. -/
theorem probability_prod_reorder {Ω I N : Type*}
    [Fintype Ω] [Fintype I] [Fintype N] (p : Ω → I → N → Prop) :
    probability (fun z : Ω × (I × N) => p z.1 z.2.1 z.2.2) =
      probability (fun z : I × (Ω × N) => p z.2.1 z.1 z.2.2) := by
  let e : (Ω × (I × N)) ≃ (I × (Ω × N)) :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun z => (z.2.1, z.1, z.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact probability_equiv e (fun z => p z.2.1 z.1 z.2.2)

/-- If each conditional probability is the same, their uniform average is
that common value. -/
theorem probability_prod_eq_of_const {Ω Ξ : Type*}
    [Fintype Ω] [Fintype Ξ] [Nonempty Ω]
    (p : Ω → Ξ → Prop) (q : ℚ) (h : ∀ x, probability (p x) = q) :
    probability (fun z : Ω × Ξ => p z.1 z.2) = q := by
  rw [probability_prod_average]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ q hcard

/-- For a fixed selected injection, the enlargement's change event has exactly
the base input/noise probability. -/
theorem enlarged_single_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)]
    (C : V → B) (a : N → V) (L : LinearInjection F B K) :
    probability (fun z : (LinearInjection F B K → V) × N =>
      enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠
        enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  calc
    _ = probability (fun z : (LinearInjection F B K → V) × N =>
        C (z.1 L + a z.2) ≠ C (z.1 L)) := by
      congr 1
      funext z
      exact propext (enlargedOutput_update_ne_iff C z.1 L (z.1 L + a z.2))
    _ = _ := probability_coordinate_prod L (fun x n => C (x + a n) ≠ C x)

/-- The same equality after selecting the injection uniformly as part of the
noise sample. Its sample space is exactly product-input × (copy × base-noise). -/
theorem enlarged_random_copy_probability {F B K V N : Type*} [Field F]
    [AddCommGroup B] [Module F B] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Fintype V] [Fintype N]
    [Fintype (LinearInjection F B K)] [Nonempty (LinearInjection F B K)]
    (C : V → B) (a : N → V) :
    probability (fun z : (LinearInjection F B K → V) ×
        (LinearInjection F B K × N) =>
      enlargedOutput C
        (Function.update z.1 z.2.1 (z.1 z.2.1 + a z.2.2)) ≠
          enlargedOutput C z.1) =
      probability (fun z : V × N => C (z.1 + a z.2) ≠ C z.1) := by
  rw [probability_prod_reorder (fun x L n =>
    enlargedOutput C (Function.update x L (x L + a n)) ≠ enlargedOutput C x)]
  apply probability_prod_eq_of_const (fun L (z : (LinearInjection F B K → V) × N) =>
    enlargedOutput C (Function.update z.1 L (z.1 L + a z.2)) ≠ enlargedOutput C z.1)
  intro L
  exact enlarged_single_copy_probability C a L

universe u

variable {B K V N : Type u}
variable [AddCommGroup B] [Module (ZMod 2) B] [Fintype B]
variable [FiniteDimensional (ZMod 2) B]
variable [AddCommGroup K] [Module (ZMod 2) K] [Fintype K]
variable [FiniteDimensional (ZMod 2) K]
variable [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
variable [Fintype N] [Nonempty N]

abbrev Copies (B K : Type u) [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup K] [Module (ZMod 2) K] := LinearInjection (ZMod 2) B K

/-- A concrete finite enumeration exists because an injection is determined
by its finite function table. -/
@[instance_reducible]
noncomputable def copiesFintype : Fintype (Copies B K) :=
  Fintype.ofInjective (fun L : Copies B K => (L.1 : B → K)) (by
    intro L M h
    apply Subtype.ext
    exact LinearMap.ext (congrFun h))

local instance : Fintype (Copies B K) := copiesFintype

def productEmbed (i : B →ₗ[ZMod 2] V) :
    (Copies B K → B) →ₗ[ZMod 2] (Copies B K → V) where
  toFun b L := i (b L)
  map_add' b c := by ext L; exact map_add i (b L) (c L)
  map_smul' t b := by ext L; exact map_smul i t (b L)

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Fintype V] in
theorem productEmbed_injective (i : B →ₗ[ZMod 2] V)
    (hi : Function.Injective i) : Function.Injective (productEmbed (K := K) i) := by
  intro b c h
  funext L
  apply hi
  exact congrFun h L

/-- The product before the quotient. Its finite noise sampler first chooses
an injection uniformly, then independently chooses the original base noise. -/
def productStage (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K := by
  letI : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  exact
    { Input := Copies B K → V
      Shift := Copies B K → B
      Noise := Copies B K × N
      embed := productEmbed i
      embed_injective := productEmbed_injective i hi
      logical := productShift
      logical_surjective := productShift_surjective hdim b₀ hb₀
      output := enlargedOutput C
      equivariant := enlargedOutput_shift C i hC
      noise := fun t => Pi.single t.1 (noise t.2) }

/-- The final finite gadget, with `K` embedded as its actual shift space. -/
def build (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) : Stage (ZMod 2) K :=
  StageQuotient.toStage (productStage i hi C hC noise hdim b₀ hb₀)

private theorem update_canonical {A B : Type*} (d : DecidableEq A) (f : A → B) (a : A) (b : B) :
    @Function.update A (fun _ => B) d f a b =
      @Function.update A (fun _ => B) (Classical.typeDecidableEq A) f a b := by
  cases Subsingleton.elim d (Classical.typeDecidableEq A : DecidableEq A)
  rfl

private theorem probability_pointwise {A : Type*} (i j : Fintype A) (p q : A → Prop)
    (h : ∀ a, p a ↔ q a) : @probability A i p = @probability A j q := by
  unfold probability
  have he : p = q := funext (fun a => propext (h a))
  rw [he]

omit [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
theorem add_single_eq_update (x : Copies B K → V) (L : Copies B K) (a : V) :
    x + Pi.single L a = Function.update x L (x L + a) := by
  funext J
  by_cases h : J = L
  · subst J
    simp
  · simp [h]

/-- The quotient and injection preserve each individual nonlinear change
event exactly, before taking any finite averages. -/
theorem change_iff (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0) (x : Copies B K → V) (L : Copies B K) (n : N) :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    StageQuotient.output s (StageQuotient.projection s x + StageQuotient.noise s (L, n)) ≠
        StageQuotient.output s (StageQuotient.projection s x) ↔
      C (x L + noise n) ≠ C (x L) := by
  dsimp only
  refine (StageQuotient.noise_change_iff
    (productStage i hi C hC noise hdim b₀ hb₀) x (L, n)).trans ?_
  change enlargedOutput C (x + Pi.single L (noise n)) ≠ enlargedOutput C x ↔ _
  rw [add_single_eq_update]
  have h := enlargedOutput_update_ne_iff C x L (x L + noise n)
  simp only [update_canonical] at h ⊢
  exact h

/-- Restriction of a linear observer on the quotient to one base-input copy. -/
def copyObserver {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) : V →ₗ[ZMod 2] E :=
  T.comp ((StageQuotient.projection (productStage i hi C hC noise hdim b₀ hb₀)).comp
    (LinearMap.single (R := ZMod 2) (φ := fun _ : Copies B K => V) L))

theorem copyObserver_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (L : Copies B K) :
    (copyObserver i hi C hC noise hdim b₀ hb₀ T L).comp i =
      (T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))).comp L.1 := by
  ext b
  let s := productStage i hi C hC noise hdim b₀ hb₀
  have he : s.embed (Pi.single L b) = Pi.single L (i b) := by
    funext J
    change i ((Pi.single L b : Copies B K → B) J) =
      (Pi.single L (i b) : Copies B K → V) J
    by_cases h : J = L
    · subst J
      simp
    · simp [h]
  have hl : s.logical (Pi.single L b) = L.1 b := by
    change (∑ J : Copies B K, J.1 ((Pi.single L b : Copies B K → B) J)) = L.1 b
    simp [Pi.single_apply, apply_ite]
  have hh := congrArg T (StageQuotient.shift_logical s (Pi.single L b))
  rw [he, hl] at hh
  exact hh.symm

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem dual_pullback_eq_top_iff {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (A : K →ₗ[ZMod 2] E) (L : B →ₗ[ZMod 2] K) :
    (LinearMap.range A.dualMap).map L.dualMap = ⊤ ↔ Function.Injective (A.comp L) := by
  rw [← LinearMap.range_comp, LinearMap.dualMap_comp_dualMap,
    LinearMap.range_eq_top, LinearMap.dualMap_surjective_iff]

/-- Average detection over the actual injection-indexed base copies. The
restriction threshold is the rank on the final embedded logical space. -/
theorem detection_average {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤
      (∑ L : Copies B K, probability (fun n : N =>
        copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)) /
          (Fintype.card (Copies B K) : ℚ) := by
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let A := T.comp (StageQuotient.shift (productStage i hi C hC noise hdim b₀ hb₀))
  apply (enlarged_detection (LinearMap.range A.dualMap)
    (by simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hr)
    (fun L => probability (fun n : N =>
      copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0))
    (fun _ => by unfold probability; positivity) ?_).2
  intro L hL
  apply hbase
  rw [copyObserver_shift]
  exact (dual_pullback_eq_top_iff A L.1).1 hL

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
/-- Passing uniform input through the actual quotient preserves its law. -/
theorem probability_projection (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    (p : StageQuotient.Space s → Prop) :
    probability (fun x : s.Input => p (StageQuotient.projection s x)) = probability p := by
  apply probability_preimage_of_fibers (StageQuotient.projection s)
  intro x y
  have h := (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) x).trans
    (Quotient.fiber_card (StageQuotient.shifts s) (StageQuotient.logical s) y).symm
  exact h

omit [Fintype K] [FiniteDimensional (ZMod 2) K] in
theorem probability_projection_prod (s : Stage (ZMod 2) K)
    [Fintype s.Input] [Fintype (StageQuotient.Space s)]
    {A : Type*} [Fintype A] (p : StageQuotient.Space s → A → Prop) :
    probability (fun z : s.Input × A => p (StageQuotient.projection s z.1) z.2) =
      probability (fun z : StageQuotient.Space s × A => p z.1 z.2) := by
  rw [probability_prod_average_right (fun x a => p (StageQuotient.projection s x) a),
    probability_prod_average_right p]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact probability_projection s (fun x => p x a)

/-- Nonlinear change probability is exactly the base probability after both
the single-copy enlargement and quotient, on uniform quotient input. -/
theorem change_probability (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    [Fintype (StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀))] :
    let s := productStage i hi C hC noise hdim b₀ hb₀
    probability (fun z : StageQuotient.Space s × (Copies B K × N) =>
      StageQuotient.output s (z.1 + StageQuotient.noise s z.2) ≠ StageQuotient.output s z.1) =
        probability (fun z : V × N => C (z.1 + noise z.2) ≠ C z.1) := by
  dsimp only
  let : Nonempty (Copies B K) := linearInjection_nonempty_of_finrank_le hdim
  let s := productStage i hi C hC noise hdim b₀ hb₀
  let : Fintype s.Input := Fintype.ofFinite _
  have hp := probability_projection_prod s (fun q (t : Copies B K × N) =>
    StageQuotient.output s (q + StageQuotient.noise s t) ≠ StageQuotient.output s q)
  calc
    _ = probability (fun z : s.Input × (Copies B K × N) =>
        StageQuotient.output s (StageQuotient.projection s z.1 + StageQuotient.noise s z.2) ≠
          StageQuotient.output s (StageQuotient.projection s z.1)) := hp.symm
    _ = probability (fun z : (Copies B K → V) × (Copies B K × N) =>
        enlargedOutput C
          (Function.update z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)) ≠ enlargedOutput C z.1) := by
      apply probability_pointwise
      intro z
      have h₁ := change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2
      have h₂ := enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)
      simp only [update_canonical] at h₁ h₂ ⊢
      have hc := h₁.trans h₂.symm
      -- `s.Input` is a defined function space; rewrite at default transparency.
      erw [update_canonical] at hc
      exact hc
    _ = _ := by
      have hh := enlarged_random_copy_probability (F := ZMod 2) (K := K) C noise
      simp only [update_canonical] at hh ⊢
      unfold probability at hh ⊢
      exact hh

/-- The final noise sample is the actual product sampler and meets the stated
rank-detection bound. No detection premise about the enlarged gadget is assumed. -/
theorem detection_probability {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (i : B →ₗ[ZMod 2] V) (hi : Function.Injective i)
    (C : V → B) (hC : ∀ x b, C (x + i b) = C x + b) (noise : N → V)
    (hdim : Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) K)
    (b₀ : B) (hb₀ : b₀ ≠ 0)
    (hbase : ∀ U : V →ₗ[ZMod 2] E, Function.Injective (U.comp i) →
      1 / 4 ≤ probability (fun n : N => U (noise n) ≠ 0))
    (T : StageQuotient.Space (productStage i hi C hC noise hdim b₀ hb₀) →ₗ[ZMod 2] E)
    (hr : Module.finrank (ZMod 2) B + 2 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (T.comp (StageQuotient.shift
        (productStage i hi C hC noise hdim b₀ hb₀))))) :
    1 / 8 ≤ probability (fun t : Copies B K × N =>
      T (StageQuotient.noise (productStage i hi C hC noise hdim b₀ hb₀) t) ≠ 0) := by
  change 1 / 8 ≤ probability (fun t : Copies B K × N =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T t.1 (noise t.2) ≠ 0)
  rw [probability_prod_average (fun L n =>
    copyObserver i hi C hC noise hdim b₀ hb₀ T L (noise n) ≠ 0)]
  exact detection_average i hi C hC noise hdim b₀ hb₀ hbase T hr

end MaxCutGames.Gadget.EnlargementConstruction
end

end OAI
