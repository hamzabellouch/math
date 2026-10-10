import Mathlib
import OAI.Computability.DirectedFeedback.Games.Genericity

namespace OAI

namespace DFVSGames.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

def harmonic : ℕ → ℚ
  | 0 => 0
  | r + 1 => harmonic r + (↑(r + 1))⁻¹

@[simp] theorem harmonic_zero : harmonic 0 = 0 := rfl

@[simp] theorem harmonic_succ (r : ℕ) :
    harmonic (r + 1) = harmonic r + (↑(r + 1))⁻¹ := rfl

theorem harmonic_eq_sum (r : ℕ) :
    harmonic r = ∑ i ∈ Finset.range r, (↑(i + 1) : ℚ)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih => simp [harmonic_succ, Finset.sum_range_succ, ih]

def average (f : Ω → ℚ) : ℚ := Finset.univ.expect f

def probability (p : Ω → Prop) [DecidablePred p] : ℚ :=
  average (fun ω => if p ω then 1 else 0)

theorem average_mono {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g :=
  Finset.expect_le_expect fun ω _ => h ω

theorem average_nonneg {f : Ω → ℚ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f :=
  Finset.expect_nonneg fun ω _ => h ω

@[simp] theorem average_const [Nonempty Ω] (c : ℚ) :
    average (fun _ : Ω => c) = c :=
  Finset.expect_const Finset.univ_nonempty c

theorem average_add (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g :=
  Finset.expect_add_distrib _ _ _

theorem average_sub (f g : Ω → ℚ) :
    average (fun ω => f ω - g ω) = average f - average g :=
  Finset.expect_sub_distrib _ _ _

theorem average_mul_left (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f :=
  (Finset.mul_expect _ _ _).symm

theorem probability_nonneg (p : Ω → Prop) [DecidablePred p] :
    0 ≤ probability p := by
  apply average_nonneg
  intro ω
  split <;> norm_num

theorem probability_le_one [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability p ≤ 1 := by
  calc
    probability p ≤ average (fun _ : Ω => 1) := by
      apply average_mono
      intro ω
      split <;> norm_num
    _ = 1 := average_const _

theorem probability_mono (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ ω, p ω → q ω) : probability p ≤ probability q := by
  apply average_mono
  intro ω
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · simp only [ite_eq_right hp]
    split <;> norm_num

theorem probability_not [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability (fun ω => ¬ p ω) = 1 - probability p := by
  have he : (fun ω => if ¬ p ω then (1 : ℚ) else 0) =
      (fun ω => 1 - if p ω then (1 : ℚ) else 0) := by
    funext ω
    by_cases h : p ω <;> simp [h]
  unfold probability
  rw [he, average_sub, average_const]

theorem probability_eq_half_of_swap [Nonempty Ω]
    (p : Ω → Prop) [DecidablePred p] (e : Ω ≃ Ω)
    (hswap : ∀ ω, p (e ω) ↔ ¬ p ω) : probability p = 1 / 2 := by
  have he : probability (fun ω => ¬ p ω) = probability p := by
    apply Fintype.expect_equiv e
    intro ω
    simp only [hswap ω]
  rw [probability_not] at he
  linarith

theorem binary_character_detection_probability [AddGroup Ω]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0) :
    probability (fun ω => χ ω ≠ 0) = 1 / 2 := by
  apply probability_eq_half_of_swap _ (Equiv.addLeft v)
  intro ω
  change χ (v + ω) ≠ 0 ↔ ¬χ ω ≠ 0
  rw [map_add]
  generalize ha : χ v = a at hv ⊢
  generalize hb : χ ω = b
  fin_cases a <;> fin_cases b
  · exact (hv rfl).elim
  · exact (hv rfl).elim
  · change (1 : ZMod 2) + 0 ≠ 0 ↔ ¬ (0 : ZMod 2) ≠ 0
    decide
  · change (1 : ZMod 2) + 1 ≠ 0 ↔ ¬ (1 : ZMod 2) ≠ 0
    decide

theorem binary_family_detection_ge_half [AddGroup Ω]
    (detects : Ω → Prop) [DecidablePred detects]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0)
    (hcontains : ∀ ω, χ ω ≠ 0 → detects ω) :
    (1 / 2 : ℚ) ≤ probability detects := by
  rw [← binary_character_detection_probability χ v hv]
  exact probability_mono _ _ hcontains

theorem harmonic_nonneg (r : ℕ) : 0 ≤ harmonic r := by
  induction r with
  | zero => simp
  | succ r ih => rw [harmonic_succ]; positivity

theorem harmonic_mono {r s : ℕ} (h : r ≤ s) : harmonic r ≤ harmonic s := by
  induction h with
  | refl => exact le_rfl
  | @step s h ih =>
    rw [harmonic_succ]
    have : (0 : ℚ) ≤ (↑(s + 1))⁻¹ := by positivity
    linarith

theorem harmonic_pos {r : ℕ} (h : 0 < r) : 0 < harmonic r := by
  have hm := harmonic_mono (r := 1) (s := r) h
  norm_num [harmonic_succ] at hm
  linarith

theorem harmonic_sub_predecessor {r : ℕ} (h : 0 < r) :
    harmonic r - harmonic (r - 1) = (r : ℚ)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [harmonic_succ]

theorem generic_drop_identity (r : ℕ) (next : Ω → ℕ) (hr : 0 < r)
    (hstep : ∀ ω, next ω = r ∨ next ω = r - 1) :
    average (fun ω => harmonic r - harmonic (next ω)) =
      (r : ℚ)⁻¹ * probability (fun ω => next ω < r) := by
  have he : (fun ω => harmonic r - harmonic (next ω)) =
      (fun ω => (r : ℚ)⁻¹ * if next ω < r then 1 else 0) := by
    funext ω
    rcases hstep ω with h | h
    · simp [h]
    · rw [h, ite_eq_left (Nat.sub_lt hr (by omega))]
      simp [harmonic_sub_predecessor hr]
  rw [he, average_mul_left]
  rfl

theorem generic_expected_drop_le (r : ℕ) (next : Ω → ℕ) (θ : ℚ)
    (hr : 0 < r) (hstep : ∀ ω, next ω = r ∨ next ω = r - 1)
    (hloss : probability (fun ω => next ω < r) ≤ 3 * r * θ) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ 3 * θ := by
  rw [generic_drop_identity r next hr hstep]
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  calc
    (r : ℚ)⁻¹ * probability (fun ω => next ω < r) ≤
        (r : ℚ)⁻¹ * (3 * r * θ) :=
      mul_le_mul_of_nonneg_left hloss (le_of_lt (inv_pos.mpr hrq))
    _ = 3 * θ := by field_simp [ne_of_gt hrq]

theorem arbitrary_expected_drop_le (r : ℕ) (next : Ω → ℕ) (p : ℚ)
    (hstep : ∀ ω, next ω ≤ r)
    (hloss : probability (fun ω => next ω < r) ≤ p) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ harmonic r * p := by
  calc
    average (fun ω => harmonic r - harmonic (next ω)) ≤
        average (fun ω => harmonic r * if next ω < r then 1 else 0) := by
      apply average_mono
      intro ω
      by_cases h : next ω < r
      · simp only [ite_eq_left h, mul_one]
        exact sub_le_self _ (harmonic_nonneg _)
      · have he : next ω = r := by have := hstep ω; omega
        simp [he]
    _ = harmonic r * probability (fun ω => next ω < r) := by
      rw [average_mul_left]
      rfl
    _ ≤ harmonic r * p := mul_le_mul_of_nonneg_left hloss (harmonic_nonneg _)

theorem expected_drop_le_four_theta [Nonempty Ω]
    (drop : Ω → ℚ) (bad : Ω → Prop) [DecidablePred bad] (C θ ε : ℚ)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hconditional : ∀ ω, drop ω ≤ 3 * θ + C * θ * if bad ω then 1 else 0)
    (hbad : probability bad ≤ ε) (hsmall : C * ε ≤ 1) :
    average drop ≤ 4 * θ := by
  have haverage : average drop ≤ 3 * θ + C * θ * probability bad := by
    calc
      average drop ≤ average (fun ω => 3 * θ + C * θ * if bad ω then 1 else 0) :=
        average_mono hconditional
      _ = 3 * θ + C * θ * probability bad := by
        rw [average_add, average_const, average_mul_left]
        rfl
  have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
  nlinarith

def badRankCoefficient (r₀ : ℕ) : ℚ := harmonic r₀ * 2 ^ r₀

theorem badRankCoefficient_nonneg (r₀ : ℕ) : 0 ≤ badRankCoefficient r₀ := by
  exact mul_nonneg (harmonic_nonneg _) (by positivity)

def depth (r₀ : ℕ) (θ : ℚ) : ℕ := ⌊harmonic r₀ / (8 * θ)⌋₊

theorem depth_budget (r₀ : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    4 * (depth r₀ θ : ℚ) * θ ≤ harmonic r₀ / 2 := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.floor_le (div_nonneg (harmonic_nonneg r₀) (le_of_lt hden))
  have hb := (le_div_iff₀ hden).mp hf
  change (depth r₀ θ : ℚ) * (8 * θ) ≤ harmonic r₀ at hb
  nlinarith

theorem expected_total_drop_le [Nonempty Ω] (rank : ℕ → Ω → ℕ)
    (r₀ s : ℕ) (θ : ℚ) (hinitial : ∀ ω, rank 0 ω = r₀)
    (hstep : ∀ j < s,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) ≤ 4 * θ) :
    harmonic r₀ - average (fun ω => harmonic (rank s ω)) ≤ 4 * s * θ := by
  have haux : ∀ n, n ≤ s →
      harmonic r₀ - average (fun ω => harmonic (rank n ω)) ≤ 4 * n * θ := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [hinitial, average_const, Nat.cast_zero, mul_zero, zero_mul, sub_self, le_refl]
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hnext := hstep n (by omega)
      rw [average_sub] at hnext
      push_cast
      linarith
  exact haux s le_rfl

theorem survival_probability_ge_half_of_potential (rank : Ω → ℕ) (r₀ : ℕ)
    (hr₀ : 0 < r₀) (hterminal : ∀ ω, rank ω ≤ r₀)
    (hmean : harmonic r₀ / 2 ≤ average (fun ω => harmonic (rank ω))) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank ω) := by
  have hpoint : average (fun ω => harmonic (rank ω)) ≤
      harmonic r₀ * probability (fun ω => 0 < rank ω) := by
    calc
      average (fun ω => harmonic (rank ω)) ≤
          average (fun ω => harmonic r₀ * if 0 < rank ω then 1 else 0) := by
        apply average_mono
        intro ω
        by_cases h : 0 < rank ω
        · simpa only [ite_eq_left h, mul_one] using harmonic_mono (hterminal ω)
        · have he : rank ω = 0 := by omega
          simp [he]
      _ = harmonic r₀ * probability (fun ω => 0 < rank ω) := by
        rw [average_mul_left]
        rfl
  have hpos := harmonic_pos hr₀
  nlinarith

theorem survival_probability_ge_half [Nonempty Ω] (rank : ℕ → Ω → ℕ)
    (r₀ s : ℕ) (θ : ℚ) (hr₀ : 0 < r₀)
    (hinitial : ∀ ω, rank 0 ω = r₀)
    (hterminal : ∀ ω, rank s ω ≤ r₀)
    (hstep : ∀ j < s,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) ≤ 4 * θ)
    (hdepth : 4 * s * θ ≤ harmonic r₀ / 2) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank s ω) := by
  have htotal := expected_total_drop_le rank r₀ s θ hinitial hstep
  apply survival_probability_ge_half_of_potential (rank s) r₀ hr₀ hterminal
  linarith

theorem survival_of_adaptive_step_law [Nonempty Ω]
    (rank : ℕ → Ω → ℕ) (bad : ℕ → Ω → Prop)
    [∀ j, DecidablePred (bad j)] (conditionalDrop : ℕ → Ω → ℚ)
    (r₀ : ℕ) (θ ε : ℚ) (hr₀ : 0 < r₀) (hθ : 0 < θ)
    (hinitial : ∀ ω, rank 0 ω = r₀)
    (hterminal : ∀ ω, rank (depth r₀ θ) ω ≤ r₀)
    (hmean : ∀ j < depth r₀ θ,
      average (fun ω => harmonic (rank j ω) - harmonic (rank (j + 1) ω)) =
        average (conditionalDrop j))
    (hconditional : ∀ j < depth r₀ θ, ∀ ω,
      conditionalDrop j ω ≤ 3 * θ + badRankCoefficient r₀ * θ *
        if bad j ω then 1 else 0)
    (hbad : ∀ j < depth r₀ θ, probability (bad j) ≤ ε)
    (hsmall : badRankCoefficient r₀ * ε ≤ 1) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank (depth r₀ θ) ω) := by
  apply survival_probability_ge_half rank r₀ (depth r₀ θ) θ hr₀ hinitial hterminal
  · intro j hj
    rw [hmean j hj]
    exact expected_drop_le_four_theta (conditionalDrop j) (bad j)
      (badRankCoefficient r₀) θ ε (badRankCoefficient_nonneg r₀)
      (le_of_lt hθ) (hconditional j hj) (hbad j hj) hsmall
  · exact depth_budget r₀ θ hθ

theorem detection_probability_ge_quarter [Nonempty Ω]
    (survives : Ω → Prop) [DecidablePred survives] (conditionalDetection : Ω → ℚ)
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hnonneg : ∀ ω, 0 ≤ conditionalDetection ω)
    (hdetect : ∀ ω, survives ω → (1 / 2 : ℚ) ≤ conditionalDetection ω) :
    (1 / 4 : ℚ) ≤ average conditionalDetection := by
  have h : (1 / 2 : ℚ) * probability survives ≤ average conditionalDetection := by
    calc
      (1 / 2 : ℚ) * probability survives =
          average (fun ω => (1 / 2 : ℚ) * if survives ω then 1 else 0) :=
        (average_mul_left _ _).symm
      _ ≤ average conditionalDetection := by
        apply average_mono
        intro ω
        by_cases hs : survives ω
        · simpa only [ite_eq_left hs, mul_one] using hdetect ω hs
        · simpa only [ite_eq_right hs, mul_zero] using hnonneg ω
  linarith

theorem probability_product {Ξ : Type*} [Fintype Ξ]
    (detects : Ω × Ξ → Prop) [DecidablePred detects] :
    probability detects = average (fun ω => probability (fun ξ => detects (ω, ξ))) := by
  unfold probability average
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ)
      (fun z => if detects z then (1 : ℚ) else 0))

theorem product_detection_probability_ge_quarter [Nonempty Ω]
    {Ξ : Type*} [Fintype Ξ]
    (survives : Ω → Prop) [DecidablePred survives]
    (detects : Ω × Ξ → Prop) [DecidablePred detects]
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hdetect : ∀ ω, survives ω →
      (1 / 2 : ℚ) ≤ probability (fun ξ => detects (ω, ξ))) :
    (1 / 4 : ℚ) ≤ probability detects := by
  rw [probability_product]
  exact detection_probability_ge_quarter survives _ hsurvival
    (fun ω => probability_nonneg _) hdetect

theorem binary_product_detection_probability_ge_quarter [Nonempty Ω]
    {Ξ : Type*} [Fintype Ξ] [AddGroup Ξ]
    (survives : Ω → Prop) [DecidablePred survives]
    (detects : Ω × Ξ → Prop) [DecidablePred detects]
    (hsurvival : (1 / 2 : ℚ) ≤ probability survives)
    (hcharacter : ∀ ω, survives ω → ∃ χ : Ξ →+ ZMod 2, ∃ v : Ξ,
      χ v ≠ 0 ∧ ∀ ξ, χ ξ ≠ 0 → detects (ω, ξ)) :
    (1 / 4 : ℚ) ≤ probability detects := by
  apply product_detection_probability_ge_quarter survives detects hsurvival
  intro ω hω
  obtain ⟨χ, v, hv, hcontains⟩ := hcharacter ω hω
  exact binary_family_detection_ge_half (fun ξ => detects (ω, ξ)) χ v hv hcontains

end DFVSGames.Gadget.Harmonic

namespace DFVSGames.Quadratic

open scoped BigOperators
open DFVSGames.Gadget.Harmonic

noncomputable section

private theorem exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    (f : V →ₗ[ZMod 2] W)
    (h : Module.finrank (ZMod 2) f.range < Module.finrank (ZMod 2) V) :
    ∃ z, z ≠ 0 ∧ f z = 0 := by
  by_contra hn
  have hk : f.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hz0
    exact hn ⟨z, hz0, hz⟩
  have hdim := f.finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hdim
  omega

private theorem probability_rank_drop_le_loss_count_inline_HarmonicLoss
    {I V W : Type*} [Fintype I] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : I → V →ₗ[ZMod 2] W) :
    probability (fun i => Module.finrank (ZMod 2) (f i).range <
        Module.finrank (ZMod 2) V) ≤
      ((lossIndices f).card : ℚ) / Fintype.card I := by
  classical
  have hsub : Finset.univ.filter (fun i =>
      Module.finrank (ZMod 2) (f i).range < Module.finrank (ZMod 2) V) ⊆
      lossIndices f := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss (f i) (Finset.mem_filter.mp hi).2⟩
  simp only [probability, average, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance harmonicFieldLineFintype : Fintype (FieldLine F) := Fintype.ofFinite _
local instance harmonicSubmoduleFintype (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

def fieldLineTheta (F : Type*) [Field F] [Finite F] : ℚ :=
  (Nat.card (FieldLine F) : ℚ)⁻¹

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem fieldLineTheta_eq : fieldLineTheta F =
    ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ :=
  reciprocal_card_FieldLine

def nextBlockRank (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : ℕ :=
  Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).range

theorem nextBlockRank_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A ≤ Module.finrank (ZMod 2) S :=
  LinearMap.finrank_range_le _

theorem nextBlockRank_independent (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J J' : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A = nextBlockRank S g J' A := by
  have hk : (fieldLineRestrictions S g J A).ker =
      (fieldLineRestrictions S g J' A).ker :=
    ker_orientedBlockRestriction_independent S g (lineGenerator A) (J A) (J' A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  have hdim' := (fieldLineRestrictions S g J' A).finrank_range_add_finrank_ker
  rw [hk] at hdim
  unfold nextBlockRank
  omega

theorem generic_nextBlockRank_dichotomy (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) (A : FieldLine F) :
    nextBlockRank S g J A = Module.finrank (ZMod 2) S ∨
      nextBlockRank S g J A = Module.finrank (ZMod 2) S - 1 := by
  have hk := finrank_ker_orientedBlockRestriction_le_one S g
    (lineGenerator_ne_zero A) hS (J A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).ker ≤ 1 at hk
  unfold nextBlockRank
  omega

theorem generic_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      3 * Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ (3 * (Module.finrank (ZMod 2) S : ℚ)) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_loss_fieldLineRestrictions_le_three_rank S g J hS
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem generic_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    average (fun A => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤ 3 * fieldLineTheta F := by
  classical
  by_cases hr : 0 < Module.finrank (ZMod 2) S
  · exact generic_expected_drop_le _ _ _ hr
      (generic_nextBlockRank_dichotomy S g J hS)
      (generic_block_loss_probability_le S g J hS)
  · have hr0 : Module.finrank (ZMod 2) S = 0 := by omega
    have hnext : ∀ A, nextBlockRank S g J A = 0 := by
      intro A
      have := nextBlockRank_le S g J A
      omega
    simp only [hr0, hnext, DFVSGames.Gadget.Harmonic.harmonic_zero, sub_self]
    have hzero : average (fun _ : FieldLine F => (0 : ℚ)) = 0 := by
      simp [average]
    rw [hzero]
    unfold fieldLineTheta
    positivity

theorem card_loss_fieldLineRestrictions_le_nonzero
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤ Fintype.card S - 1 := by
  classical
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    exact one_ne_zero (congrFun h 0))
  apply card_lossIndices_le_nonzero (fieldLineRestrictions S g J)
    (fun z : S => characterFieldLine A₀ (z : Vec F))
  intro A z hz hzero
  have hk := (mem_ker_orientedBlockRestriction_iff S g
    (lineGenerator_ne_zero A) (J A) hz).mp hzero
  exact characterFieldLine_eq_of_mem (fun h => hz (Subtype.ext h)) hk.1

theorem arbitrary_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  have hc : Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
    simpa only [ZMod.card] using Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  have hcount : (lossIndices (fieldLineRestrictions S g J)).card ≤
      2 ^ Module.finrank (ZMod 2) S :=
    (card_loss_fieldLineRestrictions_le_nonzero S g J).trans
      ((Nat.sub_le _ _).trans_eq hc)
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ ((2 : ℚ) ^ Module.finrank (ZMod 2) S) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem arbitrary_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    average (fun A => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) *
          2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  simpa only [mul_assoc] using arbitrary_expected_drop_le
    (Module.finrank (ZMod 2) S) (nextBlockRank S g J)
    (2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F)
    (nextBlockRank_le S g J) (arbitrary_block_loss_probability_le S g J)

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance harmonicVecLinearEquivFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
local instance harmonicVecLinearEquivFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) := Fintype.ofFinite _

def outgoingLoss (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : ℚ :=
  average (fun i : BlockOrientationIndex F => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
    DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ i).range))

theorem outgoingLoss_eq_line_average
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ = average (fun A : FieldLine F =>
      DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A)) := by
  unfold outgoingLoss average
  rw [mean_block_pairs]
  apply Finset.expect_congr rfl
  intro A _
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  have hrank (J : BlockOrientation A) :
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
        nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A := by
    rw [childCharacter_rank_independent S γ A J (chosenBlockOrientation A)]
    rw [childCharacter_range_eq]
    rfl
  simp_rw [hrank]
  exact Finset.expect_const Finset.univ_nonempty _

theorem generic_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (hS : IsGeneric (traceSpace S)) :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank] using
    generic_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation hS

theorem arbitrary_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank, badRankCoefficient] using
    arbitrary_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation

theorem badRankCoefficient_mono {r s : ℕ} (h : r ≤ s) :
    badRankCoefficient r ≤ badRankCoefficient s := by
  unfold badRankCoefficient
  apply mul_le_mul (harmonic_mono h) (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h)
  · positivity
  · exact harmonic_nonneg _

theorem outgoing_harmonic_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (r₀ : ℕ)
    (hcap : Module.finrank (ZMod 2) S ≤ r₀)
    [Decidable (IsGeneric (traceSpace S))] :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F +
      badRankCoefficient r₀ * fieldLineTheta F * if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  have hθ : 0 ≤ fieldLineTheta F := by unfold fieldLineTheta; positivity
  by_cases hS : IsGeneric (traceSpace S)
  · simpa only [not_true_eq_false, hS, ite_false, mul_zero, add_zero] using
      generic_outgoing_loss_le S γ hS
  · rw [ite_eq_left hS, mul_one]
    calc
      outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F :=
        arbitrary_outgoing_loss_le S γ
      _ ≤ badRankCoefficient r₀ * fieldLineTheta F :=
        mul_le_mul_of_nonneg_right (badRankCoefficient_mono hcap) hθ
      _ ≤ 3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F := by linarith

theorem descendant_harmonic_loss_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S) (r₀ : ℕ)
      (_hcap : Module.finrank (ZMod 2) S ≤ r₀)
      [Decidable (IsGeneric (traceSpace S))],
      average (fun i : BlockOrientationIndex F => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (Descent.childDomain J hJ Q s S L i))) ≤
        3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F *
          if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  intro J hJ Q s S L r₀ hcap hdec
  exact outgoing_harmonic_loss_le S (Descent.commonGamma J hJ Q s S L) r₀ hcap

end

end DFVSGames.Gadget.OutgoingHarmonic

noncomputable section

open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic

def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end DFVSGames.Quadratic
end

noncomputable section

open scoped BigOperators Classical
open Module

namespace DFVSGames.Gadget.FreshGenericity

open _root_.OAI.DFVSGames.Gadget.Orientation Quadratic BlockDescent OrientedBlockKernel

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

def rankSpaceEquiv (e : V ≃ₗ[K] W) (r : ℕ) : RankSpace K V r ≃ RankSpace K W r :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun S => by
    change finrank K S = r ↔ finrank K (S.map e.toLinearMap) = r
    rw [e.finrank_map_eq])

@[simp] theorem rankSpaceEquiv_apply (e : V ≃ₗ[K] W) (r : ℕ)
    (S : RankSpace K V r) :
    (rankSpaceEquiv e r S).val = S.val.map e.toLinearMap := rfl

local instance linearMapFintype [Fintype V] [Fintype W] : Fintype (V →ₗ[K] W) :=
  Fintype.ofInjective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective

local instance linearEquivFintype [Fintype V] [Fintype W] : Fintype (V ≃ₗ[K] W) :=
  Fintype.ofInjective (fun e : V ≃ₗ[K] W => (e : V → W)) DFunLike.coe_injective

local instance submoduleFintype [Fintype V] : Fintype (Submodule K V) :=
  Fintype.ofInjective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective

local instance rankSpaceFintype [Fintype V] (r : ℕ) : Fintype (RankSpace K V r) :=
  inferInstanceAs (Fintype {S : Submodule K V // finrank K S = r})

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def bad (S : Submodule (ZMod 2) (BinaryDual (F := F))) : Prop :=
  ¬ IsGeneric (traceSpace S)

theorem mean_bad_rankSpace (r : ℕ) :
    (𝔼 S : RankSpace (ZMod 2) (BinaryDual (F := F)) r,
      if bad S.val then (1 : ℚ) else 0) = nongenericFraction F r := by
  calc
    _ = 𝔼 S : RankSpace (ZMod 2) (Vec F) r,
        if ¬IsGeneric S.val then (1 : ℚ) else 0 := by
      exact Fintype.expect_equiv (rankSpaceEquiv traceDualEquiv.symm r) _ _
        (fun T => by
          by_cases h : IsGeneric (traceSpace T.val)
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_true_eq_false, ite_false]
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_false_eq_true, ite_true])
    _ = _ := by
      simp only [nongenericFraction, Fintype.expect_eq_sum_div_card,
        Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_fresh_bad_at_line
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) =
      nongenericFraction F
        (finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
          (lineGenerator A)).range) := by
  let E := (blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator A)).range
  calc
    _ = 𝔼 J : BlockOrientation A,
        if bad (E.map J.dualMap.toLinearMap) then (1 : ℚ) else 0 := by
      apply Finset.expect_congr rfl
      intro J _
      rw [childCharacter_range_eq_dual_pullback]
    _ = 𝔼 T : RankSpace (ZMod 2) (BinaryDual (F := F)) (finrank (ZMod 2) E),
        if bad T.val then (1 : ℚ) else 0 := by
      simp only [Fintype.expect_eq_sum_div_card]
      exact mean_dual_pullback E (chosenBlockOrientation A)
        (fun T => if bad T.val then (1 : ℚ) else 0)
    _ = _ := mean_bad_rankSpace _

omit [(A : FieldLine F) → Fintype (BlockOrientation A)] in

theorem unoriented_rank_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
      (lineGenerator A)).range ≤ finrank (ZMod 2) S := by
  calc
    _ ≤ finrank (ZMod 2) (traceSpace S) := LinearMap.finrank_range_le _
    _ = _ := traceSpace_finrank S

theorem fresh_bad_at_line_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) ≤ ε := by
  rw [mean_fresh_bad_at_line]
  exact hgeneric _ ((unoriented_rank_le S γ A).trans hS)

variable [Fintype (FieldLine F)]

theorem fresh_bad_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F))
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 i : BlockOrientationIndex F,
      if bad (childCharacter orientedBlockLinear γ i).range then (1 : ℚ) else 0) ≤ ε := by
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  calc
    _ ≤ 𝔼 _A : FieldLine F, ε := Finset.expect_le_expect
      (fun A _ => fresh_bad_at_line_le S γ A r₀ ε hS hgeneric)
    _ = ε := Fintype.expect_const _

theorem descendant_bad_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J := orientedBlockLinear (F := F)
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S)
      (r₀ : ℕ) (ε : ℚ), finrank (ZMod 2) S ≤ r₀ →
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) →
      (𝔼 i : BlockOrientationIndex F,
        if bad (Descent.childDomain J hJ Q s S L i) then (1 : ℚ) else 0) ≤ ε := by
  intro J hJ Q s S L r₀ ε hS hgeneric
  exact fresh_bad_le S (Descent.commonGamma J hJ Q s S L) r₀ ε hS hgeneric

end DFVSGames.Gadget.FreshGenericity
end

end OAI
