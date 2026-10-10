import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Uniform averaging over labelled samples factors over any partition of the labels. -/
theorem expect_pi_partition {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [AddCommMonoid M] [Module ℚ≥0 M] (p : ι → Prop) [DecidablePred p]
    (F : (ι → A) → M) :
    (𝔼 f : ι → A, F f) =
      𝔼 a : {i // p i} → A, 𝔼 b : {i // ¬p i} → A,
        F (fun i => if h : p i then a ⟨i,h⟩ else b ⟨i,h⟩) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => A)
  calc
    (𝔼 f : ι → A, F f) = 𝔼 ab, F (e.symm ab) :=
      Fintype.expect_equiv e F (fun ab => F (e.symm ab)) (fun f => by simp)
    _ = _ := by
      simpa [e, Equiv.piEquivPiSubtypeProd] using
        Finset.expect_product Finset.univ Finset.univ (fun ab => F (e.symm ab))

/-- The same partition identity in explicit normalized-sum form. -/
theorem normalized_sum_pi_partition {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → Prop) [DecidablePred p] (F : (ι → A) → ℂ) :
    (∑ f : ι → A, F f) / Fintype.card (ι → A) =
      (∑ a : {i // p i} → A,
        (∑ b : {i // ¬p i} → A,
          F (fun i => if h : p i then a ⟨i,h⟩ else b ⟨i,h⟩)) /
            Fintype.card ({i // ¬p i} → A)) / Fintype.card ({i // p i} → A) := by
  simpa only [Fintype.expect_eq_sum_div_card] using expect_pi_partition p F

/-- Average over a finite probability space of an indicator is its relative cardinality. -/
lemma expect_finset_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (B : Finset Ω) :
    (𝔼 x : Ω, if x ∈ B then (1 : ℝ) else 0) =
      (B.card : ℝ) / Fintype.card Ω := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  simp

/-- Exposing some variables costs only the proportion of exceptional exposures.
The inner finite type can itself be a product of independent fresh sample blocks. -/
theorem conditional_average_norm_bound {Ω A : Type*} [Fintype Ω] [Fintype A]
    [Nonempty Ω] [Nonempty A] (F : Ω → A → ℂ) (B : Finset Ω) (δ : ℝ)
    (hδ : 0 ≤ δ) (hunit : ∀ ω a, ‖F ω a‖ ≤ 1)
    (hgood : ∀ ω, ω ∉ B → ‖𝔼 a : A, F ω a‖ ≤ δ) :
    ‖𝔼 ω : Ω, 𝔼 a : A, F ω a‖ ≤ (B.card : ℝ) / Fintype.card Ω + δ := by
  classical
  have hbound (ω : Ω) : ‖𝔼 a : A, F ω a‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 a : A, ‖F ω a‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _a : A, (1 : ℝ) := Finset.expect_le_expect (fun a _ => hunit ω a)
      _ = 1 := Fintype.expect_const 1
  calc
    _ ≤ 𝔼 ω : Ω, ‖𝔼 a : A, F ω a‖ := RCLike.norm_expect_le (K := ℂ)
    _ ≤ 𝔼 ω : Ω, ((if ω ∈ B then (1 : ℝ) else 0) + δ) := by
      apply Finset.expect_le_expect
      intro ω hω
      by_cases hb : ω ∈ B
      · simp only [ite_eq_left hb]
        linarith [hbound ω]
      · simpa only [ite_eq_right hb, zero_add] using hgood ω hb
    _ = _ := by
      rw [Finset.expect_add_distrib, expect_finset_indicator, Fintype.expect_const]

/-- A finite reindexing into exposed and fresh coordinates gives exact Fubini averaging. -/
theorem expect_equiv_prod {Ω E A M : Type*} [Fintype Ω] [Fintype E] [Fintype A]
    [AddCommMonoid M] [Module ℚ≥0 M] (e : Ω ≃ E × A) (F : Ω → M) :
    (𝔼 ω : Ω, F ω) = 𝔼 x : E, 𝔼 a : A, F (e.symm (x,a)) := by
  calc
    (𝔼 ω : Ω, F ω) = 𝔼 xa, F (e.symm xa) :=
      Fintype.expect_equiv e F (fun xa => F (e.symm xa)) (fun ω => by simp)
    _ = _ := by
      simpa using Finset.expect_product Finset.univ Finset.univ (fun xa => F (e.symm xa))

/-- The conditional estimate transported back to the original labelled sample space. -/
theorem exposure_average_norm_bound {Ω E A : Type*}
    [Fintype Ω] [Fintype E] [Fintype A] [Nonempty E] [Nonempty A]
    (e : Ω ≃ E × A) (F : Ω → ℂ) (B : Finset E) (δ : ℝ)
    (hδ : 0 ≤ δ) (hunit : ∀ ω, ‖F ω‖ ≤ 1)
    (hgood : ∀ x, x ∉ B → ‖𝔼 a : A, F (e.symm (x,a))‖ ≤ δ) :
    ‖𝔼 ω : Ω, F ω‖ ≤ (B.card : ℝ) / Fintype.card E + δ := by
  rw [expect_equiv_prod e F]
  exact conditional_average_norm_bound (fun x a => F (e.symm (x,a))) B δ hδ
    (fun x a => hunit _) hgood

/-- Multipliers fixed by the exposure and of norm at most one do not spoil cancellation. -/
theorem conditional_average_phase_bound {Ω A : Type*} [Fintype Ω] [Fintype A]
    [Nonempty Ω] [Nonempty A] (F : Ω → A → ℂ) (phase : Ω → ℂ)
    (B : Finset Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hphase : ∀ ω, ‖phase ω‖ ≤ 1) (hunit : ∀ ω a, ‖F ω a‖ ≤ 1)
    (hgood : ∀ ω, ω ∉ B → ‖𝔼 a : A, F ω a‖ ≤ δ) :
    ‖𝔼 ω : Ω, 𝔼 a : A, phase ω * F ω a‖ ≤
      (B.card : ℝ) / Fintype.card Ω + δ := by
  apply conditional_average_norm_bound _ B δ hδ
  · intro ω a
    rw [norm_mul]
    simpa using mul_le_mul (hphase ω) (hunit ω a) (norm_nonneg _) (by norm_num)
  · intro ω hω
    rw [← Finset.mul_expect, norm_mul]
    simpa using mul_le_mul (hphase ω) (hgood ω hω) (norm_nonneg _) (by norm_num)

/-- Uniform samples on coordinates not inspected by the function can be discarded. -/
theorem expect_restrict_coordinates {ι A M : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]
    [AddCommMonoid M] [Module ℚ≥0 M] (p : ι → Prop) [DecidablePred p]
    (F : ({i // p i} → A) → M) :
    (𝔼 f : ι → A, F (fun i => f i)) = 𝔼 a : {i // p i} → A, F a := by
  rw [expect_pi_partition p]
  simp only [dite_eq_left, Subtype.property, Fintype.expect_const]

/-- Sampling any injectively selected labels gives the same uniform product law. -/
theorem expect_injective_coordinates {ι κ A M : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype A] [Nonempty A] [AddCommMonoid M] [Module ℚ≥0 M]
    (e : κ ↪ ι) (F : (κ → A) → M) :
    (𝔼 f : ι → A, F (fun k => f (e k))) = 𝔼 a : κ → A, F a := by
  classical
  let : Fintype (Set.range e) := Subtype.fintype (fun i => i ∈ Set.range e)
  let E := Equiv.ofInjective e e.injective
  have h := expect_restrict_coordinates (fun i => i ∈ Set.range e)
    (fun a => F (fun k => a (E k)))
  calc
    (𝔼 f : ι → A, F (fun k => f (e k))) =
        𝔼 a : (Set.range e) → A, F (fun k => a (E k)) := h
    _ = 𝔼 a : κ → A, F a := by
      apply Fintype.expect_equiv (Equiv.arrowCongr E.symm (Equiv.refl A))
      intro a
      rfl

/-- The normalized count of a coordinate event is unaffected by unused independent labels. -/
theorem injective_coordinate_event_fraction {ι κ A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype A] [Nonempty A] (e : κ ↪ ι) (R : (κ → A) → Prop) [DecidablePred R] :
    ((Finset.univ.filter (fun f : ι → A => R (fun k => f (e k)))).card : ℝ) /
        Fintype.card (ι → A) =
      ((Finset.univ.filter R).card : ℝ) / Fintype.card (κ → A) := by
  simpa only [Fintype.expect_eq_sum_div_card, Finset.sum_boole] using
    expect_injective_coordinates e (fun a => if R a then (1 : ℝ) else 0)

end Problem337

end

end OAI
