import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Pi
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Gadgets.ConcatenationLemmas
import OAI.Computability.UniqueGames.Gadgets.QuotientLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem compLeft_surjective (lam : R →ₗ[k] B) (hlam : Function.Surjective lam) :
    Function.Surjective (lam.compLeft I) := by
  intro b
  choose h hh using fun i => hlam (b i)
  exact ⟨h, funext hh⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem aggregate_single (J : I → B →ₗ[k] X × B) (i : I) (b : B) :
    aggregate J (Pi.single i b) = J i b := by
  classical
  change (∑ j, J j ((Pi.single i b : I → B) j)) = J i b
  simp only [LinearMap.apply_single]
  simp

omit [Fintype I] [Fintype P] [Fintype B] [DecidableEq B] in
theorem child_outputs_perturb (C : P → B) (u : I → P) (i : I) (a : P) :
    (fun j => C ((u + (Pi.single i a : I → P)) j)) =
      (fun j => C (u j)) + (Pi.single i (C (u i + a) - C (u i)) : I → B) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [add_comm (C (u i)), sub_add_cancel]
  · simp [Pi.single_eq_of_ne hj]

omit [Module k P] [Fintype P] [Fintype X] [Fintype B] [DecidableEq B] in
theorem parent_output_perturb (J : I → B →ₗ[k] X × B) (C : P → B)
    (F : X × B → B) (u : I → P) (i : I) (a : P) :
    F (aggregate J (fun j => C ((u + (Pi.single i a : I → P)) j))) =
      F (aggregate J (fun j => C (u j)) + J i (C (u i + a) - C (u i))) := by
  rw [child_outputs_perturb, map_add, aggregate_single]

/-- The exact conditional-uniform and coordinate-marginal law for a fixed
selected index and fixed child perturbation. -/
theorem expect_change_at_index (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (i : I) (a : P) :
    (𝔼 u : I → P,
      change F (aggregate J (fun j => C (u j))) (J i (C (u i + a) - C (u i)))) =
      𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
  have hCt : ∀ (u : I → P) (h : I → R),
      (fun j => C ((u + (e.compLeft I) h) j)) =
        (fun j => C (u j)) + (lam.compLeft I) h := by
    intro u h
    funext j
    exact hC (u j) (h j)
  have hDt : ∀ (u : I → P) (h : I → R),
      C ((u + (e.compLeft I) h) i + a) - C ((u + (e.compLeft I) h) i) =
        C (u i + a) - C (u i) := by
    intro u h
    change C (u i + e (h i) + a) - C (u i + e (h i)) = _
    have he : u i + e (h i) + a = (u i + a) + e (h i) := by
      simp only [add_assoc, add_comm (e (h i)) a]
    rw [he, hC, hC, add_sub_add_right_eq_sub]
  calc
    _ = 𝔼 u : I → P, 𝔼 b : I → B,
        change F (aggregate J b) (J i (C (u i + a) - C (u i))) :=
      EmbeddedConditional.expect_uniform_output_embedded
        (e.compLeft I) (lam.compLeft I) (compLeft_surjective lam hlam)
        (fun u j => C (u j)) hCt (fun u => C (u i + a) - C (u i)) hDt
        (fun b d => change F (aggregate J b) (J i d))
    _ = 𝔼 u : I → P, 𝔼 z : X × B,
        change F z (J i (C (u i + a) - C (u i))) := by
      apply Finset.expect_congr rfl
      intro u _
      exact EmbeddedConditional.expect_linear_surjective (aggregate J) hJ
        (fun z => change F z (J i (C (u i + a) - C (u i))))
    _ = 𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
      exact EmbeddedConditional.expect_linear_surjective
        (LinearMap.proj i : (I → P) →ₗ[k] P)
        (fun x => ⟨fun _ => x, rfl⟩)
        (fun x : P => 𝔼 z : X × B, change F z (J i (C (x + a) - C x)))

omit [DecidableEq I] in
/-- The averaged block kernel includes zero differences by multiplication with
their nonzero indicator. -/
theorem kernel_all (J : I → B →ₗ[k] X × B) (F : X × B → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ)
    (d : B) :
    (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ * (if d ≠ 0 then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · simp only [ite_eq_left hd, mul_one]
    exact hk d hd

/-- One exact nonlinear recurrence on the actual product input and the actual
single-coordinate noise. The only remaining block obligation is `hk`. -/
theorem parent_change_recurrence {N : Type*} [Fintype N]
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (C : P → B) (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (noise : N → P) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ) :
    (𝔼 i, 𝔼 n : N, 𝔼 u : I → P,
      if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
        F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
      ρ * (𝔼 n : N, 𝔼 x : P, if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
  classical
  have hpoint (i : I) (n : N) :
      (𝔼 u : I → P,
        if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
          F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
        𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
    simp_rw [parent_output_perturb]
    exact expect_change_at_index J hJ e lam hlam C hC F i (noise n)
  simp_rw [hpoint]
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 n : N, 𝔼 x : P, 𝔼 i,
        𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
      apply Finset.expect_congr rfl
      intro n _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 n : N, 𝔼 x : P,
        ρ * (if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      apply Finset.expect_congr rfl
      intro x _
      simpa only [ne_eq, sub_eq_zero] using kernel_all J F ρ hk (C (x + noise n) - C x)
    _ = _ := by simp only [← Finset.mul_expect]

end UniqueGamesTheorem.Gadget.NonlinearRecurrence

end

section

namespace UniqueGamesTheorem.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

def shifts (s : Stage k B) : Submodule k s.Input := LinearMap.range s.embed

noncomputable def shiftEquiv (s : Stage k B) : s.Shift ≃ₗ[k] shifts s :=
  LinearEquiv.ofInjective s.embed s.embed_injective

@[simp] theorem shiftEquiv_coe (s : Stage k B) (h : s.Shift) :
    ((shiftEquiv s h : shifts s) : s.Input) = s.embed h := rfl

@[simp] theorem embed_shiftEquiv_symm (s : Stage k B) (h : shifts s) :
    s.embed ((shiftEquiv s).symm h) = (h : s.Input) :=
  LinearEquiv.ofInjective_symm_apply s.embed h

noncomputable def logical (s : Stage k B) : shifts s →ₗ[k] B :=
  s.logical.comp (shiftEquiv s).symm.toLinearMap

@[simp] theorem logical_shiftEquiv (s : Stage k B) (h : s.Shift) :
    logical s (shiftEquiv s h) = s.logical h := by
  simp [logical]

theorem logical_surjective (s : Stage k B) : Function.Surjective (logical s) := by
  intro b
  obtain ⟨h, hh⟩ := s.logical_surjective b
  exact ⟨shiftEquiv s h, (logical_shiftEquiv s h).trans hh⟩

theorem equivariant (s : Stage k B) :
    Quotient.Equivariant (shifts s) (logical s) s.output := by
  intro u h
  have he := s.equivariant u ((shiftEquiv s).symm h)
  simpa only [embed_shiftEquiv_symm, logical, LinearMap.comp_apply,
    LinearEquiv.coe_coe] using he

abbrev Space (s : Stage k B) := Quotient.Space (shifts s) (logical s)

noncomputable def projection (s : Stage k B) : s.Input →ₗ[k] Space s :=
  Quotient.projection (shifts s) (logical s)

theorem projection_surjective (s : Stage k B) : Function.Surjective (projection s) :=
  Quotient.projection_surjective (shifts s) (logical s)

instance spaceFinite (s : Stage k B) : Finite (Space s) :=
  Finite.of_surjective (projection s) (projection_surjective s)

noncomputable def shift (s : Stage k B) : B →ₗ[k] Space s :=
  Quotient.logicalShift (shifts s) (logical s) (logical_surjective s)

theorem shift_injective (s : Stage k B) : Function.Injective (shift s) :=
  Quotient.logicalShift_injective (shifts s) (logical s) (logical_surjective s)

@[simp] theorem shift_logical (s : Stage k B) (h : s.Shift) :
    shift s (s.logical h) = projection s (s.embed h) := by
  rw [← logical_shiftEquiv s h]
  exact Quotient.logicalShift_lambda (shifts s) (logical s) (logical_surjective s)
    (shiftEquiv s h)

noncomputable def output (s : Stage k B) : Space s → B :=
  Quotient.output (shifts s) (logical s) s.output (equivariant s)

@[simp] theorem output_projection (s : Stage k B) (u : s.Input) :
    output s (projection s u) = s.output u := rfl

theorem output_equivariant (s : Stage k B) (x : Space s) (b : B) :
    output s (x + shift s b) = output s x + b :=
  Quotient.output_equivariant (shifts s) (logical s) (logical_surjective s)
    s.output (equivariant s) x b

/-- Original finite noise choices, pushed through the actual quotient map. -/
noncomputable def noise (s : Stage k B) : s.Noise → Space s :=
  fun t => projection s (s.noise t)

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

theorem character_logical (s : Stage k B) (g : Space s →ₗ[k] k) (h : s.Shift) :
    (g.comp (projection s)) (s.embed h) = (g.comp (shift s)) (s.logical h) := by
  simp only [LinearMap.comp_apply, shift_logical]

theorem noise_detection_iff {I : Type*} (s : Stage k B)
    (family : I → Space s →ₗ[k] k) (t : s.Noise) :
    (∃ i, family i (noise s t) ≠ 0) ↔
      ∃ i, (family i).comp (projection s) (s.noise t) ≠ 0 := Iff.rfl

/-- The quotient is again a finite stage; its logical map is now the identity. -/
noncomputable def toStage [Finite B] (s : Stage k B) : Stage k B where
  Input := Space s
  Shift := B
  Noise := s.Noise
  embed := shift s
  embed_injective := shift_injective s
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := output s
  equivariant := output_equivariant s
  noise := noise s

end UniqueGamesTheorem.Gadget.StageQuotient

end

section

noncomputable section

namespace UniqueGamesTheorem.Gadget.EnlargementConstruction

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

local instance enlargementCopiesFintype : Fintype (Copies B K) := copiesFintype

def productEmbed (i : B →ₗ[ZMod 2] V) :
    (Copies B K → B) →ₗ[ZMod 2] (Copies B K → V) where
  toFun b L := i (b L)
  map_add' b c := by ext L; exact map_add i (b L) (c L)
  map_smul' t b := by ext L; exact map_smul i t (b L)

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K]
  [FiniteDimensional (ZMod 2) K] [Fintype V] in
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

omit [Fintype B] [FiniteDimensional (ZMod 2) B] [Fintype K]
  [FiniteDimensional (ZMod 2) K] [Module (ZMod 2) V] [Fintype V] in
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
  rw [add_single_eq_update, enlargedOutput_update_ne_iff]

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

omit [Fintype B] [FiniteDimensional (ZMod 2) B]
  [Fintype K] [FiniteDimensional (ZMod 2) K] in
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
      congr 1
      funext z
      apply propext
      exact (change_iff i hi C hC noise hdim b₀ hb₀ z.1 z.2.1 z.2.2).trans
        (enlargedOutput_update_ne_iff C z.1 z.2.1 (z.1 z.2.1 + noise z.2.2)).symm
    _ = _ := enlarged_random_copy_probability C noise

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

end UniqueGamesTheorem.Gadget.EnlargementConstruction

end

end

section

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace UniqueGamesTheorem.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

noncomputable def pullbackFullLift (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    Lift s (⊤ : Submodule k (Module.Dual k B)) where
  family :=
    { toFun z := (ψ z.val).comp (StageQuotient.projection s)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  agrees := by
    intro z h
    change ψ z.val (StageQuotient.projection s (s.embed h)) = z.val (s.logical h)
    rw [← StageQuotient.shift_logical]
    exact hψ z.val (s.logical h)

omit [Finite B] in
theorem pullback_detection_iff (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) (n : s.Noise) :
    (∃ z, (pullbackFullLift s ψ hψ).family z (s.noise n) ≠ 0) ↔
      ∃ z, ψ z (StageQuotient.noise s n) ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, Submodule.mem_top⟩, hz⟩

omit [Finite B] in
/-- Any checked full-lift probability bound before quotienting applies to
every full family on the actual quotient, on the same noise sampler. -/
theorem full_detection_after_quotient (s : Stage k B) [Fintype s.Noise] (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    q ≤ characterDetection (StageQuotient.noise s) ψ := by
  classical
  have h := hfull (pullbackFullLift s ψ hψ)
  simpa only [characterDetection, pullback_detection_iff] using h

omit [Finite B] in
/-- The form consumed by the injection enlargement: injectivity on the base
logical alphabet suffices for the same detection probability. -/
theorem target_detection_after_quotient (s : Stage k B) [Fintype s.Noise]
    {E : Type*} [AddCommGroup E] [Module k E] [DecidableEq E]
    (T : StageQuotient.Space s →ₗ[k] E) (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (hinj : Function.Injective (T.comp (StageQuotient.shift s))) :
    q ≤ probability (fun n => T (StageQuotient.noise s n) ≠ 0) := by
  exact target_detection_of_full_lift_bound (StageQuotient.noise s)
    (StageQuotient.shift s) T q (full_detection_after_quotient s q hfull) hinj

end UniqueGamesTheorem.Gadget.QuotientDetection

end

section

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace UniqueGamesTheorem.Gadget.StageNoiseRecurrence

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
    _ = _ := by simp

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

end UniqueGamesTheorem.Gadget.StageNoiseRecurrence

end

end OAI
