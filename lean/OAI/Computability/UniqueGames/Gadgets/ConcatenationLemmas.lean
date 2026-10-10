import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section

namespace UniqueGamesTheorem.Gadget

open scoped BigOperators

section Parent

variable {k I P R X B : Type*} [CommRing k] [Fintype I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

/-- Sum of the oriented block inclusions on the child logical symbols. -/
def aggregate (J : I → B →ₗ[k] X × B) : (I → B) →ₗ[k] X × B where
  toFun v := ∑ i, J i (v i)
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

/-- The same aggregate, evaluated on actual child shifts. -/
def shiftAggregate (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    (I → R) →ₗ[k] X × B where
  toFun h := aggregate J (fun i => lam (h i))
  map_add' u v := by simp [aggregate, Finset.sum_add_distrib]
  map_smul' c v := by simp [aggregate, Finset.smul_sum]

/-- The parent shift space: precisely the child shifts with zero first
aggregate coordinate. -/
def parentShifts (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    Submodule k (I → R) :=
  LinearMap.ker ((LinearMap.fst k X B).comp (shiftAggregate J lam))

/-- Parent logical translation, the second aggregate coordinate. -/
def parentLogical (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B) :
    parentShifts J lam →ₗ[k] B :=
  ((LinearMap.snd k X B).comp (shiftAggregate J lam)).comp
    (parentShifts J lam).subtype

/-- Embedding parent shifts in the actual product of child input spaces. -/
def parentEmbed (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) : parentShifts J lam →ₗ[k] (I → P) where
  toFun h i := e (h.val i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

theorem parentEmbed_injective (J : I → B →ₗ[k] X × B) (lam : R →ₗ[k] B)
    (e : R →ₗ[k] P) (he : Function.Injective e) :
    Function.Injective (parentEmbed J lam e) := by
  intro u v huv
  apply Subtype.ext
  funext i
  exact he (congrFun huv i)

theorem shiftAggregate_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (shiftAggregate J lam) := by
  classical
  intro v
  obtain ⟨u, hu⟩ := hJ v
  choose h hh using fun i => hlam (u i)
  refine ⟨h, ?_⟩
  have heq : (fun i => lam (h i)) = u := funext hh
  change aggregate J (fun i => lam (h i)) = v
  rw [heq, hu]

theorem parentLogical_surjective (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) : Function.Surjective (parentLogical J lam) := by
  intro b
  obtain ⟨h, hh⟩ := shiftAggregate_surjective J hJ lam hlam (0, b)
  have hm : h ∈ parentShifts J lam := by
    change (shiftAggregate J lam h).1 = 0
    rw [hh]
  refine ⟨⟨h, hm⟩, ?_⟩
  change (shiftAggregate J lam h).2 = b
  rw [hh]

def parentOutput (J : I → B →ₗ[k] X × B) (C : P → B) (Q : X → B)
    (u : I → P) : B :=
  let v := aggregate J (fun i => C (u i))
  v.2 + Q v.1

/-- Child equivariance gives the actual aggregate translation formula. -/
theorem aggregate_output_shift (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : I → R) :
    aggregate J (fun i => C (u i + e (h i))) =
      aggregate J (fun i => C (u i)) + shiftAggregate J lam h := by
  simp only [hC]
  change aggregate J ((fun i => C (u i)) + (fun i => lam (h i))) = _
  exact (aggregate J).map_add _ _

/-- Parent equivariance is derived for the kernel-defined shift space. -/
theorem parentOutput_equivariant (J : I → B →ₗ[k] X × B)
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (C : P → B) (Q : X → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (u : I → P) (h : parentShifts J lam) :
    parentOutput J C Q (u + parentEmbed J lam e h) =
      parentOutput J C Q u + parentLogical J lam h := by
  have hzero : (shiftAggregate J lam h.val).1 = 0 := h.property
  unfold parentOutput
  change (aggregate J (fun i => C (u i + e (h.val i)))).2 +
    Q (aggregate J (fun i => C (u i + e (h.val i)))).1 = _
  rw [aggregate_output_shift J e lam C hC]
  simp only [Prod.fst_add, Prod.snd_add, hzero, add_zero]
  change _ = _ + (shiftAggregate J lam h.val).2
  abel

end Parent

section Difference

variable {P R B : Type*} [AddCommGroup P] [AddCommGroup B]

/-- The output difference at a fixed perturbation is invariant under logical
shifts. This is the conditioning input for the exact nonlinear noise law. -/
theorem output_difference_shift
    (C : P → B) (e : R → P) (lam : R → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (u a : P) (h : R) :
    C (u + e h + a) - C (u + e h) = C (u + a) - C u := by
  have hreorder : u + e h + a = (u + a) + e h := by abel
  rw [hreorder, hC, hC]
  abel

end Difference

end UniqueGamesTheorem.Gadget

end

section

namespace UniqueGamesTheorem.Gadget.EmbeddedConditional

open scoped BigOperators

variable {k P R B Z M : Type*} [Ring k]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup B] [Module k B] [Fintype B]
variable [AddCommMonoid M] [Module ℚ≥0 M]

/-- Exact conditional uniformity for an embedded carrier of logical shifts.
No injectivity of the embedding is needed for this averaging statement. -/
theorem expect_uniform_output_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (D : P → Z) (hD : ∀ u h, D (u + e h) = D u)
    (f : B → Z → M) :
    (𝔼 u, f (C u) (D u)) = 𝔼 u, 𝔼 b : B, f b (D u) := by
  classical
  have hs (b : B) :
      (𝔼 u, f (C u + b) (D u)) = 𝔼 u, f (C u) (D u) := by
    obtain ⟨h, rfl⟩ := hlam b
    apply Fintype.expect_equiv (Equiv.addRight (e h))
    intro u
    simp only [Equiv.coe_addRight, hC, hD]
  calc
    (𝔼 u, f (C u) (D u)) = 𝔼 b : B, 𝔼 u, f (C u + b) (D u) := by
      simp only [hs, Fintype.expect_const]
    _ = 𝔼 u, 𝔼 b : B, f (C u + b) (D u) := Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 b : B, f b (D u) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Fintype.expect_equiv (Equiv.addLeft (C u))
      intro b
      rfl

/-- Unconditional uniformity is the constant-observable instance. -/
theorem expect_equivariant_output (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (f : B → M) :
    (𝔼 u, f (C u)) = 𝔼 b : B, f b := by
  have he := expect_uniform_output_embedded e lam hlam C hC
    (fun _ => ()) (fun _ _ => rfl) (fun b _ => f b)
  simpa only [Fintype.expect_const] using he

/-- Surjective linear maps send uniform finite input to uniform output. -/
theorem expect_linear_surjective (f : P →ₗ[k] B) (hf : Function.Surjective f)
    (test : B → M) : (𝔼 u, test (f u)) = 𝔼 b : B, test b := by
  apply expect_equivariant_output (LinearMap.id : P →ₗ[k] P) f hf f
  intro u h
  exact f.map_add u h

/-- Fixed-perturbation conditional uniformity without a range conversion. -/
theorem expect_uniform_difference_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (a : P) (f : B → B → M) :
    (𝔼 u, f (C u) (C (u + a) - C u)) =
      𝔼 u, 𝔼 b : B, f b (C (u + a) - C u) := by
  apply expect_uniform_output_embedded e lam hlam C hC
  intro u h
  have he : u + e h + a = (u + a) + e h := by
    simp only [add_assoc, add_comm (e h) a]
  rw [he, hC, hC, add_sub_add_right_eq_sub]

end UniqueGamesTheorem.Gadget.EmbeddedConditional

end

section

namespace UniqueGamesTheorem.Gadget.Enlargement

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
    simp only [Submodule.mem_dualCoannihilator, Submodule.mem_comap]
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
  push_cast
  rfl

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

end UniqueGamesTheorem.Gadget.Enlargement

end

section

namespace UniqueGamesTheorem.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The finite harmonic potential, by its exact rational recurrence. -/
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

/-- Rational expectation under uniform sampling on a finite space. -/
def average (f : Ω → ℚ) : ℚ := Finset.univ.expect f

/-- Probability of a decidable event in the finite experiment. -/
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

/-- A bijection swapping an event with its complement proves exact half
probability. At a leaf the bijection is translation by a symbol on which a
nonzero binary character is one. -/
theorem probability_eq_half_of_swap [Nonempty Ω]
    (p : Ω → Prop) [DecidablePred p] (e : Ω ≃ Ω)
    (hswap : ∀ ω, p (e ω) ↔ ¬ p ω) : probability p = 1 / 2 := by
  have he : probability (fun ω => ¬ p ω) = probability p := by
    apply Fintype.expect_equiv e
    intro ω
    simp only [hswap ω]
  rw [probability_not] at he
  linarith

/-- Every nonzero binary additive character detects precisely half of uniform
symbols. The witness may depend on the previously sampled path. -/
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

/-- A surviving family contains a nonzero character, so its detection event
contains an event of exact half probability. -/
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

/-- A generic rank-`r` space loses either zero or one dimension. Its harmonic
drop is exactly the loss indicator times `1/r`. -/
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

/-- The generic loss probability `3rθ` becomes the rank-independent harmonic
loss bound `3θ`. -/
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

/-- Without genericity, charge the entire harmonic potential only on paths
where some rank is lost. -/
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

/-- Averaging a conditional rank-loss estimate uses only a bound on the bad
space's probability, even when the selected lift depends on that space. -/
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

/-- Expected harmonic losses telescope. The ranks may be arbitrary functions
of the full path; this assertion introduces no independence premise. -/
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

/-- The potential-to-survival step needs only the final finite experiment,
allowing earlier levels to have different path sample spaces. -/
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

/-- At depth `s` with `4sθ ≤ H(r₀)/2`, at least half the paths have nonzero
terminal rank. The terminal bound follows from rank monotonicity in the actual
gadget, and is kept explicit here. -/
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

/-- Direct assembly of the adaptive calculation. `conditionalDrop` is the
conditional mean after fixing the history; `hmean` is the finite averaging
identity. The only assertion about bad orientations is their probability
bound, so a future lift is allowed to depend on the incoming orientation. -/
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

/-- A final independent uniform symbol detects a surviving character with
probability at least one half. Multiplying this conditional bound by the
surviving-path probability gives the required quarter. -/
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

/-- Uniform paths and a separately sampled uniform terminal symbol have the
product law used in the leaf-noise experiment. -/
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

/-- Terminal family detection with actual binary characters rather than an
assumed conditional probability bound. A character can be selected separately
on every surviving path. -/
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

end UniqueGamesTheorem.Gadget.Harmonic

end

end OAI
