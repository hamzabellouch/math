import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

namespace MaxCutGames.Gadget

section

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

variable {P R B : Type*} [AddCommGroup P] [AddCommGroup R] [AddCommGroup B]

omit [AddCommGroup R] in
/-- The output difference at a fixed perturbation is invariant under logical
shifts. This is the conditioning input for the exact nonlinear noise law. -/
theorem output_difference_shift
    (C : P → B) (e : R → P) (lam : R → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (u a : P) (h : R) :
    C (u + e h + a) - C (u + e h) = C (u + a) - C u := by
  have hreorder : u + e h + a = (u + a) + e h := by abel
  rw [hreorder, hC, hC]
  abel

end

section

universe u v

/-- An equivariant finite stage, including its concrete finite noise sampler. -/
structure Stage (k : Type u) (B : Type v) [CommRing k]
    [AddCommGroup B] [Module k B] where
  Input : Type v
  Shift : Type v
  Noise : Type v
  [inputAdd : AddCommGroup Input]
  [inputModule : Module k Input]
  [shiftAdd : AddCommGroup Shift]
  [shiftModule : Module k Shift]
  [inputFinite : Finite Input]
  [shiftFinite : Finite Shift]
  [noiseFinite : Finite Noise]
  [noiseNonempty : Nonempty Noise]
  embed : Shift →ₗ[k] Input
  embed_injective : Function.Injective embed
  logical : Shift →ₗ[k] B
  logical_surjective : Function.Surjective logical
  output : Input → B
  equivariant : ∀ u h, output (u + embed h) = output u + logical h
  noise : Noise → Input

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

namespace Stage

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B] [Finite B]

/-- The height-zero input, shift and uniform noise alphabet. -/
def base : Stage k B where
  Input := B
  Shift := B
  Noise := B
  embed := LinearMap.id
  embed_injective := Function.injective_id
  logical := LinearMap.id
  logical_surjective := Function.surjective_id
  output := id
  equivariant := by intros; rfl
  noise := id

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- One complete recursive level, with actual single-coordinate leaf noise. -/
noncomputable def next (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B)
    (s : Stage k B) : Stage k B where
  Input := I → s.Input
  Shift := parentShifts J s.logical
  Noise := I × s.Noise
  embed := parentEmbed J s.logical s.embed
  embed_injective := parentEmbed_injective J s.logical s.embed s.embed_injective
  logical := parentLogical J s.logical
  logical_surjective := parentLogical_surjective J hJ s.logical s.logical_surjective
  output := parentOutput J s.output Q
  equivariant := parentOutput_equivariant J s.embed s.logical s.output Q s.equivariant
  noise := fun t => Pi.single t.1 (s.noise t.2)

/-- The finite stage at any natural height, using the same alphabet and block
family at every level. Surjectivity and equivariance have been proved by the
constructor, and hence are available at every height without extra hypotheses. -/
noncomputable def iterate (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) : ℕ → Stage k B
  | 0 => base
  | n + 1 => next J hJ Q (iterate J hJ Q n)

@[simp] theorem iterate_zero (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    iterate J hJ Q 0 = base := rfl

@[simp] theorem iterate_succ (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (n : ℕ) :
    iterate J hJ Q (n + 1) = next J hJ Q (iterate J hJ Q n) := rfl

end Stage

end

/-!
# Common-parent factorization before fresh orientation

This is the linear algebra in the lift-factorization lemma of v2 Section 2.
The map `gamma` is obtained from the whole parent family and the first
aggregate coordinate. It is chosen once, before any child is selected.
No rank, genericity, or independence assumption is needed for this step.
-/

section

variable {k S T X B : Type*} [Field k]
variable [AddCommGroup S] [Module k S]
variable [AddCommGroup T] [Module k T]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]

/-- A linear family vanishing on the kernel of a surjection factors as one
linear family on the target. In particular the factor is linear in its
character parameter, rather than a separate arbitrary choice for each one. -/
theorem family_factors_of_ker
    (f : T →ₗ[k] X) (hf : Function.Surjective f)
    (ψ : S →ₗ[k] (T →ₗ[k] k))
    (hker : ∀ z t, f t = 0 → ψ z t = 0) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ z t, ψ z t = γ z (f t) := by
  obtain ⟨σ, hσ⟩ := f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hf)
  have hσ_apply (x : X) : f (σ x) = x := congrArg (fun g : X →ₗ[k] X => g x) hσ
  let γ : S →ₗ[k] (X →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp σ
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  refine ⟨γ, fun z t => ?_⟩
  have hz := hker z (t - σ (f t)) (by rw [map_sub, hσ_apply, sub_self])
  have heq : ψ z t - ψ z (σ (f t)) = 0 := by simpa only [map_sub] using hz
  exact sub_eq_zero.mp heq

/-- The common first-coordinate character of a parent lift. `ψ z` is the
parent character on child shifts, `ζ z` its prescribed logical character,
and `(a,b)` the aggregate. A parent shift is exactly a tuple with `a=0`.
The conclusion quantifies one `γ` before all tuples and all later children. -/
theorem common_parent_factorization
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ z t, ψ z t = γ z (a t) + ζ z (b t) := by
  let η : S →ₗ[k] (T →ₗ[k] k) :=
    { toFun := fun z => ψ z - (ζ z).comp b
      map_add' := by intros; ext; simp; abel
      map_smul' := by intros; ext; simp [smul_sub] }
  obtain ⟨γ, hγ⟩ := family_factors_of_ker a ha η (by
    intro z t ht
    change ψ z t - ζ z (b t) = 0
    rw [hlift z t ht, sub_self])
  refine ⟨γ, fun z t => ?_⟩
  have h := hγ z t
  change ψ z t - ζ z (b t) = γ z (a t) at h
  exact (sub_eq_iff_eq_add).mp h

/-- Evaluating the single parent factor on any child embedding gives the
child restriction formula. The same `γ` works for every child, so its choice
cannot depend on the fresh orientation subsequently sampled at that child. -/
theorem common_child_factorization
    {ι P : Type*} [AddCommGroup P] [Module k P]
    (a : T →ₗ[k] X) (b : T →ₗ[k] B) (ha : Function.Surjective a)
    (ψ : S →ₗ[k] (T →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z t, a t = 0 → ψ z t = ζ z (b t))
    (child : ι → P →ₗ[k] T) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k),
      ∀ i z p, ψ z (child i p) = γ z (a (child i p)) + ζ z (b (child i p)) := by
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha ψ ζ hlift
  exact ⟨γ, fun i z p => hγ z (child i p)⟩

/-- For a surjective aggregate, its first coordinate is surjective. -/
theorem aggregate_fst_surjective (A : T →ₗ[k] X × B)
    (hA : Function.Surjective A) :
    Function.Surjective ((LinearMap.fst k X B).comp A) := by
  intro x
  obtain ⟨t, ht⟩ := hA (x, 0)
  exact ⟨t, congrArg Prod.fst ht⟩

end

/-!
# Every parent lift has one common map before the child is selected

This specializes the kernel factorization to the actual product construction.
It derives the child logical characters from a parent lift; it does not assume
independence of the lift and an incoming orientation.
-/

section

open scoped BigOperators

variable {k I P R X B S : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]
variable [AddCommGroup S] [Module k S]

/-- Inclusion of all child shifts before imposing the parent kernel condition. -/
def tupleEmbed (e : R →ₗ[k] P) : (I → R) →ₗ[k] (I → P) where
  toFun h i := e (h i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

omit [Fintype I] in
theorem tupleEmbed_single (e : R →ₗ[k] P) (i : I) (h : R) :
    tupleEmbed e (Pi.single i h) = Pi.single i (e h) := by
  ext j
  by_cases hij : i = j
  · subst j; simp [tupleEmbed]
  · simp [tupleEmbed, hij]

theorem shiftAggregate_single (J : I → B →ₗ[k] X × B)
    (lam : R →ₗ[k] B) (i : I) (h : R) :
    shiftAggregate J lam (Pi.single i h) = J i (lam h) := by
  classical
  simp [shiftAggregate, aggregate, Pi.single_apply, apply_ite, map_zero]

/-- Actual parent lifts factor through the same aggregate first-coordinate
family on all child shifts. The existential `γ` occurs before both `i` and `h`.
This is the common-parent requirement used before revealing fresh orientation. -/
theorem parent_lift_common_child
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      ψ z (Pi.single i (e h)) =
        γ z (J i (lam h)).1 + ζ z (J i (lam h)).2 := by
  let a := (LinearMap.fst k X B).comp (shiftAggregate J lam)
  let b := (LinearMap.snd k X B).comp (shiftAggregate J lam)
  let Ψ : S →ₗ[k] ((I → R) →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp (tupleEmbed e)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have ha : Function.Surjective a :=
    aggregate_fst_surjective _ (shiftAggregate_surjective J hJ lam hlam)
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha Ψ ζ (by
    intro z h hh
    exact hlift z ⟨h, hh⟩)
  refine ⟨γ, fun i z h => ?_⟩
  have heq := hγ z (Pi.single i h)
  change ψ z (tupleEmbed e (Pi.single i h)) =
    γ z (shiftAggregate J lam (Pi.single i h)).1 +
      ζ z (shiftAggregate J lam (Pi.single i h)).2 at heq
  simpa only [tupleEmbed_single, shiftAggregate_single] using heq

/-- In particular, every child restriction annihilates the child's logical
kernel. This proves that a child logical character exists for every lift. -/
theorem parent_lift_child_kernel
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h))
    (i : I) (z : S) (h : R) (hh : lam h = 0) :
    ψ z (Pi.single i (e h)) = 0 := by
  obtain ⟨γ, hγ⟩ := parent_lift_common_child J hJ e lam hlam ψ ζ hlift
  simpa [hh] using hγ i z h

end

/-!
# Actual lifts and their descendant restrictions

Every descendant lift is constructed by a linear section of the child image.
Its detection on the child noise implies detection by the parent family on
the actual embedded noise. The common parent family is chosen before the
child index; only the image section is chosen after that index is known.
-/

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

/-- A linear lift of a logical character subspace to the actual stage input. -/
structure Lift (s : Stage k B) (S : Submodule k (B →ₗ[k] k)) where
  family : S →ₗ[k] (s.Input →ₗ[k] k)
  agrees : ∀ z h, family z (s.embed h) = z.val (s.logical h)

/-- Restricting a lift preserves its prescribed logical characters. -/
def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

/-- Linear insertion into one physical input coordinate. -/
def singleInput (i : I) (P : Type v) [AddCommGroup P] [Module k P] :
    P →ₗ[k] (I → P) where
  toFun p := Pi.single i p
  map_add' a b := by ext j; by_cases h : i = j <;> simp [h]
  map_smul' c p := by ext j; by_cases h : i = j <;> simp [h]

/-- The logical map of a child, obtained from the common parent first-coordinate
map and the prescribed logical character. -/
def childCharacter (J : I → B →ₗ[k] X × B)
    {S : Submodule k (B →ₗ[k] k)} (γ : S →ₗ[k] (X →ₗ[k] k)) (i : I) :
    S →ₗ[k] (B →ₗ[k] k) where
  toFun z := (γ z).comp ((LinearMap.fst k X B).comp (J i)) +
    z.val.comp ((LinearMap.snd k X B).comp (J i))
  map_add' a b := by ext; simp; abel
  map_smul' c z := by ext; simp [smul_add]

omit [Finite B] in
theorem exists_common_child_character
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      L.family z (Pi.single i (s.embed h)) = childCharacter J γ i z (s.logical h) := by
  have hlift : ∀ z (h : parentShifts J s.logical),
      L.family z (parentEmbed J s.logical s.embed h) =
        z.val (parentLogical J s.logical h) := by
    intro z h
    simpa only [Stage.next] using! L.agrees z h
  have hcommon := parent_lift_common_child (S := S) J hJ s.embed s.logical
    s.logical_surjective
  obtain ⟨γ, hγ⟩ := hcommon L.family S.subtype hlift
  exact ⟨γ, fun i z h => hγ i z h⟩

/-- The descendant family using a section of the actual image. -/
def descendantFamily {s : Stage k B} {S : Submodule k (B →ₗ[k] k)}
    (ψ : S →ₗ[k] ((I → s.Input) →ₗ[k] k)) (i : I)
    (φ : S →ₗ[k] (B →ₗ[k] k))
    (sectionMap : LinearMap.range φ →ₗ[k] S) :
    LinearMap.range φ →ₗ[k] (s.Input →ₗ[k] k) where
  toFun z := (ψ (sectionMap z)).comp (singleInput i s.Input)
  map_add' a b := by ext; simp
  map_smul' c z := by ext; simp

omit [Finite B] in
/-- Every child image carries a genuine child lift. The section is constructed
by ordinary linear algebra and is chosen without any later path or leaf symbol. -/
theorem exists_descendant_lift
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    (γ : S →ₗ[k] (X →ₗ[k] k))
    (hγ : ∀ i z h, L.family z (Pi.single i (s.embed h)) =
      childCharacter J γ i z (s.logical h)) (i : I) :
    ∃ (L' : Lift s (LinearMap.range (childCharacter J γ i)))
      (sectionMap : LinearMap.range (childCharacter J γ i) →ₗ[k] S),
      (∀ z, childCharacter J γ i (sectionMap z) = z.val) ∧
      (∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p)) := by
  let φ : S →ₗ[k] (B →ₗ[k] k) := childCharacter J γ i
  let : Module.Free k (LinearMap.range φ) :=
    Module.Free.of_divisionRing k (LinearMap.range φ)
  let : Module.Projective k (LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    φ.range_rangeRestrict
  have hσ' (z : LinearMap.range φ) : φ (σ z) = z.val :=
    congrArg Subtype.val (congrArg (fun f => f z) hσ)
  let L' : Lift s (LinearMap.range φ) :=
    { family := descendantFamily L.family i φ σ
      agrees := by
        intro z h
        change L.family (σ z) (Pi.single i (s.embed h)) = z.val (s.logical h)
        rw [hγ, hσ'] }
  exact ⟨L', σ, hσ', fun z p => rfl⟩

omit [Finite B] in
/-- Pointwise containment of child detection in parent detection. Repeating
this implication along a path preserves the original family at the root. -/
theorem descendant_detection_implies_parent
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    {S' : Submodule k (B →ₗ[k] k)} (L' : Lift s S')
    (sectionMap : S' →ₗ[k] S) (i : I)
    (hfamily : ∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p))
    (n : s.Noise) (hdetect : ∃ z, L'.family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hdetect
  refine ⟨sectionMap z, ?_⟩
  simpa only [hfamily, Stage.next] using hz

end MaxCutGames.Gadget

/-!
# Fresh finite orientations

The rank is fixed before the fresh isomorphism is sampled.  The finite
counting identities below do not require the subsequent lift to be independent
of that isomorphism.  In particular, an event concerning the oriented subspace
may be tested after arbitrary earlier choices have been fixed.
-/

noncomputable section

open scoped BigOperators
open Module

namespace MaxCutGames.Gadget.Orientation

section FiniteAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in
/-- Right translation of the uniform group element changes the starting point,
but leaves the complete sample sum unchanged. -/
theorem sum_action_eq (x y : X) (h : ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) = ∑ g : G, f (g • y) := by
  obtain ⟨a, rfl⟩ := h
  symm
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun g => by simp [mul_smul])

/-- Cross-multiplied uniform-pushforward identity for a transitive finite action.
This form also handles empty event sets without additional cases. -/
theorem card_mul_sum_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℚ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
        ∑ y : X, ∑ g : G, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_action_eq x y (transitive y) f
    _ = ∑ g : G, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : G, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
    _ = (Fintype.card G : ℚ) * (∑ y : X, f y) := by simp

/-- A uniform group element sends a fixed point to the uniform distribution on
the entire transitive space.  Apply to indicator functions for event bounds. -/
theorem mean_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) / Fintype.card G =
      (∑ y : X, f y) / Fintype.card X := by
  have : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hG hX).2
  simpa [mul_comm] using card_mul_sum_action x transitive f

end FiniteAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

/-- Every two equal-dimensional subspaces are related by an automorphism of
the ambient space.  This supplies actual transitivity, rather than assuming
the desired distribution on the Grassmannian. -/
theorem exists_map_eq_of_finrank_eq (E F : Submodule K V)
    (h : finrank K E = finrank K F) :
    ∃ a : V ≃ₗ[K] V, E.map a.toLinearMap = F := by
  let e : E ≃ₗ[K] F := LinearEquiv.ofFinrankEq E F h
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha ⟨u, hu⟩) ▸ (e ⟨u, hu⟩).property
  · intro hv
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hv⟩
    refine ⟨u, u.property, ?_⟩
    exact (ha u).symm.trans (congrArg Subtype.val hu)

omit [FiniteDimensional K V] in
/-- Rank does not depend on the fresh orientation. -/
theorem rank_map (E : Submodule K V) (a : V ≃ₗ[K] V) :
    finrank K (E.map a.toLinearMap) = finrank K E :=
  a.finrank_map_eq E

/-- The finite Grassmannian at a rank chosen before orientation. -/
def RankSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) :=
  {E : Submodule K V // finrank K E = r}

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

/-- Equal-rank transitivity specialized to the rank-indexed sampling space. -/
theorem rankSpace_transitive {r : ℕ} (E F : RankSpace K V r) :
    ∃ a : V ≃ₗ[K] V, a • E = F := by
  obtain ⟨a, ha⟩ := exists_map_eq_of_finrank_eq E.val F.val
    (E.property.trans F.property.symm)
  exact ⟨a, Subtype.ext ha⟩

/-- The exact uniform law of a fixed-rank subspace under a fresh uniform
linear orientation, with no genericity or independence premise. -/
theorem mean_oriented_subspace {r : ℕ} [Fintype (V ≃ₗ[K] V)]
    [Fintype (RankSpace K V r)] (E : RankSpace K V r) (f : RankSpace K V r → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • E)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ F : RankSpace K V r, f F) / Fintype.card (RankSpace K V r) :=
  mean_action E (rankSpace_transitive E) f

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

/-- Pullback of a fixed character space by an isomorphism preserves rank.
The character space is an argument preceding the newly chosen orientation. -/
theorem rank_dual_pullback (E : Submodule K (Module.Dual K U)) (J : B ≃ₗ[K] U) :
    finrank K (E.map J.dualMap.toLinearMap) = finrank K E :=
  J.dualMap.finrank_map_eq E

/-- Choosing a reference isomorphism identifies all orientations with the
automorphism group of the target. -/
def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

/-- Uniform orientations between two spaces send a fixed character subspace
to the uniform distribution on all subspaces of the same dimension. -/
theorem mean_map_equiv [FiniteDimensional K U] (E : Submodule K B) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype (RankSpace K U (finrank K E))]
    (f : RankSpace K U (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K U (finrank K E), f F) /
        Fintype.card (RankSpace K U (finrank K E)) := by
  let E₀ : RankSpace K U (finrank K E) :=
    ⟨E.map J₀.toLinearMap, J₀.finrank_map_eq E⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • E₀) := by
    apply Fintype.sum_equiv (orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change E.map J.toLinearMap =
      (E.map J₀.toLinearMap).map (J₀.symm.trans J).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [hsum, Fintype.card_congr (orientationEquiv J₀)]
  exact mean_oriented_subspace E₀ f

/-- Dualization is a bijection on finite-dimensional isomorphisms.  This
connects uniform primal orientations to uniform character-space orientations. -/
def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

theorem mean_dual_pullback [FiniteDimensional K B] [FiniteDimensional K U]
    (E : Submodule K (Module.Dual K U)) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)]
    [Fintype (Module.Dual K U ≃ₗ[K] Module.Dual K B)]
    [Fintype (Module.Dual K B ≃ₗ[K] Module.Dual K B)]
    [Fintype (RankSpace K (Module.Dual K B) (finrank K E))]
    (f : RankSpace K (Module.Dual K B) (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K (Module.Dual K B) (finrank K E), f F) /
        Fintype.card (RankSpace K (Module.Dual K B) (finrank K E)) := by
  let e := dualOrientationEquiv (K := K) (B := B) (U := U)
  have hsum := Fintype.sum_equiv e
    (fun J : B ≃ₗ[K] U => f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩)
    (fun J : Module.Dual K U ≃ₗ[K] Module.Dual K B =>
      f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) (fun _ => rfl)
  rw [hsum, Fintype.card_congr e]
  exact mean_map_equiv E J₀.dualMap f

end MaxCutGames.Gadget.Orientation
end

end OAI
