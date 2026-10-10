import Mathlib

namespace OAI

/-! Brauer projection and foundations for blockwise Alperin weights. -/

noncomputable section
namespace BlockwiseAW
abbrev AlgebraicIntegers := integralClosure ℤ ℂ

lemma exists_integer_reduction (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] :
    Nonempty (AlgebraicIntegers →+* k) := by
  let P : Ideal ℤ := RingHom.ker (Int.castRingHom (ZMod p))
  have hsur : Function.Surjective (Int.castRingHom (ZMod p)) := by
    intro x
    exact ⟨x.val, by simp⟩
  have : P.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsur
  have hker : RingHom.ker (algebraMap ℤ AlgebraicIntegers) ≤ P := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (FaithfulSMul.algebraMap_injective ℤ AlgebraicIntegers)]
    exact bot_le
  obtain ⟨Q, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := AlgebraicIntegers) P hker
  have : Q.IsMaximal := hQ
  let P' := Q.comap (algebraMap ℤ AlgebraicIntegers)
  have : P'.IsMaximal := by
    change (Q.under ℤ).IsMaximal
    rw [hQP]
    infer_instance
  let R := ℤ ⧸ P'
  let S := AlgebraicIntegers ⧸ Q
  let : Field R := Ideal.Quotient.field P'
  let : Field S := Ideal.Quotient.field Q
  let : Algebra R S := Ideal.quotientAlgebra
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.quotient
  have : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  let f : R →+* k := Ideal.Quotient.lift P' (Int.castRingHom k) (by
    intro x hx
    change (x : k) = 0
    rw [CharP.intCast_eq_zero_iff k p]
    have hx' : (x : ZMod p) = 0 := by
      change x ∈ P
      rw [← hQP]
      exact hx
    exact (CharP.intCast_eq_zero_iff (ZMod p) p x).mp hx')
  let : Algebra R k := f.toAlgebra
  let lift : S →ₐ[R] k := IsAlgClosed.lift
  exact ⟨lift.toRingHom.comp (Ideal.Quotient.mk Q)⟩

def integerReduction (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] :
    AlgebraicIntegers →+* k :=
  Classical.choice (exists_integer_reduction p k)

section OrbitCancellation
open scoped BigOperators
open MulAction

theorem invariant_sum_eq_fixedPoint_sum
    {p : ℕ} [Fact p.Prime] {P α R : Type*} [Group P] [MulAction P α]
    [Fintype α] [Fintype (fixedPoints P α)] [CommSemiring R] [CharP R p] (hP : IsPGroup p P)
    (f : α → R) (hf : ∀ (g : P) (x : α), f (g • x) = f x) :
    (∑ x : α, f x) = ∑ x : fixedPoints P α, f x.val := by
  classical
  have key (x : α) :
      (∑ y : { y // (Quotient.mk'' y : Quotient (orbitRel P α)) = Quotient.mk'' x }, f y.val) =
        (Fintype.card (orbit P x) : R) * f x := by
    have hval (y : { y // (Quotient.mk'' y : Quotient (orbitRel P α)) = Quotient.mk'' x }) :
        f y.val = f x := by
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp (Quotient.exact' y.property)
      rw [← hg]
      exact hf g x
    simp_rw [hval]
    have hcard : Fintype.card { y // (Quotient.mk'' y : Quotient (orbitRel P α)) = Quotient.mk'' x } =
        Fintype.card (orbit P x) := by
      simp only [Quotient.eq'']; congr
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  calc
    (∑ x : α, f x) = ∑ a : Quotient (orbitRel P α),
        ∑ y : {y // Quotient.mk'' y = a}, f y.val := by
      rw [← Fintype.sum_sigma' (fun (a : Quotient (orbitRel P α)) (y : {y // Quotient.mk'' y = a}) => f y.val)]
      exact (Fintype.sum_equiv (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel P α))) _ _
        (fun _ => rfl)).symm
    _ = ∑ x : fixedPoints P α, f x.val := by
      symm
      refine Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.val)
        (fun _ _ _ => Finset.mem_univ _)
        (fun a₁ _ _ a₂ _ _ h =>
          Subtype.ext (mem_fixedPoints'.mp a₂.property a₁.val (Quotient.exact' h)))
        (fun b => Quotient.inductionOn' b fun b _ hb => by
        obtain ⟨n, hn⟩ := hP.card_orbit b
        rw [Nat.card_eq_fintype_card] at hn
        have hn0 : n = 0 := by
          by_contra hne
          have hp : (p : R) = 0 := CharP.cast_eq_zero R p
          apply hb
          rw [key, hn, Nat.cast_pow, hp, zero_pow hne, zero_mul]
        have hbfix : b ∈ fixedPoints P α :=
          mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rw [hn, hn0, pow_zero])
        refine ⟨⟨b, hbfix⟩, Finset.mem_univ _, ?_, rfl⟩
        simpa [key, hn, hn0] using hb
      ) (fun a _ _ => by
        rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.property]
        simp)

end OrbitCancellation

section GroupAlgebra
variable {R G : Type*} [CommSemiring R] [Group G]

abbrev Center (R G : Type*) [CommSemiring R] [Group G] :=
  Subalgebra.center R (MonoidAlgebra R G)

theorem mem_center_iff_coeff_conj (a : MonoidAlgebra R G) :
    a ∈ Center R G ↔ ∀ g x : G, a.coeff (g * x * g⁻¹) = a.coeff x := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h g x
    have eq := congrArg (fun b : MonoidAlgebra R G => b.coeff (g * x))
      (h (MonoidAlgebra.single g 1))
    simpa using eq.symm
  · intro h b
    induction b using MonoidAlgebra.induction_on with
    | of g =>
      ext x
      simpa [MonoidAlgebra.of_apply, mul_assoc] using (h g (g⁻¹ * x)).symm
    | add b c hb hc => simp only [add_mul, mul_add, hb, hc]
    | smul r b hb => simp only [smul_mul_assoc, mul_smul_comm, hb]

def coefficientRestriction (H : Subgroup G) :
    MonoidAlgebra R G →ₗ[R] MonoidAlgebra R H where
  toFun a := .ofCoeff (a.coeff.comapDomain Subtype.val Subtype.val_injective.injOn)
  map_add' a b := by ext; rfl
  map_smul' r a := by ext; rfl

@[simp] theorem coefficientRestriction_coeff (H : Subgroup G)
    (a : MonoidAlgebra R G) (h : H) :
    (coefficientRestriction H a).coeff h = a.coeff h := rfl

theorem coefficientRestriction_mem_center (H : Subgroup G)
    (a : MonoidAlgebra R G) (ha : a ∈ Center R G) :
    coefficientRestriction H a ∈ Center R H := by
  rw [mem_center_iff_coeff_conj] at ha ⊢
  intro g x
  exact ha g x

def centerRestriction (H : Subgroup G) : Center R G →ₗ[R] Center R H where
  toFun z := ⟨coefficientRestriction H z.val,
    coefficientRestriction_mem_center H z.val z.property⟩
  map_add' _ _ := Subtype.ext (map_add (coefficientRestriction H) _ _)
  map_smul' _ _ := Subtype.ext (map_smul (coefficientRestriction H) _ _)

def classSum [Finite G] (g : G) : Center R G := by
  classical
  refine ⟨.ofCoeff (Finsupp.equivFunOnFinite.symm (fun x => if IsConj g x then 1 else 0)), ?_⟩
  rw [mem_center_iff_coeff_conj]
  intro h x
  change (if IsConj g (h * x * h⁻¹) then (1 : R) else 0) =
    (if IsConj g x then (1 : R) else 0)
  have hc : IsConj x (h * x * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
  have hi : IsConj g (h * x * h⁻¹) ↔ IsConj g x :=
    ⟨fun t => t.trans hc.symm, fun t => t.trans hc⟩
  simp only [hi]

end GroupAlgebra

section BrauerProjection
open scoped BigOperators
variable {R G : Type*} [CommSemiring R] [Group G]

def conjugationInvariants (R : Type*) [CommSemiring R] (Q : Subgroup G) :
    Subalgebra R (MonoidAlgebra R G) :=
  Subalgebra.centralizer R (Set.range (fun q : Q => MonoidAlgebra.single (q : G) (1 : R)))

theorem mem_conjugationInvariants_iff (Q : Subgroup G) (a : MonoidAlgebra R G) :
    a ∈ conjugationInvariants R Q ↔
      ∀ (q : Q) (x : G), a.coeff ((q : G) * x * (q : G)⁻¹) = a.coeff x := by
  rw [conjugationInvariants, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h q x
    have eq := congrArg (fun b : MonoidAlgebra R G => b.coeff ((q : G) * x))
      (h (MonoidAlgebra.single (q : G) 1) ⟨q, rfl⟩)
    simpa using eq.symm
  · rintro h _ ⟨q, rfl⟩
    ext x
    simpa [mul_assoc] using (h q ((q : G)⁻¹ * x)).symm

theorem coeff_mul_sum [Fintype G] (a b : MonoidAlgebra R G) (g : G) :
    (a * b).coeff g = ∑ x : G, a.coeff x * b.coeff (x⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro x
  exact zero_mul _

@[simp] theorem coefficientRestriction_one (H : Subgroup G) :
    coefficientRestriction (R := R) H 1 = 1 := by
  classical
  ext x
  simp [MonoidAlgebra.one_def, Finsupp.single_apply, eq_comm]

variable [Finite G]

theorem coefficientRestriction_mul_of_invariant
    {p : ℕ} [Fact p.Prime] [CharP R p] (Q : Subgroup G) (hQ : IsPGroup p Q)
    (a b : MonoidAlgebra R G) (ha : a ∈ conjugationInvariants R Q)
    (hb : b ∈ conjugationInvariants R Q) :
    coefficientRestriction (Subgroup.centralizer (Q : Set G)) (a * b) =
      coefficientRestriction (Subgroup.centralizer (Q : Set G)) a *
        coefficientRestriction (Subgroup.centralizer (Q : Set G)) b := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : MulAction Q G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp Q.subtype)
  have hfixed : MulAction.fixedPoints Q G = (Subgroup.centralizer (Q : Set G) : Set G) := by
    ext g
    change (g ∈ MulAction.fixedPoints Q G) ↔ g ∈ Subgroup.centralizer (Q : Set G)
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro h q hq
      have hq' := h ⟨q, hq⟩
      change q * g * q⁻¹ = g at hq'
      exact (mul_inv_eq_iff_eq_mul).mp hq'
    · intro h q
      change (q : G) * g * (q : G)⁻¹ = g
      exact (mul_inv_eq_iff_eq_mul).mpr (h q q.property)
  rw [mem_conjugationInvariants_iff] at ha hb
  ext g
  rw [coefficientRestriction_coeff, coeff_mul_sum, coeff_mul_sum]
  simp only [coefficientRestriction_coeff]
  let f : G → R := fun x => a.coeff x * b.coeff (x⁻¹ * (g : G))
  have hf : ∀ (q : Q) (x : G), f (q • x) = f x := by
    intro q x
    have hg : (q : G) * (g : G) * (q : G)⁻¹ = g :=
      (mul_inv_eq_iff_eq_mul).mpr (Subgroup.mem_centralizer_iff.mp g.property q q.property)
    have he : ((q : G) * x * (q : G)⁻¹)⁻¹ * (g : G) =
        (q : G) * (x⁻¹ * (g : G)) * (q : G)⁻¹ := by
      calc
        _ = ((q : G) * x * (q : G)⁻¹)⁻¹ * ((q : G) * (g : G) * (q : G)⁻¹) := by rw [hg]
        _ = _ := by group
    change a.coeff ((q : G) * x * (q : G)⁻¹) *
      b.coeff (((q : G) * x * (q : G)⁻¹)⁻¹ * (g : G)) = f x
    rw [ha q x, he, hb q (x⁻¹ * (g : G))]
  have hs := invariant_sum_eq_fixedPoint_sum hQ f hf
  change (∑ x : G, f x) = ∑ x : Subgroup.centralizer (Q : Set G), f x.val
  rw [hs]
  exact (Fintype.sum_equiv (Set.equivOfEq hfixed) _ _ (fun _ => rfl))

def brauerHom {p : ℕ} [Fact p.Prime] [CharP R p]
    (Q : Subgroup G) (hQ : IsPGroup p Q) :
    conjugationInvariants R Q →ₐ[R] MonoidAlgebra R (Subgroup.centralizer (Q : Set G)) where
  toFun a := coefficientRestriction (Subgroup.centralizer (Q : Set G)) a.val
  map_zero' := map_zero _
  map_one' := coefficientRestriction_one _
  map_add' a b := map_add _ a.val b.val
  map_mul' a b := coefficientRestriction_mul_of_invariant Q hQ a.val b.val a.property b.property
  commutes' r := by
    change coefficientRestriction _ (algebraMap R (MonoidAlgebra R G) r) = _
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, coefficientRestriction_one]

end BrauerProjection

theorem finite_simple_quotients {R M ι : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    [∀ i, IsSimpleModule R (S i)]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j)
    (hM : IsFiniteLength R M) :
    Set.Finite {i | ∃ f : M →ₗ[R] S i, f ≠ 0} := by
  classical
  induction hM with
  | of_subsingleton =>
    convert Set.finite_empty (α := ι) using 1
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_not]
    intro f
    ext x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  | @of_simple_quotient M _ _ N _ hN ih =>
    have hsimple : Set.Subsingleton {i | Nonempty ((M ⧸ N) ≃ₗ[R] S i)} := by
      rintro i ⟨e⟩ j ⟨f⟩
      exact hS i j ⟨e.symm.trans f⟩
    refine (ih.union hsimple.finite).subset ?_
    rintro i ⟨f, hf⟩
    by_cases hn : f.comp N.subtype = 0
    · right
      have hker : N ≤ LinearMap.ker f := by
        intro x hx
        have hh := congrArg (fun g : N →ₗ[R] S i => g ⟨x, hx⟩) hn
        exact hh
      let g : (M ⧸ N) →ₗ[R] S i := N.liftQ f hker
      have hg : g ≠ 0 := by
        intro hg0
        apply hf
        ext x
        exact congrArg (fun t : (M ⧸ N) →ₗ[R] S i => t (N.mkQ x)) hg0
      exact ⟨LinearEquiv.ofBijective g ((LinearMap.bijective_or_eq_zero g).resolve_right hg)⟩
    · exact Or.inl ⟨f.comp N.subtype, hn⟩

section Blocks
variable (k G : Type*) [Field k] [Group G]

structure Block where
  idempotent : Center k G
  isIdempotent : idempotent * idempotent = idempotent
  nonzero : idempotent ≠ 0
  primitive : ∀ c : Center k G, c * c = c → c * idempotent = c →
    c = 0 ∨ c = idempotent

structure SimpleRepresentation where
  dim : ℕ
  representation : Representation k G (Fin dim → k)
  irreducible : representation.IsIrreducible

variable {k G}

theorem irreducible_moduleFinite {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.Finite k V := by
  have : Module.Finite (MonoidAlgebra k G) ρ.asModule := inferInstance
  have : Module.Finite k ρ.asModule := Module.Finite.trans (MonoidAlgebra k G) ρ.asModule
  exact Module.Finite.equiv ρ.asModuleEquiv

theorem exists_coordinate_simple {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ S : SimpleRepresentation k G, Nonempty (Representation.Equiv ρ S.representation) := by
  let : Module.Finite k V := irreducible_moduleFinite ρ
  let n := Module.finrank k V
  let e : V ≃ₗ[k] (Fin n → k) := (Module.finBasis k V).equivFun
  let σ : Representation k G (Fin n → k) := e.conjRingEquiv.toMonoidHom.comp ρ
  let E : Representation.Equiv ρ σ := Representation.Equiv.mk e (by
    intro g
    ext x
    simp [σ, LinearEquiv.conjRingEquiv])
  let f : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ σ E.toIntertwiningMap
  have hσ : σ.IsIrreducible := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact (f.isSimpleModule_iff_of_bijective e.bijective).mp inferInstance
  exact ⟨⟨n, σ, hσ⟩, ⟨E⟩⟩

def SimpleRepresentation.BelongsTo (V : SimpleRepresentation k G) (B : Block k G) : Prop :=
  V.representation.asAlgebraHom B.idempotent.val = 1

def simpleModuleSetoid (B : Block k G) :
    Setoid {V : SimpleRepresentation k G // V.BelongsTo B} where
  r V W := Nonempty (Representation.Equiv V.val.representation W.val.representation)
  iseqv := by
    constructor
    · intro V; exact ⟨Representation.Equiv.refl _⟩
    · rintro V W ⟨e⟩; exact ⟨e.symm⟩
    · rintro U V W ⟨e⟩ ⟨f⟩; exact ⟨e.trans f⟩

def SimpleModuleClasses (B : Block k G) := Quotient (simpleModuleSetoid B)

instance finiteSimpleModuleClasses {k G : Type*} [Field k] [Group G] [Finite G]
    (B : Block k G) : Finite (SimpleModuleClasses B) := by
  classical
  let R := MonoidAlgebra k G
  let V (q : SimpleModuleClasses B) := (Quotient.out q).val
  let S (q : SimpleModuleClasses B) := (V q).representation.asModule
  let (q : SimpleModuleClasses B) : (V q).representation.IsIrreducible := (V q).irreducible
  let (q : SimpleModuleClasses B) : IsSimpleModule R (S q) := inferInstance
  have hS (q t : SimpleModuleClasses B) (h : Nonempty (S q ≃ₗ[R] S t)) : q = t := by
    obtain ⟨e⟩ := h
    let f := (Representation.IntertwiningMap.equivLinearMapAsModule
      (V q).representation (V t).representation).symm e.toLinearMap
    have hf : Function.Bijective f := e.bijective
    have hrel : (simpleModuleSetoid B).r (Quotient.out q) (Quotient.out t) :=
      ⟨f.ofBijective hf⟩
    exact (Quotient.out_eq q).symm.trans ((Quotient.sound hrel).trans (Quotient.out_eq t))
  have hNoeth : IsNoetherian R R := isNoetherian_of_tower k (inferInstance : IsNoetherian k R)
  have hArtin : IsArtinian R R := isArtinian_of_tower k (inferInstance : IsArtinian k R)
  have hfinite := finite_simple_quotients S hS
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hNoeth, hArtin⟩)
  apply Finite.of_finite_univ
  apply hfinite.subset
  intro q _
  have : Nontrivial (S q) := IsSimpleModule.nontrivial R (S q)
  obtain ⟨x, hx⟩ := exists_ne (0 : S q)
  refine ⟨LinearMap.toSpanSingleton R (S q) x, ?_⟩
  intro hzero
  apply hx
  simpa using congrArg (fun f : R →ₗ[R] S q => f 1) hzero

def l (B : Block k G) : ℕ := Nat.card (SimpleModuleClasses B)

def IsCentralCharacter (B : Block k G) (lam : Center k G →ₐ[k] k) : Prop :=
  ∀ V : SimpleRepresentation k G, V.BelongsTo B → ∀ z : Center k G,
    V.representation.asAlgebraHom z.val =
      algebraMap k (Module.End k (Fin V.dim → k)) (lam z)

end Blocks

def OrdinaryCharacter (G : Type*) [Group G] :=
  {χ : G → ℂ // ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    ρ.IsIrreducible ∧ ρ.character = χ}

namespace OrdinaryCharacter
variable {G : Type*} [Group G]

def degree (χ : OrdinaryCharacter G) : ℕ := χ.property.choose

def affording (χ : OrdinaryCharacter G) : Representation ℂ G (Fin χ.degree → ℂ) :=
  χ.property.choose_spec.choose

instance affording_irreducible (χ : OrdinaryCharacter G) : χ.affording.IsIrreducible :=
  χ.property.choose_spec.choose_spec.left

@[simp] theorem affording_character (χ : OrdinaryCharacter G) : χ.affording.character = χ.val :=
  χ.property.choose_spec.choose_spec.right

theorem apply_conj (χ : OrdinaryCharacter G) (g x : G) :
    χ.val (g * x * g⁻¹) = χ.val x := by
  rw [← χ.affording_character]
  exact Representation.char_conj χ.affording x g

theorem degree_spec (χ : OrdinaryCharacter G) : χ.val 1 = (χ.degree : ℂ) := by
  obtain ⟨ρ, -, hρ⟩ := χ.property.choose_spec
  rw [← hρ, Representation.char_one]
  simp [degree]

theorem degree_pos (χ : OrdinaryCharacter G) : 0 < χ.degree := by
  have : Nontrivial χ.affording.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
  have : Nontrivial (Fin χ.degree → ℂ) := χ.affording.asModuleEquiv.symm.toEquiv.nontrivial
  simpa using Module.finrank_pos (R := ℂ) (M := Fin χ.degree → ℂ)

open scoped Classical in

theorem orthogonality [Fintype G] (χ ψ : OrdinaryCharacter G) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, χ.val g * ψ.val g⁻¹ = if χ = ψ then 1 else 0 := by
  classical
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have he : Nonempty (Representation.Equiv ψ.affording χ.affording) ↔ χ = ψ := by
    constructor
    · rintro ⟨e⟩
      apply Subtype.ext
      simpa using (Representation.char_iso e).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa [he] using Representation.char_orthonormal χ.affording ψ.affording

theorem linearIndependent [Finite G] :
    LinearIndependent ℂ (fun χ : OrdinaryCharacter G => χ.val) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let pair (ψ : OrdinaryCharacter G) : (G → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => (Nat.card G : ℂ)⁻¹ * ∑ g : G, f g * ψ.val g⁻¹
      map_add' := fun f g => by simp [add_mul, Finset.sum_add_distrib, mul_add]
      map_smul' := fun c f => by
        simp [Finset.mul_sum, mul_left_comm, mul_assoc] }
  have hpair (χ ψ : OrdinaryCharacter G) : pair ψ χ.val = if χ = ψ then 1 else 0 :=
    orthogonality χ ψ
  refine linearIndependent_iff'.mpr ?_
  intro s c hs χ hχ
  have h := congrArg (pair χ) hs
  simpa [map_sum, map_smul, hpair, ← Finset.mul_sum, hχ] using h

instance finite [Finite G] : Finite (OrdinaryCharacter G) := linearIndependent.finite

end OrdinaryCharacter

def pPart (p n : ℕ) : ℕ := p ^ n.factorization p

abbrev Normalizer {G : Type*} [Group G] (Q : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (Q : Set G)

abbrev NormalizerQuotient {G : Type*} [Group G] (Q : Subgroup G) :=
  (Normalizer Q) ⧸ Q.subgroupOf (Normalizer Q)

structure Weight (p : ℕ) (G : Type*) [Group G] where
  subgroup : Subgroup G
  isPSubgroup : IsPGroup p subgroup
  character : OrdinaryCharacter (NormalizerQuotient subgroup)
  defectZero : pPart p character.degree = pPart p (Nat.card (NormalizerQuotient subgroup))

namespace Weight
variable {p : ℕ} {G : Type*} [Group G]

def inflatedCharacter (w : Weight p G) (h : (Normalizer w.subgroup)) : ℂ :=
  w.character.val (QuotientGroup.mk' (w.subgroup.subgroupOf (Normalizer w.subgroup)) h)

def extendedCharacter (w : Weight p G) (g : G) : ℂ := by
  classical
  exact if h : g ∈ (Normalizer w.subgroup) then w.inflatedCharacter ⟨g, h⟩ else 0

def IsConjugate (w v : Weight p G) : Prop :=
  ∃ g : G,
    (∀ x : G, x ∈ w.subgroup ↔ g * x * g⁻¹ ∈ v.subgroup) ∧
    (∀ x : G, w.extendedCharacter x = v.extendedCharacter (g * x * g⁻¹))

theorem isConjugate_refl (w : Weight p G) : w.IsConjugate w := by
  refine ⟨1, ?_, ?_⟩ <;> simp

theorem isConjugate_symm {w v : Weight p G} (hwv : w.IsConjugate v) :
    v.IsConjugate w := by
  obtain ⟨g, hQ, hχ⟩ := hwv
  refine ⟨g⁻¹, ?_, ?_⟩
  · intro x
    simpa [mul_assoc] using (hQ (g⁻¹ * x * g)).symm
  · intro x
    simpa [mul_assoc] using (hχ (g⁻¹ * x * g)).symm

theorem isConjugate_trans {w v u : Weight p G}
    (hwv : w.IsConjugate v) (hvu : v.IsConjugate u) : w.IsConjugate u := by
  obtain ⟨g, hQ, hχ⟩ := hwv
  obtain ⟨h, hR, hψ⟩ := hvu
  refine ⟨h * g, ?_, ?_⟩
  · intro x
    simpa [mul_assoc] using (hQ x).trans (hR (g * x * g⁻¹))
  · intro x
    simpa [mul_assoc] using (hχ x).trans (hψ (g * x * g⁻¹))

instance finite [Finite G] : Finite (Weight p G) := by
  let f : Weight p G → Σ Q : Subgroup G, OrdinaryCharacter (NormalizerQuotient Q) :=
    fun w => ⟨w.subgroup, w.character⟩
  apply Finite.of_injective f
  rintro ⟨Q, hQ, χ, hχ⟩ ⟨Q', hQ', χ', hχ'⟩ h
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq he
  rfl

def conjugacySetoid (p : ℕ) (G : Type*) [Group G] : Setoid (Weight p G) where
  r := IsConjugate
  iseqv := ⟨isConjugate_refl, isConjugate_symm, isConjugate_trans⟩

end Weight

section BlockAssignment
variable {k G : Type*} [Field k] [Group G] [Finite G]

def IsOrdinaryReduction (r : AlgebraicIntegers →+* k) (χ : G → ℂ)
    (lam : Center k G →ₐ[k] k) : Prop :=
  ∀ g : G, ∃ a : AlgebraicIntegers,
    (a : ℂ) = (Nat.card {x : G // IsConj g x} : ℂ) * χ g / χ 1 ∧
    lam (classSum g) = r a

def AssignedTo (r : AlgebraicIntegers →+* k) {p : ℕ}
    (w : Weight p G) (B : Block k G) : Prop :=
  ∃ b : Block k (Normalizer w.subgroup),
    ∃ lam_b : Center k (Normalizer w.subgroup) →ₐ[k] k,
    ∃ lam_B : Center k G →ₐ[k] k,
      IsCentralCharacter b lam_b ∧ IsCentralCharacter B lam_B ∧
      IsOrdinaryReduction r w.inflatedCharacter lam_b ∧
      (∀ z : Center k G, lam_b (centerRestriction (Normalizer w.subgroup) z) = lam_B z)

def W (p : ℕ) [Fact p.Prime] [IsAlgClosed k] [CharP k p] (B : Block k G) :=
  Quotient ((Weight.conjugacySetoid p G).comap
    (fun w : {w : Weight p G // AssignedTo (integerReduction p k) w B} => w.val))

instance finiteW (p : ℕ) [Fact p.Prime] [IsAlgClosed k] [CharP k p] (B : Block k G) :
    Finite (W p B) := by
  unfold W
  infer_instance

end BlockAssignment

end BlockwiseAW

end

end OAI
