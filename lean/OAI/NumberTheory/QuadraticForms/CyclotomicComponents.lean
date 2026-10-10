import Mathlib
import OAI.NumberTheory.QuadraticForms.LocalTrace

namespace OAI

/-! Cyclotomic operator components and nondegenerate forms. -/



namespace MultiplicityCounterexample.PolynomialComponentRestriction
noncomputable section
open TensorProduct Polynomial
open LinearMap (BilinForm)
variable {R A V W : Type*} [Field R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

lemma range_baseChange (f : Module.End R V) :
    (LinearMap.range f).baseChange A = LinearMap.range (f.baseChange A) := by
  have hf : (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f := rfl
  rw [Submodule.baseChange, ← hf, LinearMap.baseChange_comp]
  exact (LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective A f.surjective_rangeRestrict))).symm

def rangeBaseChangeEquiv (f : Module.End R V) :
    (A ⊗[R] LinearMap.range f) ≃ₗ[A] LinearMap.range (f.baseChange A) :=
  (Submodule.toBaseChange.toLinearEquiv A (LinearMap.range f)).trans
    (LinearEquiv.ofEq _ _ (range_baseChange f))

lemma rangeBaseChangeEquiv_coe (f : Module.End R V) (x : A ⊗[R] LinearMap.range f) :
    (rangeBaseChangeEquiv (A := A) f x : A ⊗[R] V) =
      (LinearMap.range f).subtype.baseChange A x := rfl

lemma map_ranges (f : Module.End R V) (g : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (f.baseChange A x) = g.baseChange A (e x)) :
    (LinearMap.range (f.baseChange A)).map e.toLinearMap =
      LinearMap.range (g.baseChange A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
    exact ⟨e v, (he v).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨f.baseChange A (e.symm w), ⟨e.symm w, rfl⟩, ?_⟩
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using he (e.symm w)

def restrictRangeEquiv (f : Module.End R V) (g : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (f.baseChange A x) = g.baseChange A (e x)) :
    (A ⊗[R] LinearMap.range f) ≃ₗ[A] (A ⊗[R] LinearMap.range g) :=
  (rangeBaseChangeEquiv f).trans
    ((e.ofSubmodules _ _ (map_ranges f g e he)).trans (rangeBaseChangeEquiv g).symm)

lemma restrictRangeEquiv_subtype (f : Module.End R V) (g : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (f.baseChange A x) = g.baseChange A (e x))
    (x : A ⊗[R] LinearMap.range f) :
    (LinearMap.range g).subtype.baseChange A (restrictRangeEquiv f g e he x) =
      e ((LinearMap.range f).subtype.baseChange A x) := by
  rw [← rangeBaseChangeEquiv_coe, ← rangeBaseChangeEquiv_coe]
  change ((rangeBaseChangeEquiv g)
    ((rangeBaseChangeEquiv g).symm ((e.ofSubmodules _ _ (map_ranges f g e he))
      (rangeBaseChangeEquiv f x))) : A ⊗[R] W) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma restrictForm_baseChange (B : BilinForm R V) (P : Submodule R V)
    (x y : A ⊗[R] P) :
    B.baseChange A (P.subtype.baseChange A x) (P.subtype.baseChange A y) =
      (B.restrict P).baseChange A x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b y => rfl

theorem restrictRangeEquiv_preserves
    (f : Module.End R V) (g : Module.End R W)
    (B₁ : BilinForm R V) (B₂ : BilinForm R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (f.baseChange A x) = g.baseChange A (e x))
    (hB : ∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y)
    (x y : A ⊗[R] LinearMap.range f) :
    (B₂.restrict (LinearMap.range g)).baseChange A
      (restrictRangeEquiv f g e he x) (restrictRangeEquiv f g e he y) =
      (B₁.restrict (LinearMap.range f)).baseChange A x y := by
  rw [← restrictForm_baseChange, ← restrictForm_baseChange,
    restrictRangeEquiv_subtype, restrictRangeEquiv_subtype, hB]

end
end MultiplicityCounterexample.PolynomialComponentRestriction

namespace MultiplicityCounterexample.CyclicComponent
noncomputable section
open Polynomial
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
lemma commute_eval (T : Module.End F V) (p : F[X]) : Commute T (aeval T p) := by
  simpa only [aeval_X] using (Commute.all X p).map (aeval T)
abbrev component (T : Module.End F V) (p : F[X]) := LinearMap.range (aeval T p)
def componentOperator (T : Module.End F V) (p : F[X]) :
    Module.End F (component T p) := T.restrict (by
  intro x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨T y,?_⟩
  exact (congrArg (fun f : Module.End F V => f y) (commute_eval T p).eq).symm)
lemma componentOperator_coe (T : Module.End F V) (p : F[X]) (x : component T p) :
    (componentOperator T p x : V)=T x := rfl
end
end MultiplicityCounterexample.CyclicComponent

namespace MultiplicityCounterexample.PolynomialComponentRestriction
noncomputable section
open TensorProduct Polynomial CyclicComponent
open LinearMap (BilinForm)
variable {R A V W : Type*} [Field R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

lemma intertwines_pow (T : Module.End R V) (U : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x)) (n : ℕ) (x) :
    e ((T ^ n).baseChange A x) = (U ^ n).baseChange A (e x) := by
  simp only [LinearMap.baseChange_pow]
  induction n with
  | zero => rfl
  | succ n hn =>
    simp only [pow_succ', Module.End.mul_apply, he, hn]

lemma intertwines_aeval (T : Module.End R V) (U : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x)) (p : R[X]) (x) :
    e ((aeval T p).baseChange A x) = (aeval U p).baseChange A (e x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.baseChange_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, ← Algebra.smul_def, LinearMap.baseChange_smul,
      LinearMap.smul_apply]
    have hsm (v : A ⊗[R] V) : e (a • v) = a • e v :=
      (e.restrictScalars R).map_smul a v
    rw [hsm, intertwines_pow T U e he]

def restrictComponentEquiv (T : Module.End R V) (U : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x)) (p : R[X]) :
    (A ⊗[R] component T p) ≃ₗ[A] (A ⊗[R] component U p) :=
  restrictRangeEquiv _ _ e (intertwines_aeval T U e he p)

lemma componentOperator_baseChange_coe (T : Module.End R V) (p : R[X])
    (x : A ⊗[R] component T p) :
    (component T p).subtype.baseChange A ((componentOperator T p).baseChange A x) =
      T.baseChange A ((component T p).subtype.baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem restrictComponentEquiv_intertwines (T : Module.End R V) (U : Module.End R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x)) (p : R[X])
    (x : A ⊗[R] component T p) :
    restrictComponentEquiv T U e he p ((componentOperator T p).baseChange A x) =
      (componentOperator U p).baseChange A (restrictComponentEquiv T U e he p x) := by
  apply (rangeBaseChangeEquiv (aeval U p)).injective
  apply Subtype.val_injective
  change (component U p).subtype.baseChange A
      (restrictComponentEquiv T U e he p ((componentOperator T p).baseChange A x)) =
    (component U p).subtype.baseChange A
      ((componentOperator U p).baseChange A (restrictComponentEquiv T U e he p x))
  rw [componentOperator_baseChange_coe]
  simp only [restrictComponentEquiv, restrictRangeEquiv_subtype]
  rw [componentOperator_baseChange_coe, he]

theorem component_local_datum (T : Module.End R V) (U : Module.End R W)
    (B₁ : BilinForm R V) (B₂ : BilinForm R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x))
    (hB : ∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y)
    (p : R[X]) :
    ∃ c : (A ⊗[R] component T p) ≃ₗ[A] (A ⊗[R] component U p),
      (∀ x, c ((componentOperator T p).baseChange A x) =
        (componentOperator U p).baseChange A (c x)) ∧
      (∀ x y, (B₂.restrict (component U p)).baseChange A (c x) (c y) =
        (B₁.restrict (component T p)).baseChange A x y) := by
  refine ⟨restrictComponentEquiv T U e he p,
    restrictComponentEquiv_intertwines T U e he p, ?_⟩
  exact restrictRangeEquiv_preserves _ _ B₁ B₂ e (intertwines_aeval T U e he p) hB
end
end MultiplicityCounterexample.PolynomialComponentRestriction

namespace MultiplicityCounterexample.CyclicComponent
noncomputable section
open Polynomial
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
def action (T : Module.End F V) (f : F[X]) (hf : aeval T f=0) :
    AdjoinRoot f →ₐ[F] Module.End F V where
  toRingHom := Ideal.Quotient.lift _ (aeval T).toRingHom (by
    intro q hq
    obtain ⟨r,rfl⟩ := Ideal.mem_span_singleton.mp hq
    change aeval T (f*r)=0
    rw [map_mul,hf,zero_mul])
  commutes' a := by
    change aeval T (C a)=algebraMap F (Module.End F V) a
    exact aeval_C T a

abbrev scalarModule (T : Module.End F V) (f : F[X]) (hf : aeval T f=0) :
    Module (AdjoinRoot f) V := Module.compHom V (action T f hf).toRingHom

instance scalarTower (T : Module.End F V) (f : F[X]) (hf : aeval T f=0) :
    letI := scalarModule T f hf
    IsScalarTower F (AdjoinRoot f) V := by
  let := scalarModule T f hf
  constructor
  intro a z x
  change (action T f hf (a • z)) x=a • (action T f hf z) x
  rw [map_smul]
  rfl

lemma root_smul (T : Module.End F V) (f : F[X]) (hf : aeval T f=0) (x : V) :
    letI := scalarModule T f hf
    AdjoinRoot.root f • x=T x := by
  change (aeval T X) x=T x
  rw [aeval_X]

lemma eval_componentOperator (T : Module.End F V) (p q : F[X]) (x : component T p) :
    ((aeval (componentOperator T p) q) x : V)=(aeval T q) x := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add,LinearMap.add_apply,Submodule.coe_add,hq,hr]
  | monomial n a =>
    rw [aeval_monomial,aeval_monomial,← Algebra.smul_def,← Algebra.smul_def]
    change a • (((componentOperator T p)^n) x : V)=a • (T^n) x
    congr 1
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply]
      change T ((((componentOperator T p)^n) x : component T p) : V)=T ((T^n) x)
      rw [hn]

lemma component_annihilated (T : Module.End F V) (p f : F[X])
    (h : aeval T (f*p)=0) : aeval (componentOperator T p) f=0 := by
  ext x
  rw [eval_componentOperator]
  obtain ⟨y,hy⟩ := x.property
  change (aeval T f) (x : V)=0
  rw [← hy,← Module.End.mul_apply,← map_mul,h]
  rfl

@[instance_reducible] def componentScalarModule {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (p f : F[X]) (h : aeval T (f*p)=0) :
    Module (AdjoinRoot f) (component T p) :=
  scalarModule (componentOperator T p) f (component_annihilated T p f h)

end
end MultiplicityCounterexample.CyclicComponent

namespace MultiplicityCounterexample.ComponentRootLocalComparison
noncomputable section
open TensorProduct Polynomial CyclicComponent PolynomialComponentRestriction TensorAlgebraModule
open LinearMap (BilinForm)
variable {R A V W : Type*} [Field R] [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

lemma rightAction_root (T : Module.End R V) (p f : R[X])
    (hf : aeval T (f * p) = 0) :
    letI := componentScalarModule T p f hf
    rightAction (A := A) (V := component T p) (AdjoinRoot.root f) =
      (componentOperator T p).baseChange A := by
  let := componentScalarModule T p f hf
  have hr : Algebra.lsmul R R (component T p) (AdjoinRoot.root f) = componentOperator T p := by
    ext x
    exact congrArg Subtype.val (root_smul (componentOperator T p) f
      (component_annihilated T p f hf) x)
  change (Algebra.lsmul R R (component T p) (AdjoinRoot.root f)).baseChange A = _
  rw [hr]

theorem component_root_local_datum (T : Module.End R V) (U : Module.End R W)
    (B₁ : BilinForm R V) (B₂ : BilinForm R W)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (he : ∀ x, e (T.baseChange A x) = U.baseChange A (e x))
    (hB : ∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y)
    (p f : R[X]) (hfT : aeval T (f * p) = 0) (hfU : aeval U (f * p) = 0) :
    letI := componentScalarModule T p f hfT
    letI := componentScalarModule U p f hfU
    ∃ c : (A ⊗[R] component T p) ≃ₗ[A] (A ⊗[R] component U p),
      (∀ x, c (rightAction (AdjoinRoot.root f) x) = rightAction (AdjoinRoot.root f) (c x)) ∧
      (∀ x y, (B₂.restrict (component U p)).baseChange A (c x) (c y) =
        (B₁.restrict (component T p)).baseChange A x y) := by
  let := componentScalarModule T p f hfT
  let := componentScalarModule U p f hfU
  simpa only [rightAction_root] using component_local_datum T U B₁ B₂ e he hB p
end
end MultiplicityCounterexample.ComponentRootLocalComparison

namespace MultiplicityCounterexample.RealCyclotomicField
noncomputable section
open NumberField Polynomial Algebra
variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

def realGeneratorField (z : E) : IntermediateField ℚ E :=
  IntermediateField.adjoin ℚ ({z + z⁻¹} : Set E)

lemma realGeneratorField_le_maximalReal (z : E)
    (hz : IsCMField.complexConj E z = z⁻¹) :
    (realGeneratorField z).toSubfield ≤ maximalRealSubfield E := by
  let M : IntermediateField ℚ E := (maximalRealSubfield E).toIntermediateField
    (fun a => by simp)
  change realGeneratorField z ≤ M
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change z + z⁻¹ ∈ maximalRealSubfield E
  rw [← IsCMField.complexConj_eq_self_iff, map_add, map_inv₀, hz, inv_inv, add_comm]

omit [IsCMField E] in
lemma realGeneratorField_finrank_le_two (z : E) (hz0 : z ≠ 0)
    (hgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤) :
    Module.finrank (realGeneratorField z) E ≤ 2 := by
  let F := realGeneratorField z
  have hgen' : IntermediateField.adjoin ℚ ({z} : Set E) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    simpa only [IntermediateField.adjoin_toSubalgebra, IntermediateField.top_toSubalgebra] using hgen
  have hgenF : IntermediateField.adjoin F ({z} : Set E) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ hgen'
  have hd := (Field.primitive_element_iff_minpoly_natDegree_eq F z).mp hgenF
  let a : F := ⟨z + z⁻¹, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
  let q : F[X] := X ^ 2 - C a * X + 1
  have hq : aeval z q = 0 := by
    simp only [q, map_add, map_sub, map_pow, aeval_X, map_mul, aeval_C, map_one]
    change z ^ 2 - (z + z⁻¹) * z + 1 = 0
    field_simp
    ring
  have hqne : q ≠ 0 := by
    intro h
    have hc := congrArg (fun p : F[X] => p.coeff 2) h
    norm_num [q, coeff_X_pow, coeff_one] at hc
  have hqdeg : q.natDegree ≤ 2 := by
    dsimp [q]
    compute_degree!
  rw [← hd]
  exact (natDegree_le_of_dvd (minpoly.dvd F z hq) hqne).trans hqdeg

theorem realGeneratorField_eq_maximalReal (z : E) (hz0 : z ≠ 0)
    (hgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (hz : IsCMField.complexConj E z = z⁻¹)
    (hnreal : IsCMField.complexConj E z ≠ z) :
    (realGeneratorField z).toSubfield = maximalRealSubfield E := by
  let F := realGeneratorField z
  have hle := realGeneratorField_le_maximalReal z hz
  let : IsTotallyReal F := isTotallyReal_iff_le_maximalRealSubfield.mpr hle
  have hle2 := realGeneratorField_finrank_le_two z hz0 hgen
  have hne1 : Module.finrank F E ≠ 1 := by
    intro h
    have ht : F = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp h
    have hzF : z ∈ F := ht ▸ Set.mem_univ z
    exact hnreal ((IsCMField.complexConj_eq_self_iff E z).mpr (hle hzF))
  have hp : 0 < Module.finrank F E := Module.finrank_pos
  let : IsQuadraticExtension F E := ⟨by change Module.finrank F E ≤ 2 at hle2; omega⟩
  let : IsQuadraticExtension F.toSubfield E := ⟨by
    change Module.finrank F E = 2
    exact IsQuadraticExtension.finrank_eq_two F E⟩
  exact CMExtension.eq_maximalRealSubfield E F.toSubfield
end
end MultiplicityCounterexample.RealCyclotomicField

namespace MultiplicityCounterexample.CyclotomicQuotient
noncomputable section
open Polynomial
variable (d : ℕ) [NeZero d]

instance cycloIrred : Fact (Irreducible (cyclotomic d ℚ)) :=
  ⟨cyclotomic.irreducible_rat (NeZero.pos d)⟩

abbrev E := AdjoinRoot (cyclotomic d ℚ)

instance finite : FiniteDimensional ℚ (E d) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (cyclotomic.irreducible_rat (NeZero.pos d)).ne_zero).basis

instance numberField : NumberField (E d) where

lemma root_primitive : IsPrimitiveRoot (AdjoinRoot.root (cyclotomic d ℚ)) d := by
  apply (isRoot_cyclotomic_iff_charZero (NeZero.pos d)).mp
  rw [IsRoot,← map_cyclotomic d (algebraMap ℚ (E d)),← eval₂_eq_eval_map]
  exact AdjoinRoot.eval₂_root (cyclotomic d ℚ)

instance cyclotomic : IsCyclotomicExtension {d} ℚ (E d) := by
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨_,root_primitive d⟩,?_⟩
  intro x
  have h : Algebra.adjoin ℚ ({AdjoinRoot.root (Polynomial.cyclotomic d ℚ)} : Set (E d)) ≤
      Algebra.adjoin ℚ {b : E d | b^d=1} := by
    apply Algebra.adjoin_mono
    intro z hz
    have hz' : z=AdjoinRoot.root (Polynomial.cyclotomic d ℚ) := Set.mem_singleton_iff.mp hz
    rw [hz']
    exact (root_primitive d).pow_eq_one
  have htop : Algebra.adjoin ℚ ({AdjoinRoot.root (Polynomial.cyclotomic d ℚ)} : Set (E d))=⊤ :=
    AdjoinRoot.adjoinRoot_eq_top (R := ℚ) (f := Polynomial.cyclotomic d ℚ)
  rw [htop] at h
  exact h (by trivial)

lemma cm (hd : 2 < d) : NumberField.IsCMField (E d) :=
  IsCyclotomicExtension.Rat.isCMField (E d) (S := {d}) ⟨d,Set.mem_singleton d,hd⟩

end
end MultiplicityCounterexample.CyclotomicQuotient

namespace MultiplicityCounterexample.SourceCyclotomicField
noncomputable section
open NumberField Polynomial Algebra CyclotomicQuotient RealCyclotomicField
variable (d : ℕ) [NeZero d] [Fact (2 < d)]

instance quotientCM : IsCMField (E d) := cm d Fact.out

def F : IntermediateField ℚ (E d) :=
  realGeneratorField (AdjoinRoot.root (cyclotomic d ℚ))

lemma conj_root : IsCMField.complexConj (E d) (AdjoinRoot.root (cyclotomic d ℚ)) =
    (AdjoinRoot.root (cyclotomic d ℚ))⁻¹ := by
  let z := AdjoinRoot.root (cyclotomic d ℚ)
  let φ : E d →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  change φ (IsCMField.complexConj (E d) z) = φ (z⁻¹)
  rw [IsCMField.complexEmbedding_complexConj, map_inv₀]
  exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one
    (by rw [← map_pow, (root_primitive d).pow_eq_one, map_one]) (NeZero.ne d))).symm

lemma root_nonreal : IsCMField.complexConj (E d) (AdjoinRoot.root (cyclotomic d ℚ)) ≠
    AdjoinRoot.root (cyclotomic d ℚ) := by
  intro h
  let z : E d := AdjoinRoot.root (cyclotomic d ℚ)
  have hz : z ≠ 0 := (root_primitive d).ne_zero (NeZero.ne d)
  have he : z⁻¹ = z := (conj_root d).symm.trans h
  have hp : z ^ 2 = 1 := by
    rw [pow_two]
    calc z * z = z⁻¹ * z := congrArg (· * z) he.symm
         _ = 1 := inv_mul_cancel₀ hz
  have hdiv : d ∣ 2 := (root_primitive d).dvd_of_pow_eq_one 2 hp
  have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
  have hd : 2 < d := Fact.out
  omega

theorem F_eq_maximalReal : (F d).toSubfield = maximalRealSubfield (E d) :=
  realGeneratorField_eq_maximalReal _ ((root_primitive d).ne_zero (NeZero.ne d))
    (AdjoinRoot.adjoinRoot_eq_top (f := cyclotomic d ℚ)) (conj_root d) (root_nonreal d)

instance F_totallyReal : IsTotallyReal (F d) :=
  isTotallyReal_iff_le_maximalRealSubfield.mpr (F_eq_maximalReal d).le

lemma conj_fixed (a : F d) :
    IsCMField.complexConj (E d) (algebraMap (F d) (E d) a) = algebraMap (F d) (E d) a := by
  apply (IsCMField.complexConj_eq_self_iff (E d) _).mpr
  exact (F_eq_maximalReal d).le a.property

lemma exists_scalar_of_conj_fixed (x : E d) (hx : IsCMField.complexConj (E d) x = x) :
    ∃ a : F d, algebraMap (F d) (E d) a = x := by
  have hm := (IsCMField.complexConj_eq_self_iff (E d) x).mp hx
  rw [← F_eq_maximalReal d] at hm
  exact ⟨⟨x, hm⟩, rfl⟩

lemma F_finrank : Module.finrank (F d) (E d) = 2 := by
  have hle := realGeneratorField_finrank_le_two (AdjoinRoot.root (cyclotomic d ℚ))
    ((root_primitive d).ne_zero (NeZero.ne d))
    (AdjoinRoot.adjoinRoot_eq_top (f := cyclotomic d ℚ))
  change Module.finrank (F d) (E d) ≤ 2 at hle
  have hp : 0 < Module.finrank (F d) (E d) := Module.finrank_pos
  have hn : Module.finrank (F d) (E d) ≠ 1 := by
    intro h
    have ht : F d = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp h
    have hz : AdjoinRoot.root (cyclotomic d ℚ) ∈ F d := ht ▸ Set.mem_univ _
    exact root_nonreal d (conj_fixed d ⟨_, hz⟩)
  omega
end
end MultiplicityCounterexample.SourceCyclotomicField

namespace MultiplicityCounterexample.ComponentNondegenerate
noncomputable section
open Polynomial
open _root_.LinearMap (BilinForm)
variable {F E V : Type*} [Field F] [Field E] [Algebra F E]
  [AddCommGroup V] [Module F V]
  (T : Module.End F V) (B : BilinForm F V)
  (W : Submodule F V) [Module E W] [IsScalarTower F E W]
  (z : E) (hz : z ≠ 0)
  (hroot : ∀ x : W, ((z • x : W) : V)=T x)
  (hB : ∀ x y, B (T x) (T y)=B x y)

omit [Algebra F E] [IsScalarTower F E W] in
include hz hroot hB in
lemma inverse_adjoint (x : W) (y : V) :
    B (x : V) (T y)=B ((z⁻¹ • x : W) : V) y := by
  have h := hB (((z⁻¹ • x : W) : V)) y
  rw [← hroot,smul_smul,mul_inv_cancel₀ hz,one_smul] at h
  exact h

omit [Algebra F E] [IsScalarTower F E W] in
include hz hroot hB in
lemma power_adjoint (n : ℕ) (x : W) (y : V) :
    B (x : V) ((T^n) y)=B (((z⁻¹)^n • x : W) : V) y := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply,inverse_adjoint T B W z hz hroot hB,ih]
    rw [smul_smul,← pow_succ]

include hz hroot hB in
lemma polynomial_adjoint (p : F[X]) (x : W) (y : V) :
    B (x : V) ((aeval T p) y)=B (((aeval z⁻¹ p) • x : W) : V) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,LinearMap.add_apply,add_smul,Submodule.coe_add,hp,hq]
  | monomial n a =>
    rw [aeval_monomial,aeval_monomial,← Algebra.smul_def,← Algebra.smul_def]
    change B (x : V) (a • (T^n) y)=B (((a • (z⁻¹)^n) • x : W) : V) y
    rw [smul_assoc,Submodule.coe_smul]
    simp only [map_smul,LinearMap.smul_apply]
    rw [power_adjoint T B W z hz hroot hB]

include hz hroot hB in

lemma orthogonal_range (f : F[X]) (hf : aeval z⁻¹ f=0) (x : W) (y : V) :
    B (x : V) ((aeval T f) y)=0 := by
  rw [polynomial_adjoint T B W z hz hroot hB,hf,zero_smul]
  simp

omit [Field E] [Algebra F E] [Module E W] [IsScalarTower F E W] in
lemma ranges_span (p f : F[X]) (hc : IsCoprime f p) (y : V) :
    ∃ u v : V, y=(aeval T f) u+(aeval T p) v := by
  obtain ⟨a,b,h⟩ := hc
  refine ⟨(aeval T a) y,(aeval T b) y,?_⟩
  have h' := congrArg (fun q : F[X] => (aeval T q) y) h
  simp only [map_add,map_mul,map_one,LinearMap.add_apply,Module.End.mul_apply,
    Module.End.one_apply] at h'
  have haf : aeval T a * aeval T f=aeval T f * aeval T a := by
    rw [← map_mul,← map_mul,mul_comm a f]
  have hbp : aeval T b * aeval T p=aeval T p * aeval T b := by
    rw [← map_mul,← map_mul,mul_comm b p]
  rw [← Module.End.mul_apply,← Module.End.mul_apply,haf,hbp,
    Module.End.mul_apply,Module.End.mul_apply] at h'
  exact h'.symm

include hz hroot hB in

theorem restriction_nondegenerate (hs : B.IsSymm) (hnd : B.Nondegenerate)
    (p f : F[X]) (hc : IsCoprime f p)
    (hW : W=LinearMap.range (aeval T p)) (hf : aeval z⁻¹ f=0) :
    (B.restrict W).Nondegenerate := by
  have hleft : ∀ x : W, (∀ y : W, (B.restrict W) x y=0) → x=0 := by
    intro x hx
    apply Subtype.ext
    apply hnd.1 x
    intro y
    obtain ⟨u,v,rfl⟩ := ranges_span T p f hc y
    rw [map_add,orthogonal_range T B W z hz hroot hB f hf,zero_add]
    have hv : (aeval T p) v ∈ W := by rw [hW]; exact ⟨v,rfl⟩
    exact hx ⟨(aeval T p) v,hv⟩
  refine ⟨hleft,?_⟩
  intro y hy
  apply hleft y
  intro x
  change B (y : V) (x : V)=0
  rw [hs.eq]
  exact hy x

end
end MultiplicityCounterexample.ComponentNondegenerate

namespace MultiplicityCounterexample.TraceHermitian
noncomputable section
open Polynomial
open _root_.LinearMap (BilinForm)
variable {F E V : Type*} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]

def adjointScalars (σ : E ≃ₐ[F] E) (B : BilinForm F V) : Subalgebra F E where
  carrier := {a | ∀ x y, B (a • x) y=B x (σ a • y)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb x y
    simp only [add_smul,map_add,LinearMap.add_apply]
    rw [ha,hb]
  mul_mem' := by
    intro a b ha hb x y
    rw [mul_smul,ha,hb,map_mul,mul_smul,smul_comm (σ a) (σ b)]
  algebraMap_mem' := by
    intro a x y
    rw [σ.commutes,algebraMap_smul,algebraMap_smul]
    simp only [map_smul,LinearMap.smul_apply]

theorem adjointRule_of_generator (σ : E ≃ₐ[F] E) (B : BilinForm F V)
    (z : E) (hgen : Algebra.adjoin F {z}=⊤) (hz : z*σ z=1)
    (hB : ∀ x y, B (z • x) (z • y)=B x y) : AdjointRule σ B := by
  have hm : z ∈ adjointScalars σ B := by
    intro x y
    have h := hB x (σ z • y)
    rwa [← mul_smul,hz,one_smul] at h
  have hle : Algebra.adjoin F {z} ≤ adjointScalars σ B :=
    Algebra.adjoin_le (by simpa using hm)
  rw [hgen] at hle
  intro a
  exact hle (by trivial)

end
end MultiplicityCounterexample.TraceHermitian

end OAI
