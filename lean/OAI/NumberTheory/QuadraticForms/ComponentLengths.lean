import Mathlib
import OAI.NumberTheory.QuadraticForms.CyclotomicComponents

namespace OAI

/-! Component length forms at finite and infinite places. -/



namespace MultiplicityCounterexample.SourceComponentLengthAtPlaces
noncomputable section
open TensorProduct Polynomial NumberField
open LinearMap (BilinForm)
open CyclicComponent CyclotomicQuotient
open FixedFieldLocalComparison CyclotomicPlaceComparison CyclotomicLengthLocalComparison
open TensorAlgebraModule
variable (d : ℕ) [NeZero d] [Fact (2 < d)]
local notation "𝔽" => SourceCyclotomicField.F d
local notation "𝔼" => CyclotomicQuotient.E d
local notation "z" => AdjoinRoot.root (cyclotomic d ℚ)
def conjugation : 𝔼 ≃ₐ[ℚ] 𝔼 := (IsCMField.complexConj 𝔼).restrictScalars ℚ
local notation "σ" => conjugation d
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

lemma component_adjoint (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B (T x) (T y) = B x y) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hf
    TraceHermitian.AdjointRule σ (B.restrict (component T p)) := by
  let := componentScalarModule T p (cyclotomic d ℚ) hf
  apply TraceHermitian.adjointRule_of_generator σ _ z
    (AdjoinRoot.adjoinRoot_eq_top (f := cyclotomic d ℚ))
  · change z * IsCMField.complexConj 𝔼 z = 1
    rw [SourceCyclotomicField.conj_root d]
    exact mul_inv_cancel₀ ((root_primitive d).ne_zero (NeZero.ne d))
  · intro x y
    change B ((z • x : component T p) : V) ((z • y : component T p) : V) = B x y
    have hroot (w : component T p) : ((z • w : component T p) : V) = T w :=
      congrArg Subtype.val (root_smul (componentOperator T p) (cyclotomic d ℚ)
        (component_annihilated T p (cyclotomic d ℚ) hf) w)
    rw [hroot, hroot]
    exact hT x y

lemma component_selfAdjoint (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B (T x) (T y) = B x y) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hf
    SelfAdjointScalars (F := 𝔽) (B.restrict (component T p)) := by
  let := componentScalarModule T p (cyclotomic d ℚ) hf
  exact selfAdjointScalars_of_fixed_involution σ (SourceCyclotomicField.conj_fixed d) _
    (component_adjoint d T B p hf hT)

def componentLength (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B (T x) (T y) = B x y) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hf
    QuadraticForm 𝔽 (component T p) := by
  letI := componentScalarModule T p (cyclotomic d ℚ) hf
  exact sourceLength (B.restrict (component T p)) (component_selfAdjoint d T B p hf hT)

lemma componentLength_value (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B (T x) (T y) = B x y) (hs : B.IsSymm) (x : component T p) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hf
    algebraMap 𝔽 𝔼 (componentLength d T B p hf hT x) =
      TraceHermitian.lift (E := 𝔼) (B.restrict (component T p)) x x := by
  let := componentScalarModule T p (cyclotomic d ℚ) hf
  apply sourceLength_value σ
    (fun a => IsCMField.complexConj_apply_apply 𝔼 a)
    (SourceCyclotomicField.exists_scalar_of_conj_fixed d) (SourceCyclotomicField.F_finrank d)
    (B.restrict (component T p)) (component_selfAdjoint d T B p hf hT)
    ⟨fun a b => hs.eq a b⟩ (component_adjoint d T B p hf hT)

omit [Fact (2 < d)] in
lemma inverse_root : aeval z⁻¹ (cyclotomic d ℚ) = 0 := by
  have h := (isRoot_cyclotomic_iff_charZero (NeZero.pos d)).mpr (root_primitive d).inv
  rw [IsRoot, ← map_cyclotomic d (algebraMap ℚ 𝔼), ← eval₂_eq_eval_map] at h
  exact h

lemma componentLength_nondegenerate (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B (T x) (T y) = B x y)
    (hs : B.IsSymm) (hn : B.Nondegenerate) (hc : IsCoprime (cyclotomic d ℚ) p) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hf
    (componentLength d T B p hf hT).Nondegenerate := by
  let := componentScalarModule T p (cyclotomic d ℚ) hf
  apply sourceLength_nondegenerate (B.restrict (component T p))
    (component_selfAdjoint d T B p hf hT) ⟨fun x y => hs.eq x y⟩
  apply ComponentNondegenerate.restriction_nondegenerate T B (component T p) z
    ((root_primitive d).ne_zero (NeZero.ne d)) _ hT hs hn p (cyclotomic d ℚ) hc rfl
    (inverse_root d)
  intro x
  exact congrArg Subtype.val (root_smul (componentOperator T p) (cyclotomic d ℚ)
    (component_annihilated T p (cyclotomic d ℚ) hf) x)

def RationalPlaceDatum (A : Type*) [CommRing A] [Algebra ℚ A]
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W) : Prop :=
  ∃ e : (A ⊗[ℚ] V) ≃ₗ[A] (A ⊗[ℚ] W),
    (∀ x, e (T.baseChange A x) = U.baseChange A (e x)) ∧
    (∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y)

omit [Fact (2 < d)] in
lemma componentDatum {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X]) (hfT : aeval T (cyclotomic d ℚ * p) = 0)
    (hfU : aeval U (cyclotomic d ℚ * p) = 0)
    (he : RationalPlaceDatum A T U B₁ B₂) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hfT
    letI := componentScalarModule U p (cyclotomic d ℚ) hfU
    LocalEquivariantIsometry A (B₁.restrict (component T p)) (B₂.restrict (component U p)) z := by
  let := componentScalarModule T p (cyclotomic d ℚ) hfT
  let := componentScalarModule U p (cyclotomic d ℚ) hfU
  obtain ⟨e, hT, hB⟩ := he
  exact ComponentRootLocalComparison.component_root_local_datum T U B₁ B₂ e hT hB p
    (cyclotomic d ℚ) hfT hfU

theorem componentLength_isometric_at_all_places
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X]) (hfT : aeval T (cyclotomic d ℚ * p) = 0)
    (hfU : aeval U (cyclotomic d ℚ * p) = 0)
    (hT : ∀ x y, B₁ (T x) (T y) = B₁ x y) (hU : ∀ x y, B₂ (U x) (U y) = B₂ x y)
    (hreal : RationalPlaceDatum ℝ T U B₁ B₂)
    (hloc : ∀ (q : ℕ) (_ : Fact q.Prime), RationalPlaceDatum (Padic q) T U B₁ B₂) :
    letI := componentScalarModule T p (cyclotomic d ℚ) hfT
    letI := componentScalarModule U p (cyclotomic d ℚ) hfU
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 𝔽),
      Nonempty (((componentLength d T B₁ p hfT hT).baseChange (v.adicCompletion 𝔽)).IsometryEquiv
        ((componentLength d U B₂ p hfU hU).baseChange (v.adicCompletion 𝔽)))) ∧
    (∀ v : InfinitePlace 𝔽,
      Nonempty (((componentLength d T B₁ p hfT hT).baseChange v.Completion).IsometryEquiv
        ((componentLength d U B₂ p hfU hU).baseChange v.Completion))) := by
  let := componentScalarModule T p (cyclotomic d ℚ) hfT
  let := componentScalarModule U p (cyclotomic d ℚ) hfU
  constructor
  · intro v
    exact length_isometric_at_every_finitePlace _ _ _ _ z
      (AdjoinRoot.adjoinRoot_eq_top (f := cyclotomic d ℚ))
      (fun q hq => componentDatum d T U B₁ B₂ p hfT hfU (hloc q hq)) v
  · intro v
    exact length_isometric_at_every_infinitePlace _ _ _ _ z
      (AdjoinRoot.adjoinRoot_eq_top (f := cyclotomic d ℚ))
      (componentDatum d T U B₁ B₂ p hfT hfU hreal) v
end
end MultiplicityCounterexample.SourceComponentLengthAtPlaces

namespace MultiplicityCounterexample.CyclotomicComponentFactor
noncomputable section
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

lemma cyclotomic_dvd (m d : ℕ) (hd : d ∣ m) :
    cyclotomic d ℚ ∣ (X^m-1 : ℚ[X]) := by
  apply dvd_trans (cyclotomic.dvd_X_pow_sub_one d ℚ)
  obtain ⟨k,rfl⟩ := hd
  simpa only [pow_mul,one_pow] using sub_dvd_pow_sub_pow (X^d : ℚ[X]) 1 k

theorem exists_complement (T : Module.End ℚ V) (m d : ℕ) (hm : 0 < m)
    (hd : d ∣ m) (hT : T^m=1) :
    ∃ p : ℚ[X], cyclotomic d ℚ*p=X^m-1 ∧
      IsCoprime (cyclotomic d ℚ) p ∧ aeval T (cyclotomic d ℚ*p)=0 := by
  obtain ⟨p,hp⟩ := cyclotomic_dvd m d hd
  refine ⟨p,hp.symm,?_,?_⟩
  · apply Polynomial.Separable.isCoprime
    rw [← hp]
    exact (X_pow_sub_one_separable_iff).mpr (by exact_mod_cast hm.ne')
  · rw [← hp,map_sub,map_pow,aeval_X,map_one,hT,sub_self]

lemma commute_aeval (T : Module.End ℚ V) (p q : ℚ[X]) :
    Commute (aeval T p) (aeval T q) := (Commute.all p q).map (aeval T)

theorem range_eq_ker (T : Module.End ℚ V) (f p : ℚ[X])
    (hc : IsCoprime f p) (hT : aeval T (f*p)=0) :
    LinearMap.range (aeval T p)=LinearMap.ker (aeval T f) := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    change (aeval T f) ((aeval T p) y)=0
    rw [← Module.End.mul_apply,← map_mul,hT]
    rfl
  · intro x hx
    obtain ⟨a,b,h⟩ := hc
    refine ⟨(aeval T b) x,?_⟩
    have h' := congrArg (fun q : ℚ[X] => (aeval T q) x) h
    simp only [map_add,map_mul,map_one,LinearMap.add_apply,Module.End.mul_apply,
      Module.End.one_apply] at h'
    have hx' : (aeval T f) x=0 := hx
    rw [hx',map_zero,zero_add] at h'
    rw [← Module.End.mul_apply,(commute_aeval T p b).eq,Module.End.mul_apply]
    exact h'

lemma component_annihilation (T : Module.End ℚ V) (f p : ℚ[X])
    (hT : aeval T (f*p)=0) (x : LinearMap.range (aeval T p)) :
    (aeval T f) x=0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy,← Module.End.mul_apply,← map_mul,hT]
  rfl

theorem semisimple (T : Module.End ℚ V) (m : ℕ) (hm : 0 < m) (hT : T^m=1) :
    T.IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    ((X_pow_sub_one_separable_iff (F := ℚ)).mpr (by exact_mod_cast hm.ne')).squarefree
  rw [map_sub,map_pow,aeval_X,map_one,hT,sub_self]

end
end MultiplicityCounterexample.CyclotomicComponentFactor

namespace MultiplicityCounterexample.HasseMinkowskiGap
noncomputable section
open NumberField
variable {F V W : Type*} [Field F] [NumberField F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def AllPlacesIsometric (Q₁ : QuadraticForm F V) (Q₂ : QuadraticForm F W) : Prop :=
  (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    Nonempty ((Q₁.baseChange (v.adicCompletion F)).IsometryEquiv
      (Q₂.baseChange (v.adicCompletion F)))) ∧
  (∀ v : InfinitePlace F,
    Nonempty ((Q₁.baseChange v.Completion).IsometryEquiv (Q₂.baseChange v.Completion)))

def NumberFieldQuadraticLocalGlobal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Q₁ : QuadraticForm F V) (Q₂ : QuadraticForm F W),
    Q₁.Nondegenerate → Q₂.Nondegenerate → AllPlacesIsometric Q₁ Q₂ →
      Nonempty (Q₁.IsometryEquiv Q₂)
end
end MultiplicityCounterexample.HasseMinkowskiGap

namespace MultiplicityCounterexample.SourceComponentLengthAtPlaces
noncomputable section
open TensorProduct Polynomial NumberField
open LinearMap (BilinForm)
open CyclicComponent CyclotomicQuotient HasseMinkowskiGap
variable (d : ℕ) [NeZero d] [Fact (2 < d)]
local notation "𝔽" => SourceCyclotomicField.F d
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

theorem finite_order_component_hasse_input
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (m : ℕ) (hm : Odd m) (hd : d ∣ m) (hTm : T ^ m = 1) (hUm : U ^ m = 1)
    (hs₁ : B₁.IsSymm) (hs₂ : B₂.IsSymm) (hn₁ : B₁.Nondegenerate) (hn₂ : B₂.Nondegenerate)
    (hT : ∀ x y, B₁ (T x) (T y) = B₁ x y) (hU : ∀ x y, B₂ (U x) (U y) = B₂ x y)
    (hreal : RationalPlaceDatum ℝ T U B₁ B₂)
    (hloc : ∀ (q : ℕ) (_ : Fact q.Prime), RationalPlaceDatum (Padic q) T U B₁ B₂) :
    ∃ (p : ℚ[X]) (hfT : aeval T (cyclotomic d ℚ * p) = 0)
      (hfU : aeval U (cyclotomic d ℚ * p) = 0),
      cyclotomic d ℚ * p = X ^ m - 1 ∧ IsCoprime (cyclotomic d ℚ) p ∧
      letI := componentScalarModule T p (cyclotomic d ℚ) hfT
      letI := componentScalarModule U p (cyclotomic d ℚ) hfU
      FiniteDimensional 𝔽 (component T p) ∧ FiniteDimensional 𝔽 (component U p) ∧
      (componentLength d T B₁ p hfT hT).Nondegenerate ∧
      (componentLength d U B₂ p hfU hU).Nondegenerate ∧
      AllPlacesIsometric (componentLength d T B₁ p hfT hT)
        (componentLength d U B₂ p hfU hU) := by
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  obtain ⟨p, hp, hc, hfT⟩ := CyclotomicComponentFactor.exists_complement T m d hmpos hd hTm
  have hfU : aeval U (cyclotomic d ℚ * p) = 0 := by
    rw [hp, map_sub, map_pow, aeval_X, map_one, hUm, sub_self]
  refine ⟨p, hfT, hfU, hp, hc, ?_⟩
  let := componentScalarModule T p (cyclotomic d ℚ) hfT
  let := componentScalarModule U p (cyclotomic d ℚ) hfU
  exact ⟨Module.Finite.of_restrictScalars_finite ℚ 𝔽 (component T p),
    Module.Finite.of_restrictScalars_finite ℚ 𝔽 (component U p),
    componentLength_nondegenerate d T B₁ p hfT hT hs₁ hn₁ hc,
    componentLength_nondegenerate d U B₂ p hfU hU hs₂ hn₂ hc,
    componentLength_isometric_at_all_places d T U B₁ B₂ p hfT hfU hT hU hreal hloc⟩
end
end MultiplicityCounterexample.SourceComponentLengthAtPlaces

namespace MultiplicityCounterexample.IdentityComponentAtPlaces
noncomputable section
open TensorProduct Polynomial NumberField
open LinearMap (BilinForm)
open CyclicComponent FixedFieldLocalComparison CyclotomicPlaceComparison
open SourceComponentLengthAtPlaces HasseMinkowskiGap TensorAlgebraModule
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

lemma identity_on_component (T : Module.End ℚ V) (p : ℚ[X])
    (hf : aeval T ((X - 1) * p) = 0) (x : component T p) : T x = x := by
  have h := component_annihilated T p (X - 1) hf
  have he : componentOperator T p - 1 = 0 := by
    simpa only [map_sub, aeval_X, map_one] using h
  have hx := congrArg (fun f : Module.End ℚ (component T p) => (f x : V)) he
  change T x - (x : V) = 0 at hx
  exact sub_eq_zero.mp hx

lemma restriction_nondegenerate (T : Module.End ℚ V) (B : BilinForm ℚ V) (p : ℚ[X])
    (hf : aeval T ((X - 1) * p) = 0) (hc : IsCoprime (X - 1) p)
    (hT : ∀ x y, B (T x) (T y) = B x y) (hs : B.IsSymm) (hn : B.Nondegenerate) :
    (B.restrict (component T p)).Nondegenerate := by
  apply ComponentNondegenerate.restriction_nondegenerate T B (component T p) (1 : ℚ)
    one_ne_zero _ hT hs hn p (X - 1) hc rfl (by simp)
  intro x
  simpa only [one_smul] using (identity_on_component T p hf x).symm

lemma rat_selfAdjoint (B : BilinForm ℚ V) : SelfAdjointScalars (F := ℚ) B := by
  intro a x y
  simp only [map_smul, LinearMap.smul_apply]

lemma fixedForm_rat (B : BilinForm ℚ V) : fixedForm B (rat_selfAdjoint B) = B := by
  ext x y
  have h := TraceHermitian.trace_lift_one (E := ℚ) B x y
  simpa only [Algebra.trace_self, LinearMap.id_apply, fixedForm_apply] using h

lemma fixedForm_rat_canonical (B : BilinForm ℚ V) :
    letI : Algebra ℚ ℚ := DivisionRing.toRatAlgebra
    fixedForm (F := ℚ) B (rat_selfAdjoint B) = B := by
  exact fixedForm_rat B

lemma componentDatum {A : Type*} [CommRing A] [Algebra ℚ A]
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X]) (he : RationalPlaceDatum A T U B₁ B₂) :
    LocalEquivariantIsometry A (B₁.restrict (component T p)) (B₂.restrict (component U p)) (1 : ℚ) := by
  obtain ⟨e, hT, hB⟩ := he
  obtain ⟨c, _, hc⟩ := PolynomialComponentRestriction.component_local_datum T U B₁ B₂ e hT hB p
  exact ⟨c, by intro x; simp only [map_one, Module.End.one_apply], hc⟩

lemma restricted_forms_at_every_finitePlace
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X])
    (hloc : ∀ (q : ℕ) (_ : Fact q.Prime), RationalPlaceDatum (Padic q) T U B₁ B₂)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    letI : Algebra ℚ (v.adicCompletion ℚ) := IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    Nonempty (((B₁.restrict (component T p)).baseChange (v.adicCompletion ℚ)).IsometryEquiv
      ((B₂.restrict (component U p)).baseChange (v.adicCompletion ℚ))) := by
  let : Algebra ℚ (v.adicCompletion ℚ) := IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  have h := fixedForm_isometric_at_every_finitePlace (F := ℚ) (E := ℚ)
    (B₁.restrict (component T p)) (B₂.restrict (component U p))
    (rat_selfAdjoint _) (rat_selfAdjoint _) (1 : ℚ) (by
      apply top_unique
      intro x hx
      exact (Algebra.adjoin ℚ ({(1 : ℚ)} : Set ℚ)).algebraMap_mem x)
    (fun q hq => componentDatum T U B₁ B₂ p (hloc q hq)) v
  simpa only [fixedForm_rat_canonical] using h

lemma restricted_forms_at_every_infinitePlace
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X]) (hreal : RationalPlaceDatum ℝ T U B₁ B₂) (v : InfinitePlace ℚ) :
    letI : Algebra ℚ v.Completion := NumberField.InfinitePlace.Completion.instAlgebra v ℚ
    Nonempty (((B₁.restrict (component T p)).baseChange v.Completion).IsometryEquiv
      ((B₂.restrict (component U p)).baseChange v.Completion)) := by
  let : Algebra ℚ v.Completion := NumberField.InfinitePlace.Completion.instAlgebra v ℚ
  have h := fixedForm_isometric_at_every_infinitePlace (F := ℚ) (E := ℚ)
    (B₁.restrict (component T p)) (B₂.restrict (component U p))
    (rat_selfAdjoint _) (rat_selfAdjoint _) (1 : ℚ) (by
      apply top_unique
      intro x hx
      exact (Algebra.adjoin ℚ ({(1 : ℚ)} : Set ℚ)).algebraMap_mem x)
    (componentDatum T U B₁ B₂ p hreal) v
  simpa only [fixedForm_rat_canonical] using h

lemma diagonal_nondegenerate (B : BilinForm ℚ V) (hs : B.IsSymm) (hn : B.Nondegenerate) :
    B.toQuadraticMap.Nondegenerate := by
  apply QuadraticMap.nondegenerate_associated_iff.mp
  rw [QuadraticMap.associated_left_inverse ℚ hs.eq]
  exact hn

lemma diagonal_baseChange {K : Type*} [CommRing K] [Algebra ℚ K] (B : BilinForm ℚ V) :
    QuadraticForm.baseChange K B.toQuadraticMap = (B.baseChange K).toQuadraticMap := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]

def diagonalIsometryAtPlace {K : Type*} [CommRing K] [Algebra ℚ K]
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (e : (B₁.baseChange K).IsometryEquiv (B₂.baseChange K)) :
    (QuadraticForm.baseChange K B₁.toQuadraticMap).IsometryEquiv (QuadraticForm.baseChange K B₂.toQuadraticMap) where
  __ := e.toLinearEquiv
  map_app' x := by
    rw [diagonal_baseChange, diagonal_baseChange]
    exact e.map_app x x

theorem component_all_places
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (p : ℚ[X]) (hreal : RationalPlaceDatum ℝ T U B₁ B₂)
    (hloc : ∀ (q : ℕ) (_ : Fact q.Prime), RationalPlaceDatum (Padic q) T U B₁ B₂) :
    AllPlacesIsometric (B₁.restrict (component T p)).toQuadraticMap
      (B₂.restrict (component U p)).toQuadraticMap := by
  constructor
  · intro v
    let : Algebra ℚ (v.adicCompletion ℚ) := IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    obtain ⟨e⟩ := restricted_forms_at_every_finitePlace T U B₁ B₂ p hloc v
    exact ⟨diagonalIsometryAtPlace _ _ e⟩
  · intro v
    let : Algebra ℚ v.Completion := NumberField.InfinitePlace.Completion.instAlgebra v ℚ
    obtain ⟨e⟩ := restricted_forms_at_every_infinitePlace T U B₁ B₂ p hreal v
    exact ⟨diagonalIsometryAtPlace _ _ e⟩

theorem finite_order_identity_hasse_input [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (T : Module.End ℚ V) (U : Module.End ℚ W) (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (m : ℕ) (hm : Odd m) (hTm : T ^ m = 1) (hUm : U ^ m = 1)
    (hs₁ : B₁.IsSymm) (hs₂ : B₂.IsSymm) (hn₁ : B₁.Nondegenerate) (hn₂ : B₂.Nondegenerate)
    (hT : ∀ x y, B₁ (T x) (T y) = B₁ x y) (hU : ∀ x y, B₂ (U x) (U y) = B₂ x y)
    (hreal : RationalPlaceDatum ℝ T U B₁ B₂)
    (hloc : ∀ (q : ℕ) (_ : Fact q.Prime), RationalPlaceDatum (Padic q) T U B₁ B₂) :
    ∃ (p : ℚ[X]), (X - 1) * p = X ^ m - 1 ∧ IsCoprime (X - 1) p ∧
      (B₁.restrict (component T p)).toQuadraticMap.Nondegenerate ∧
      (B₂.restrict (component U p)).toQuadraticMap.Nondegenerate ∧
      AllPlacesIsometric (B₁.restrict (component T p)).toQuadraticMap
        (B₂.restrict (component U p)).toQuadraticMap := by
  have hmpos : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  obtain ⟨p, hp, hc, hfT⟩ := CyclotomicComponentFactor.exists_complement T m 1 hmpos (one_dvd m) hTm
  rw [cyclotomic_one] at hp hc hfT
  have hfU : aeval U ((X - 1) * p) = 0 := by
    rw [hp, map_sub, map_pow, aeval_X, map_one, hUm, sub_self]
  exact ⟨p, hp, hc,
    diagonal_nondegenerate (B₁.restrict (component T p)) ⟨fun x y => hs₁.eq x y⟩
      (restriction_nondegenerate T B₁ p hfT hc hT hs₁ hn₁),
    diagonal_nondegenerate (B₂.restrict (component U p)) ⟨fun x y => hs₂.eq x y⟩
      (restriction_nondegenerate U B₂ p hfU hc hU hs₂ hn₂),
    component_all_places T U B₁ B₂ p hreal hloc⟩
end
end MultiplicityCounterexample.IdentityComponentAtPlaces

end OAI
