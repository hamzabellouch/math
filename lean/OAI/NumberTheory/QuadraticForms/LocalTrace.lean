import Mathlib
import OAI.NumberTheory.QuadraticForms.ScalarExtension

namespace OAI

/-! Local trace and cyclotomic length comparisons. -/



namespace MultiplicityCounterexample.CompletionPlaceMaps
noncomputable section
open Filter
open scoped Topology

section RestrictedNorm
variable (K : Type*) [NormedField K] [CharZero K]

def rationalAbs : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : K)‖
  map_mul' x y := by simp
  nonneg' x := norm_nonneg _
  eq_zero' x := by simp
  add_le' x y := by simpa using norm_add_le (x : K) (y : K)

@[simp] lemma rationalAbs_apply (q : ℚ) : rationalAbs K q = ‖(q : K)‖ := rfl

variable {K}

def fromWithVal (p : ℕ) [Fact p.Prime] : WithVal (Rat.padicValuation p) →+* K :=
  (Rat.castHom K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom

lemma continuous_fromWithVal (p : ℕ) [Fact p.Prime]
    (h : (rationalAbs K).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Continuous (fromWithVal (K := K) p) := by
  obtain ⟨t, ht, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp h.symm
  have hn : Continuous fun q : WithVal (Rat.padicValuation p) =>
      ‖((WithVal.equiv (Rat.padicValuation p)) q : Padic p)‖ :=
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous.norm
  have hc : Continuous fun q : WithVal (Rat.padicValuation p) =>
      ‖fromWithVal (K := K) p q‖ := by
    have hr := hn.rpow_const (p := t) (fun _ => Or.inr ht.le)
    convert hr using 1
    ext q
    have e := congrFun heq ((WithVal.equiv (Rat.padicValuation p)) q)
    change ‖(((WithVal.equiv (Rat.padicValuation p)) q : ℚ) : K)‖ = _
    rw [Padic.eq_padicNorm]
    exact e.symm
  apply continuous_of_tendsto_nhds_zero (fromWithVal (K := K) p)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa using hc.continuousAt.tendsto (x := 0)

variable [CompleteSpace K]

def padicMap (p : ℕ) [Fact p.Prime]
    (h : (rationalAbs K).IsEquiv (Rat.AbsoluteValue.padic p)) : Padic p →+* K :=
  (UniformSpace.Completion.extensionHom (fromWithVal (K := K) p)
    (continuous_fromWithVal p h)).comp Padic.withValRingEquiv.symm.toRingHom

theorem exists_padicMap
    (hne : (rationalAbs K).IsNontrivial)
    (hbd : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, Nonempty (Padic p →+* K) := by
  obtain ⟨p, ⟨hp, he⟩, _⟩ :=
    Rat.AbsoluteValue.equiv_padic_of_bounded hne (by simpa using hbd)
  let := hp
  exact ⟨p, hp, ⟨padicMap p he⟩⟩

end RestrictedNorm

section FinitePlace
open scoped NumberField
open IsDedekindDomain
variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))

instance finitePlaceCharZero : CharZero (v.adicCompletion F) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding v).injective

lemma rationalAbs_finitePlace_nontrivial :
    (rationalAbs (v.adicCompletion F)).IsNontrivial := by
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp
    (Ideal.IsIntegral.under_ne_bot ℤ v.ne_bot)
  refine ⟨(z : ℚ), by exact_mod_cast hz0, ?_⟩
  have hv := (NumberField.FinitePlace.norm_lt_one_iff_mem F v
    ((algebraMap ℤ (𝓞 F)) z)).mpr hz
  have hv' : ‖(z : v.adicCompletion F)‖ < 1 := by simpa using hv
  simpa using ne_of_lt hv'

lemma rationalAbs_finitePlace_bounded (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  have hn := NumberField.FinitePlace.norm_embedding (K := F) v (n : F)
  simp only [map_natCast] at hn
  rw [hn]
  exact NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v n

theorem exists_finitePlace_padicAlgHom :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, Nonempty (Padic p →ₐ[ℚ] v.adicCompletion F) := by
  obtain ⟨p, hp, ⟨f⟩⟩ := exists_padicMap
    (rationalAbs_finitePlace_nontrivial F v) (rationalAbs_finitePlace_bounded F v)
  exact ⟨p, hp, ⟨f.toRatAlgHom⟩⟩

end FinitePlace

open NumberField
variable (F : Type*) [Field F] [NumberField F] (v : InfinitePlace F)

instance infinitePlaceCharZero : CharZero v.Completion :=
  charZero_of_injective_ringHom (algebraMap F v.Completion).injective

def infinitePlaceRealAlgHom : ℝ →ₐ[ℚ] v.Completion := by
  classical
  by_cases hv : v.IsReal
  · exact (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toRingHom.toRatAlgHom
  · exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).symm.toRingHom.comp
      (algebraMap ℝ ℂ)).toRatAlgHom


end
end MultiplicityCounterexample.CompletionPlaceMaps

namespace MultiplicityCounterexample.NumberFieldTraceLocalComparison
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped NumberField MultiplicityCounterexample.TensorAlgebraModule
open CompletionTraceDescent CompletionPlaceMaps
variable {F V W : Type*} [Field F] [NumberField F]
  [AddCommGroup V] [Module ℚ V] [Module F V] [IsScalarTower ℚ F V]
  [AddCommGroup W] [Module ℚ W] [Module F W] [IsScalarTower ℚ F W]

def LocalTraceIsometry (A : Type*) [CommRing A] [Algebra ℚ A]
    (B₁ : BilinForm F V) (B₂ : BilinForm F W) (z : F) : Prop :=
  ∃ e : (A ⊗[ℚ] V) ≃ₗ[A] (A ⊗[ℚ] W),
    (∀ x, e (TensorAlgebraModule.rightAction z x) =
      TensorAlgebraModule.rightAction z (e x)) ∧
    (∀ x y, (traceForm (R := ℚ) B₂).baseChange A (e x) (e y) =
      (traceForm (R := ℚ) B₁).baseChange A x y)

theorem isometric_at_every_finitePlace
    (B₁ : BilinForm F V) (B₂ : BilinForm F W)
    (z : F) (hzgen : Algebra.adjoin ℚ ({z} : Set F) = ⊤)
    (hloc : ∀ (p : ℕ) (_ : Fact p.Prime), LocalTraceIsometry (Padic p) B₁ B₂ z)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Nonempty ((B₁.baseChange (v.adicCompletion F)).IsometryEquiv
      (B₂.baseChange (v.adicCompletion F))) := by
  obtain ⟨p, hp, ⟨f⟩⟩ := exists_finitePlace_padicAlgHom F v
  let : Algebra (Padic p) (v.adicCompletion F) := f.toRingHom.toAlgebra
  let : IsScalarTower ℚ (Padic p) (v.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq (fun q => (f.commutes q).symm)
  obtain ⟨e, hz, he⟩ := hloc p hp
  exact ⟨descendTraceAtPlace (K := v.adicCompletion F) B₁ B₂ z hzgen e hz he⟩

theorem isometric_at_every_infinitePlace
    (B₁ : BilinForm F V) (B₂ : BilinForm F W)
    (z : F) (hzgen : Algebra.adjoin ℚ ({z} : Set F) = ⊤)
    (hreal : LocalTraceIsometry ℝ B₁ B₂ z)
    (v : NumberField.InfinitePlace F) :
    Nonempty ((B₁.baseChange v.Completion).IsometryEquiv (B₂.baseChange v.Completion)) := by
  let f := infinitePlaceRealAlgHom F v
  let : Algebra ℝ v.Completion := f.toRingHom.toAlgebra
  let : IsScalarTower ℚ ℝ v.Completion :=
    IsScalarTower.of_algebraMap_eq (fun q => (f.commutes q).symm)
  obtain ⟨e, hz, he⟩ := hreal
  exact ⟨descendTraceAtPlace (K := v.Completion) B₁ B₂ z hzgen e hz he⟩

end
end MultiplicityCounterexample.NumberFieldTraceLocalComparison

namespace MultiplicityCounterexample.TraceHermitian
open LinearMap (BilinForm)
noncomputable section
variable {F E V W : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]

lemma trace_pairing_ext {x y : E}
    (h : ∀ a : E, Algebra.trace F E (a*x) = Algebra.trace F E (a*y)) : x = y := by
  apply ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).injective
  ext a
  simpa only [BilinForm.toDual_def,Algebra.traceForm_apply,mul_comm] using h a

def traceFunctional (B : BilinForm F V) (x y : V) : Module.Dual F E where
  toFun a := B (a • x) y
  map_add' a b := by simp only [add_smul,map_add,LinearMap.add_apply]
  map_smul' a b := by simp only [smul_assoc,map_smul,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply]

def lift (B : BilinForm F V) (x y : V) : E :=
  ((Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)).symm
    (traceFunctional B x y)

lemma trace_lift (B : BilinForm F V) (x y : V) (a : E) :
    Algebra.trace F E (a * lift (E := E) B x y) = B (a • x) y := by
  have h := BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm F E)
    (hB := traceForm_nondegenerate F E) (traceFunctional B x y) a
  change Algebra.trace F E (lift (E := E) B x y * a) = B (a • x) y at h
  simpa only [mul_comm] using h

lemma trace_lift_one (B : BilinForm F V) (x y : V) :
    Algebra.trace F E (lift (E := E) B x y) = B x y := by
  simpa using trace_lift (E := E) B x y (1 : E)

lemma lift_add_left (B : BilinForm F V) (x y z : V) :
    lift (E := E) B (x+y) z = lift (E := E) B x z + lift (E := E) B y z := by
  apply trace_pairing_ext (F := F)
  intro a
  simp only [mul_add,map_add,trace_lift,smul_add,LinearMap.add_apply]

lemma lift_add_right (B : BilinForm F V) (x y z : V) :
    lift (E := E) B x (y+z) = lift (E := E) B x y + lift (E := E) B x z := by
  apply trace_pairing_ext (F := F)
  intro a
  simp only [mul_add,map_add,trace_lift]

lemma lift_smul_left (B : BilinForm F V) (a : E) (x y : V) :
    lift (E := E) B (a • x) y = a * lift (E := E) B x y := by
  apply trace_pairing_ext (F := F)
  intro b
  rw [trace_lift,← mul_assoc,trace_lift,mul_smul]

variable (σ : E ≃ₐ[F] E) (hσ : Function.Involutive σ)

def AdjointRule (B : BilinForm F V) : Prop :=
  ∀ (a : E) (x y : V), B (a • x) y = B x (σ a • y)

include hσ in
lemma lift_smul_right (B : BilinForm F V) (hB : AdjointRule σ B)
    (a : E) (x y : V) : lift (E := E) B x (a • y) = σ a * lift (E := E) B x y := by
  apply trace_pairing_ext (F := F)
  intro b
  rw [trace_lift,← mul_assoc,mul_comm b (σ a),trace_lift,mul_smul,hB (σ a) (b • x) y,hσ]

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] in
lemma trace_sigma (a : E) : Algebra.trace F E (σ a) = Algebra.trace F E a := by
  exact Algebra.trace_eq_of_algEquiv σ a

include hσ in
lemma lift_symmetric (B : BilinForm F V) (hs : B.IsSymm) (hB : AdjointRule σ B)
    (x y : V) : lift (E := E) B y x = σ (lift (E := E) B x y) := by
  apply trace_pairing_ext (F := F)
  intro a
  rw [trace_lift,← trace_sigma σ (a * σ (lift (E := E) B x y)),map_mul,hσ,trace_lift]
  rw [hB a y x,hs.eq]

lemma lift_nondegenerate_left (B : BilinForm F V) (hB : B.Nondegenerate)
    (x : V) (hx : ∀ y, lift (E := E) B x y = 0) : x = 0 := by
  apply hB.1 x
  intro y
  rw [← trace_lift_one (E := E), hx,map_zero]

lemma lift_nondegenerate_right (B : BilinForm F V) (hB : B.Nondegenerate)
    (y : V) (hy : ∀ x, lift (E := E) B x y = 0) : y = 0 := by
  apply hB.2 y
  intro x
  rw [← trace_lift_one (E := E),hy,map_zero]

theorem preserves_iff (B : BilinForm F V) (C : BilinForm F W) (e : V ≃ₗ[E] W) :
    (∀ x y, C (e x) (e y) = B x y) ↔
      ∀ x y, lift (E := E) C (e x) (e y) = lift (E := E) B x y := by
  constructor
  · intro he x y
    apply trace_pairing_ext (F := F)
    intro a
    rw [trace_lift,trace_lift,← e.map_smul,he]
  · intro he x y
    rw [← trace_lift_one (E := E),← trace_lift_one (E := E),he]

theorem lift_unique (B : BilinForm F V) (h : V → V → E)
    (hh : ∀ a x y, Algebra.trace F E (a * h x y) = B (a • x) y) :
    h = lift (E := E) B := by
  funext x y
  apply trace_pairing_ext (F := F)
  intro a
  rw [hh,trace_lift]

end
end MultiplicityCounterexample.TraceHermitian

namespace MultiplicityCounterexample.FixedFieldLocalComparison
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped MultiplicityCounterexample.TensorAlgebraModule
variable {R F V W : Type*} [Field R] [Field F] [Algebra R F]
  [FiniteDimensional R F] [Algebra.IsSeparable R F]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]
  [AddCommGroup W] [Module R W] [Module F W] [IsScalarTower R F W]

def SelfAdjointScalars (B : BilinForm R V) : Prop :=
  ∀ a : F, ∀ x y : V, B (a • x) y = B x (a • y)

def fixedForm (B : BilinForm R V) (hB : SelfAdjointScalars (F := F) B) : BilinForm F V where
  toFun x :=
    { toFun := fun y => TraceHermitian.lift (E := F) B x y
      map_add' := TraceHermitian.lift_add_right B x
      map_smul' a y := by
        change TraceHermitian.lift B x (a • y) = a * TraceHermitian.lift B x y
        exact TraceHermitian.lift_smul_right (.refl : F ≃ₐ[R] F)
          (fun _ => rfl) B hB a x y }
  map_add' x y := by ext w; exact TraceHermitian.lift_add_left B x y w
  map_smul' a x := by
    ext y
    exact TraceHermitian.lift_smul_left B a x y

@[simp] lemma fixedForm_apply (B : BilinForm R V) (hB : SelfAdjointScalars (F := F) B)
    (x y : V) : fixedForm B hB x y = TraceHermitian.lift B x y := rfl

lemma trace_fixedForm (B : BilinForm R V) (hB : SelfAdjointScalars (F := F) B) :
    CompletionTraceDescent.traceForm (fixedForm B hB) = B := by
  ext x y
  exact TraceHermitian.trace_lift_one B x y

lemma fixedForm_symmetric (B : BilinForm R V) (hB : SelfAdjointScalars (F := F) B)
    (hs : B.IsSymm) : (fixedForm B hB).IsSymm := by
  constructor
  intro x y
  exact (TraceHermitian.lift_symmetric (.refl : F ≃ₐ[R] F)
    (fun _ => rfl) B hs hB y x)

lemma fixedForm_nondegenerate (B : BilinForm R V) (hB : SelfAdjointScalars (F := F) B)
    (hn : B.Nondegenerate) : (fixedForm B hB).Nondegenerate := by
  constructor
  · intro x hx
    exact TraceHermitian.lift_nondegenerate_left B hn x hx
  · intro y hy
    exact TraceHermitian.lift_nondegenerate_right B hn y hy

end

noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped NumberField
open NumberFieldTraceLocalComparison
variable {F V W A : Type*} [Field F] [NumberField F]
  [CommRing A] [Algebra ℚ A]
  [AddCommGroup V] [Module ℚ V] [Module F V] [IsScalarTower ℚ F V]
  [AddCommGroup W] [Module ℚ W] [Module F W] [IsScalarTower ℚ F W]

theorem localTraceIsometry_of_equivariant
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : F) (e : (A ⊗[ℚ] V) ≃ₗ[A] (A ⊗[ℚ] W))
    (hz : ∀ x, e (TensorAlgebraModule.rightAction z x) =
      TensorAlgebraModule.rightAction z (e x))
    (he : ∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y) :
    LocalTraceIsometry A (fixedForm B₁ h₁) (fixedForm B₂ h₂) z := by
  refine ⟨e, hz, ?_⟩
  simpa only [trace_fixedForm] using he

end
end MultiplicityCounterexample.FixedFieldLocalComparison

namespace MultiplicityCounterexample.FixedFieldBridge
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open TensorAlgebraModule
variable {R F E A V W : Type*} [CommRing R] [CommRing F] [CommRing E]
  [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
  [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [Module F V] [Module E V]
  [IsScalarTower R F V] [IsScalarTower R E V] [IsScalarTower F E V]
  [AddCommGroup W] [Module R W] [Module F W] [Module E W]
  [IsScalarTower R F W] [IsScalarTower R E W] [IsScalarTower F E W]

omit [IsScalarTower R F E] in
lemma rightAction_tower (a : F) (x : A ⊗[R] V) :
    rightAction (algebraMap F E a) x = rightAction a x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b v =>
    change b ⊗ₜ[R] (algebraMap F E a • v) = b ⊗ₜ[R] (a • v)
    rw [IsScalarTower.algebraMap_smul]

omit [IsScalarTower R F E] in
lemma intertwines_fixedScalars
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (z : E) (hgen : Algebra.adjoin R ({z} : Set E) = ⊤)
    (hz : ∀ x, e (rightAction z x) = rightAction z (e x))
    (a : F) (x : A ⊗[R] V) : e (rightAction a x) = rightAction a (e x) := by
  have h := TensorEquivariant.intertwines_all e.toLinearMap z hgen hz
    (algebraMap F E a) x
  simpa only [rightAction_tower, LinearEquiv.coe_coe] using h

end
end MultiplicityCounterexample.FixedFieldBridge

namespace MultiplicityCounterexample.FixedFieldPrimitive
noncomputable section
variable (F : Type*) [Field F] [NumberField F]
lemma exists_primitive : ∃ z : F, Algebra.adjoin ℚ ({z} : Set F) = ⊤ := by
  obtain ⟨z, hz⟩ := Field.exists_primitive_element ℚ F
  refine ⟨z, ?_⟩
  have h := congrArg IntermediateField.toSubalgebra hz
  simpa only [IntermediateField.adjoin_toSubalgebra, IntermediateField.top_toSubalgebra] using h
end
end MultiplicityCounterexample.FixedFieldPrimitive

namespace MultiplicityCounterexample.CyclotomicPlaceComparison
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped NumberField
open TensorAlgebraModule FixedFieldLocalComparison NumberFieldTraceLocalComparison
variable {F E V W : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]
  [AddCommGroup V] [Module ℚ V] [Module F V] [Module E V]
  [IsScalarTower ℚ F V] [IsScalarTower ℚ E V] [IsScalarTower F E V]
  [AddCommGroup W] [Module ℚ W] [Module F W] [Module E W]
  [IsScalarTower ℚ F W] [IsScalarTower ℚ E W] [IsScalarTower F E W]

omit [NumberField F] [IsScalarTower ℚ F V] [IsScalarTower ℚ E V] in
lemma selfAdjointScalars_of_fixed_involution
    (σ : E ≃ₐ[ℚ] E) (hfix : ∀ a : F, σ (algebraMap F E a) = algebraMap F E a)
    (B : BilinForm ℚ V) (hB : TraceHermitian.AdjointRule σ B) :
    SelfAdjointScalars (F := F) B := by
  intro a x y
  have h := hB (algebraMap F E a) x y
  simpa only [hfix, IsScalarTower.algebraMap_smul] using h

def LocalEquivariantIsometry (A : Type*) [CommRing A] [Algebra ℚ A]
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W) (z : E) : Prop :=
  ∃ e : (A ⊗[ℚ] V) ≃ₗ[A] (A ⊗[ℚ] W),
    (∀ x, e (rightAction z x) = rightAction z (e x)) ∧
    (∀ x y, B₂.baseChange A (e x) (e y) = B₁.baseChange A x y)

lemma localTraceIsometry_of_cyclotomic
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : E) (hzgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (he : LocalEquivariantIsometry A B₁ B₂ z) (a : F) :
    LocalTraceIsometry A (fixedForm B₁ h₁) (fixedForm B₂ h₂) a := by
  obtain ⟨e, hz, hB⟩ := he
  exact localTraceIsometry_of_equivariant B₁ B₂ h₁ h₂ a e
    (FixedFieldBridge.intertwines_fixedScalars e z hzgen hz a) hB

theorem fixedForm_isometric_at_every_finitePlace
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : E) (hzgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (hloc : ∀ (p : ℕ) (_ : Fact p.Prime), LocalEquivariantIsometry (Padic p) B₁ B₂ z)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Nonempty (((fixedForm B₁ h₁).baseChange (v.adicCompletion F)).IsometryEquiv
      ((fixedForm B₂ h₂).baseChange (v.adicCompletion F))) := by
  obtain ⟨a, ha⟩ := FixedFieldPrimitive.exists_primitive F
  exact isometric_at_every_finitePlace (fixedForm B₁ h₁) (fixedForm B₂ h₂) a ha
    (fun p hp => localTraceIsometry_of_cyclotomic B₁ B₂ h₁ h₂ z hzgen (hloc p hp) a) v

theorem fixedForm_isometric_at_every_infinitePlace
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : E) (hzgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (hreal : LocalEquivariantIsometry ℝ B₁ B₂ z)
    (v : NumberField.InfinitePlace F) :
    Nonempty (((fixedForm B₁ h₁).baseChange v.Completion).IsometryEquiv
      ((fixedForm B₂ h₂).baseChange v.Completion)) := by
  obtain ⟨a, ha⟩ := FixedFieldPrimitive.exists_primitive F
  exact isometric_at_every_infinitePlace (fixedForm B₁ h₁) (fixedForm B₂ h₂) a ha
    (localTraceIsometry_of_cyclotomic B₁ B₂ h₁ h₂ z hzgen hreal a) v

end
end MultiplicityCounterexample.CyclotomicPlaceComparison

namespace MultiplicityCounterexample.TraceTowerCompatibility
noncomputable section
open LinearMap (BilinForm)
variable {R F E V : Type*} [Field R] [Field F] [Field E]
  [Algebra R F] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
  [FiniteDimensional R F] [FiniteDimensional F E] [FiniteDimensional R E]
  [Algebra.IsSeparable R F] [Algebra.IsSeparable R E]
  [AddCommGroup V] [Module R V] [Module F V] [Module E V]
  [IsScalarTower R F V] [IsScalarTower R E V] [IsScalarTower F E V]

theorem lift_fixed_eq_trace_lift (B : BilinForm R V) (x y : V) :
    TraceHermitian.lift (E := F) B x y =
      Algebra.trace F E (TraceHermitian.lift (E := E) B x y) := by
  apply TraceHermitian.trace_pairing_ext (F := R)
  intro a
  rw [TraceHermitian.trace_lift]
  calc
    B (a • x) y = B (algebraMap F E a • x) y := by rw [IsScalarTower.algebraMap_smul]
    _ = Algebra.trace R E (algebraMap F E a * TraceHermitian.lift B x y) :=
      (TraceHermitian.trace_lift B x y (algebraMap F E a)).symm
    _ = Algebra.trace R F (Algebra.trace F E
        (a • TraceHermitian.lift (E := E) B x y)) := by
      rw [Algebra.trace_trace, Algebra.smul_def]
    _ = Algebra.trace R F (a * Algebra.trace F E (TraceHermitian.lift (E := E) B x y)) := by
      rw [map_smul, smul_eq_mul]

theorem lift_fixed_diagonal (B : BilinForm R V) (x : V) (a : F)
    (hx : TraceHermitian.lift (E := E) B x x = algebraMap F E a)
    (hdim : Module.finrank F E = 2) :
    TraceHermitian.lift (E := F) B x x = 2 * a := by
  rw [lift_fixed_eq_trace_lift (E := E), hx, Algebra.trace_algebraMap, hdim]
  simp

end
end MultiplicityCounterexample.TraceTowerCompatibility

namespace MultiplicityCounterexample.LengthBaseChange
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
variable {F K V W : Type*} [Field F] [CharZero F] [Field K] [CharZero K] [Algebra F K]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def halfForm (B : BilinForm F V) : BilinForm F V := (2 : F)⁻¹ • B

def lengthForm (B : BilinForm F V) : QuadraticForm F V := (halfForm B).toQuadraticMap

omit [CharZero F] in
@[simp] lemma halfForm_apply (B : BilinForm F V) (x y : V) :
    halfForm B x y = (2 : F)⁻¹ * B x y := rfl

omit [CharZero F] in
@[simp] lemma lengthForm_apply (B : BilinForm F V) (x : V) :
    lengthForm B x = (2 : F)⁻¹ * B x x := rfl

omit [CharZero F] in
lemma halfForm_symmetric (B : BilinForm F V) (hs : B.IsSymm) : (halfForm B).IsSymm :=
  hs.smul _

lemma halfForm_nondegenerate (B : BilinForm F V) (hn : B.Nondegenerate) :
    (halfForm B).Nondegenerate := by
  constructor
  · intro x hx
    apply hn.1 x
    intro y
    have h := hx y
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
  · intro y hy
    apply hn.2 y
    intro x
    have h := hy x
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))

lemma lengthForm_nondegenerate (B : BilinForm F V) (hs : B.IsSymm) (hn : B.Nondegenerate) :
    (lengthForm B).Nondegenerate := by
  let : Invertible (2 : F) := invertibleOfNonzero (by norm_num)
  apply QuadraticMap.nondegenerate_associated_iff.mp
  have ha : (lengthForm B).associated = halfForm B :=
    QuadraticMap.associated_left_inverse F (halfForm_symmetric B hs).eq
  rw [ha]
  exact halfForm_nondegenerate B hn

omit [CharZero F] [CharZero K] in
lemma lengthForm_baseChange (B : BilinForm F V) [Invertible (2 : F)] :
    (lengthForm B).baseChange K = lengthForm (B.baseChange K) := by
  apply _root_.baseChange_ext
  intro x
  simp only [QuadraticForm.baseChange_tmul, lengthForm_apply,
    LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def,
    map_mul, map_inv₀, map_ofNat]

def lengthIsometryAtPlace (B₁ : BilinForm F V) (B₂ : BilinForm F W)
    [Invertible (2 : F)]
    (e : (B₁.baseChange K).IsometryEquiv (B₂.baseChange K)) :
    ((lengthForm B₁).baseChange K).IsometryEquiv ((lengthForm B₂).baseChange K) where
  __ := e.toLinearEquiv
  map_app' x := by
    change (lengthForm B₂).baseChange K (e x) = (lengthForm B₁).baseChange K x
    rw [lengthForm_baseChange, lengthForm_baseChange]
    simp only [lengthForm_apply, e.map_app]

end
end MultiplicityCounterexample.LengthBaseChange

namespace MultiplicityCounterexample.CyclotomicLengthLocalComparison
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped NumberField
open FixedFieldLocalComparison CyclotomicPlaceComparison LengthBaseChange
variable {F E V W : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsScalarTower ℚ F E]
  [AddCommGroup V] [Module ℚ V] [Module F V] [Module E V]
  [IsScalarTower ℚ F V] [IsScalarTower ℚ E V] [IsScalarTower F E V]
  [AddCommGroup W] [Module ℚ W] [Module F W] [Module E W]
  [IsScalarTower ℚ F W] [IsScalarTower ℚ E W] [IsScalarTower F E W]

def sourceLength (B : BilinForm ℚ V) (ha : SelfAdjointScalars (F := F) B) :
    QuadraticForm F V := lengthForm (fixedForm B ha)

theorem sourceLength_value (σ : E ≃ₐ[ℚ] E) (hσ : Function.Involutive σ)
    (hfixed : ∀ z : E, σ z = z → ∃ a : F, algebraMap F E a = z)
    (hdim : Module.finrank F E = 2)
    (B : BilinForm ℚ V) (ha : SelfAdjointScalars (F := F) B)
    (hs : B.IsSymm) (hadj : TraceHermitian.AdjointRule σ B) (x : V) :
    algebraMap F E (sourceLength B ha x) = TraceHermitian.lift (E := E) B x x := by
  have hd : σ (TraceHermitian.lift (E := E) B x x) = TraceHermitian.lift B x x :=
    (TraceHermitian.lift_symmetric σ hσ B hs hadj x x).symm
  obtain ⟨a, ha'⟩ := hfixed _ hd
  have ht := TraceTowerCompatibility.lift_fixed_diagonal B x a ha'.symm hdim
  simp only [sourceLength, lengthForm_apply, fixedForm_apply]
  rw [ht, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : F) ≠ 0), one_mul, ha']

theorem sourceLength_nondegenerate
    (B : BilinForm ℚ V) (ha : SelfAdjointScalars (F := F) B)
    (hs : B.IsSymm) (hn : B.Nondegenerate) : (sourceLength B ha).Nondegenerate :=
  lengthForm_nondegenerate _ (fixedForm_symmetric B ha hs) (fixedForm_nondegenerate B ha hn)

omit [IsScalarTower ℚ F E] in
theorem length_isometric_at_every_finitePlace
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : E) (hzgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (hloc : ∀ (p : ℕ) (_ : Fact p.Prime), LocalEquivariantIsometry (Padic p) B₁ B₂ z)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Nonempty (((sourceLength B₁ h₁).baseChange (v.adicCompletion F)).IsometryEquiv
      ((sourceLength B₂ h₂).baseChange (v.adicCompletion F))) := by
  obtain ⟨e⟩ := fixedForm_isometric_at_every_finitePlace B₁ B₂ h₁ h₂ z hzgen hloc v
  exact ⟨lengthIsometryAtPlace _ _ e⟩

omit [IsScalarTower ℚ F E] in
theorem length_isometric_at_every_infinitePlace
    (B₁ : BilinForm ℚ V) (B₂ : BilinForm ℚ W)
    (h₁ : SelfAdjointScalars (F := F) B₁) (h₂ : SelfAdjointScalars (F := F) B₂)
    (z : E) (hzgen : Algebra.adjoin ℚ ({z} : Set E) = ⊤)
    (hreal : LocalEquivariantIsometry ℝ B₁ B₂ z)
    (v : NumberField.InfinitePlace F) :
    Nonempty (((sourceLength B₁ h₁).baseChange v.Completion).IsometryEquiv
      ((sourceLength B₂ h₂).baseChange v.Completion)) := by
  obtain ⟨e⟩ := fixedForm_isometric_at_every_infinitePlace B₁ B₂ h₁ h₂ z hzgen hreal v
  exact ⟨lengthIsometryAtPlace _ _ e⟩
end
end MultiplicityCounterexample.CyclotomicLengthLocalComparison

end OAI
