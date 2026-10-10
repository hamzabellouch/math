import Mathlib

namespace OAI

/-! Tensor scalar extension and trace-form descent. -/



namespace MultiplicityCounterexample.TensorAlgebraModule
noncomputable section
open TensorProduct
variable {F E V A : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    [CommRing A] [Algebra F A]

def rightAction : E →ₐ[F] Module.End A (A ⊗[F] V) :=
  (Module.End.baseChangeHom F A V).comp (Algebra.lsmul F F V)

def fullAction : (A ⊗[F] E) →ₐ[A] Module.End A (A ⊗[F] V) :=
  AlgHom.liftEquiv F A E _ rightAction

scoped instance module : Module (A ⊗[F] E) (A ⊗[F] V) :=
  Module.compHom _ (fullAction (F := F) (E := E) (V := V) (A := A)).toRingHom

open scoped TensorAlgebraModule

lemma smul_tmul_tmul (a b : A) (e : E) (v : V) :
    (a ⊗ₜ[F] e) • (b ⊗ₜ[F] v) = (a*b) ⊗ₜ[F] (e • v) := by
  change a • (b ⊗ₜ[F] (e • v)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul]

scoped instance fullTower : IsScalarTower A (A ⊗[F] E) (A ⊗[F] V) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a x
  change fullAction (algebraMap A (A ⊗[F] E) a) x = a • x
  rw [AlgHom.commutes]
  rfl

end
end MultiplicityCounterexample.TensorAlgebraModule

namespace MultiplicityCounterexample.CompletionFactorDescent
noncomputable section
open TensorProduct
open LinearMap (BilinForm)

section IsometryBaseChange
variable {R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def extendIsometry {B₁ : BilinForm R V} {B₂ : BilinForm R W}
    (e : B₁.IsometryEquiv B₂) : (B₁.baseChange S).IsometryEquiv (B₂.baseChange S) where
  __ := LinearEquiv.baseChange R S V W e.toLinearEquiv
  map_app' x y := by
    change B₂.baseChange S ((LinearEquiv.baseChange R S V W e.toLinearEquiv) x)
      ((LinearEquiv.baseChange R S V W e.toLinearEquiv) y) = _
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | tmul a v =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul b w =>
        change B₂.baseChange S (a ⊗ₜ[R] e v) (b ⊗ₜ[R] e w) = _
        simp only [LinearMap.BilinForm.baseChange_tmul, e.map_app]

@[simp] lemma extendIsometry_tmul {B₁ : BilinForm R V} {B₂ : BilinForm R W}
    (e : B₁.IsometryEquiv B₂) (a : S) (v : V) :
    extendIsometry (S := S) e (a ⊗ₜ[R] v) = a ⊗ₜ[R] e v := rfl

end IsometryBaseChange

section Tower
variable {R S K V : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [AddCommGroup V] [Module R V]

def cancelIsometry (B : BilinForm R V) :
    ((B.baseChange S).baseChange K).IsometryEquiv (B.baseChange K) where
  __ := TensorProduct.AlgebraTensorModule.cancelBaseChange R S K K V
  map_app' x y := by
    change B.baseChange K ((AlgebraTensorModule.cancelBaseChange R S K K V) x)
      ((AlgebraTensorModule.cancelBaseChange R S K K V) y) = _
    induction x using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul b y =>
        induction x using TensorProduct.inductionOn with
        | add x z hx hz => simp only [tmul_add, map_add, LinearMap.add_apply, hx, hz]
        | tmul c v =>
          induction y using TensorProduct.inductionOn with
          | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
          | tmul d w =>
            simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
              LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def,
              map_mul, ← IsScalarTower.algebraMap_apply R S K]
            ring

end Tower
section ScalarAlgebraComparison
variable {R A F V : Type*} [CommRing R] [CommRing A] [CommRing F]
  [Algebra R A] [Algebra R F]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]

open scoped TensorAlgebraModule
local instance scalarAlgebraRightAlgebra : Algebra F (A ⊗[R] F) :=
  Algebra.TensorProduct.rightAlgebra

def collapse : (A ⊗[R] F) ⊗[F] V →ₗ[A ⊗[R] F] A ⊗[R] V := by
  letI : Module F (A ⊗[R] V) := Module.compHom _ (algebraMap F (A ⊗[R] F))
  letI : IsScalarTower F (A ⊗[R] F) (A ⊗[R] V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let j : V →ₗ[F] A ⊗[R] V := {
    toFun := fun v => 1 ⊗ₜ[R] v
    map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
    map_smul' := fun f v => by
      change (1 : A) ⊗ₜ[R] (f • v) =
        ((1 : A) ⊗ₜ[R] f) • ((1 : A) ⊗ₜ[R] v)
      rw [TensorAlgebraModule.smul_tmul_tmul, one_mul] }
  exact j.liftBaseChange _

@[simp] lemma collapse_tmul (a : A) (f : F) (v : V) :
    collapse ((a ⊗ₜ[R] f) ⊗ₜ[F] v) = a ⊗ₜ[R] (f • v) := by
  change (a ⊗ₜ[R] f) • ((1 : A) ⊗ₜ[R] v) = _
  rw [TensorAlgebraModule.smul_tmul_tmul, mul_one]

def expand : A ⊗[R] V →ₗ[R] (A ⊗[R] F) ⊗[F] V :=
  TensorProduct.lift (((TensorProduct.mk F (A ⊗[R] F) V).restrictScalars₁₂ R R).comp
    (Algebra.TensorProduct.includeLeft (R := R) (A := A) (B := F)).toLinearMap)

@[simp] lemma expand_tmul (a : A) (v : V) :
    expand (a ⊗ₜ[R] v) = (a ⊗ₜ[R] (1 : F)) ⊗ₜ[F] v := rfl

lemma collapse_expand (x : A ⊗[R] V) : collapse (expand (F := F) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => simp
  | add x y hx hy => simp [hx, hy]

lemma expand_collapse (x : (A ⊗[R] F) ⊗[F] V) : expand (collapse x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul c v =>
    induction c using TensorProduct.inductionOn with
    | add c d hc hd => simp [add_tmul, hc, hd]
    | tmul a f =>
      rw [collapse_tmul, expand_tmul, ← TensorProduct.smul_tmul]
      congr 1
      change ((1 : A) ⊗ₜ[R] f) * (a ⊗ₜ[R] (1 : F)) = a ⊗ₜ[R] f
      simp

def scalarAlgebraEquiv : (A ⊗[R] F) ⊗[F] V ≃ₗ[A ⊗[R] F] A ⊗[R] V :=
  LinearEquiv.ofBijective collapse
    ⟨Function.LeftInverse.injective expand_collapse,
      Function.RightInverse.surjective collapse_expand⟩

@[simp] lemma scalarAlgebraEquiv_tmul (a : A) (f : F) (v : V) :
    scalarAlgebraEquiv ((a ⊗ₜ[R] f) ⊗ₜ[F] v) = a ⊗ₜ[R] (f • v) :=
  collapse_tmul (R := R) a f v

@[simp] lemma scalarAlgebraEquiv_symm_tmul (a : A) (v : V) :
    scalarAlgebraEquiv.symm (a ⊗ₜ[R] v) = (a ⊗ₜ[R] (1 : F)) ⊗ₜ[F] v := by
  apply scalarAlgebraEquiv.injective
  simp

def scalarAlgebraForm (B : BilinForm F V) :
    BilinForm (A ⊗[R] F) (A ⊗[R] V) :=
  BilinForm.congr scalarAlgebraEquiv (B.baseChange (A ⊗[R] F))

@[simp] lemma scalarAlgebraForm_tmul (B : BilinForm F V)
    (a b : A) (v w : V) :
    scalarAlgebraForm B (a ⊗ₜ[R] v) (b ⊗ₜ[R] w) = (a * b) ⊗ₜ[R] B v w := by
  simp only [scalarAlgebraForm, BilinForm.congr_apply, scalarAlgebraEquiv_symm_tmul,
    BilinForm.baseChange_tmul, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

def scalarAlgebraIsometry (B : BilinForm F V) :
    (B.baseChange (A ⊗[R] F)).IsometryEquiv (scalarAlgebraForm (R := R) (A := A) B) where
  __ := scalarAlgebraEquiv
  map_app' x y := by
    change BilinForm.congr scalarAlgebraEquiv (B.baseChange (A ⊗[R] F))
      (scalarAlgebraEquiv x) (scalarAlgebraEquiv y) = _
    simp

lemma scalarAlgebraForm_restrict (B : BilinForm F V) :
    (scalarAlgebraForm (R := R) (A := A) B).restrictScalars₁₂ A A =
      LinearMap.BilinMap.baseChange A (B.restrictScalars₁₂ R R) := by
  apply AlgebraTensorModule.ext
  intro a v
  apply AlgebraTensorModule.ext
  intro b w
  exact scalarAlgebraForm_tmul B a b v w

variable {W K : Type*} [AddCommGroup W] [Module R W] [Module F W]
  [IsScalarTower R F W] [CommRing K] [Algebra F K]
  [Algebra (A ⊗[R] F) K] [IsScalarTower F (A ⊗[R] F) K]

def descendIsometry {B₁ : BilinForm F V} {B₂ : BilinForm F W}
    (e : (scalarAlgebraForm (R := R) (A := A) B₁).IsometryEquiv
      (scalarAlgebraForm (R := R) (A := A) B₂)) :
    (B₁.baseChange K).IsometryEquiv (B₂.baseChange K) :=
  (cancelIsometry (S := A ⊗[R] F) B₁).symm.trans
    ((extendIsometry (S := K)
      ((scalarAlgebraIsometry B₁).trans (e.trans (scalarAlgebraIsometry B₂).symm))).trans
      (cancelIsometry B₂))

end ScalarAlgebraComparison

variable {R A F K V W : Type*} [CommRing R] [CommRing A] [CommRing F] [CommRing K]
  [Algebra R A] [Algebra R F] [Algebra R K] [Algebra A K] [Algebra F K]
  [IsScalarTower R A K] [IsScalarTower R F K]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]
  [AddCommGroup W] [Module R W] [Module F W] [IsScalarTower R F W]

open scoped TensorAlgebraModule
local instance completionMapRightAlgebra : Algebra F (A ⊗[R] F) :=
  Algebra.TensorProduct.rightAlgebra

def factorMap : (A ⊗[R] F) →ₐ[R] K :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A K) (IsScalarTower.toAlgHom R F K)
    (fun _ _ => Commute.all _ _)

@[simp] lemma factorMap_tmul (a : A) (f : F) :
    factorMap (a ⊗ₜ[R] f) = algebraMap A K a * algebraMap F K f := rfl

def descendAlongPlace {B₁ : BilinForm F V} {B₂ : BilinForm F W}
    (e : (scalarAlgebraForm (R := R) (A := A) B₁).IsometryEquiv
      (scalarAlgebraForm (R := R) (A := A) B₂)) :
    (B₁.baseChange K).IsometryEquiv (B₂.baseChange K) := by
  letI : Algebra (A ⊗[R] F) K := (factorMap (R := R) (A := A) (F := F) (K := K)).toRingHom.toAlgebra
  letI : IsScalarTower F (A ⊗[R] F) K := IsScalarTower.of_algebraMap_eq (fun f => by
    change algebraMap F K f = factorMap ((1 : A) ⊗ₜ[R] f)
    simp)
  exact descendIsometry e


end
end MultiplicityCounterexample.CompletionFactorDescent

namespace MultiplicityCounterexample.TraceBaseChange
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Type*) [CommRing A] [Algebra F A]

def perfectBase (B : BilinForm F V) (hB : B.Nondegenerate) :
    (A ⊗[F] V) ≃ₗ[A] Module.Dual A (A ⊗[F] V) :=
  (LinearEquiv.baseChange F A V _ (B.toDual hB)).trans
    (TensorProduct.isBaseChange F V A).toDualBaseChange

lemma dualBase_tmul (a b : A) (f : Module.Dual F V) (v : V) :
    (TensorProduct.isBaseChange F V A).toDualBaseChange (a ⊗ₜ[F] f) (b ⊗ₜ[F] v) =
      b * (a * algebraMap F A (f v)) := by
  have h : b ⊗ₜ[F] v = b • (1 ⊗ₜ[F] v) := by simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul]
  change b * _ = _
  congr 1
  exact (TensorProduct.isBaseChange F V A).toDualBaseChange_tmul a f v

lemma perfectBase_apply (B : BilinForm F V) (hB : B.Nondegenerate)
    (x y : A ⊗[F] V) : perfectBase A B hB x y = B.baseChange A x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b w =>
      change (TensorProduct.isBaseChange F V A).toDualBaseChange
        ((LinearEquiv.baseChange F A V _ (B.toDual hB)) (a ⊗ₜ[F] v)) (b ⊗ₜ[F] w) = _
      rw [LinearEquiv.baseChange_tmul, dualBase_tmul, BilinForm.baseChange_tmul]
      rw [BilinForm.toDual_def, Algebra.smul_def]
      ring

lemma baseChange_nondegenerate (B : BilinForm F V) (hB : B.Nondegenerate) :
    (B.baseChange A).Nondegenerate := by
  constructor
  · intro x hx
    apply (perfectBase A B hB).injective
    apply LinearMap.ext
    intro y
    simpa [perfectBase_apply] using hx y
  · intro y hy
    have h : ∀ f : Module.Dual A (A ⊗[F] V), f y = 0 := by
      intro f
      obtain ⟨x, rfl⟩ := (perfectBase A B hB).surjective f
      simpa [perfectBase_apply] using hy x
    exact (Module.forall_dual_apply_eq_zero_iff A y).mp h

variable {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E]

lemma trace_one_tmul (x : E) :
    Algebra.trace A (A ⊗[F] E) (1 ⊗ₜ[F] x) =
      algebraMap F A (Algebra.trace F E x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  rfl

lemma trace_tmul (a : A) (x : E) :
    Algebra.trace A (A ⊗[F] E) (a ⊗ₜ[F] x) =
      a * algebraMap F A (Algebra.trace F E x) := by
  have h : a ⊗ₜ[F] x = a • (1 ⊗ₜ[F] x) := by simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, trace_one_tmul, smul_eq_mul]

lemma traceForm_baseChange :
    Algebra.traceForm A (A ⊗[F] E) = (Algebra.traceForm F E).baseChange A := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, hx, hz]
  | tmul a v =>
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b w =>
      simp only [Algebra.traceForm_apply, Algebra.TensorProduct.tmul_mul_tmul,
        trace_tmul, BilinForm.baseChange_tmul, Algebra.smul_def]
      ring

variable [Algebra.IsSeparable F E]
lemma traceForm_nondegenerate_baseChange :
    (Algebra.traceForm A (A ⊗[F] E)).Nondegenerate := by
  rw [traceForm_baseChange]
  exact baseChange_nondegenerate A _ (traceForm_nondegenerate F E)

def traceDual : (A ⊗[F] E) ≃ₗ[A] Module.Dual A (A ⊗[F] E) :=
  perfectBase A (Algebra.traceForm F E) (traceForm_nondegenerate F E)

lemma traceDual_apply (x y : A ⊗[F] E) :
    traceDual A x y = Algebra.trace A (A ⊗[F] E) (x * y) := by
  rw [traceDual, perfectBase_apply, ← traceForm_baseChange, Algebra.traceForm_apply]

lemma trace_pairing_ext {x y : A ⊗[F] E}
    (h : ∀ a, Algebra.trace A (A ⊗[F] E) (a*x) =
      Algebra.trace A (A ⊗[F] E) (a*y)) : x = y := by
  apply (traceDual A).injective
  apply LinearMap.ext
  intro a
  simpa only [traceDual_apply, mul_comm] using h a

variable {W W' : Type*} [AddCommGroup W] [Module A W]
    [Module (A ⊗[F] E) W] [IsScalarTower A (A ⊗[F] E) W]
    [AddCommGroup W'] [Module A W'] [Module (A ⊗[F] E) W']
    [IsScalarTower A (A ⊗[F] E) W']

def traceFunctional (B : BilinForm A W) (x y : W) : Module.Dual A (A ⊗[F] E) where
  toFun a := B (a • x) y
  map_add' a b := by simp only [add_smul, map_add, LinearMap.add_apply]
  map_smul' a b := by
    simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply]

def lift (B : BilinForm A W) (x y : W) : A ⊗[F] E :=
  (traceDual A).symm (traceFunctional A B x y)

lemma trace_lift (B : BilinForm A W) (x y : W) (a : A ⊗[F] E) :
    Algebra.trace A (A ⊗[F] E) (a * lift (F := F) (E := E) A B x y) = B (a • x) y := by
  rw [mul_comm, ← traceDual_apply]
  exact DFunLike.congr_fun ((traceDual A).apply_symm_apply (traceFunctional A B x y)) a

lemma trace_lift_one (B : BilinForm A W) (x y : W) :
    Algebra.trace A (A ⊗[F] E) (lift (F := F) (E := E) A B x y) = B x y := by
  simpa using trace_lift (F := F) (E := E) A B x y 1

lemma lift_add_left (B : BilinForm A W) (x y z : W) :
    lift (F := F) (E := E) A B (x+y) z = lift (F := F) (E := E) A B x z + lift (F := F) (E := E) A B y z := by
  apply trace_pairing_ext A
  intro a
  simp only [mul_add, map_add, trace_lift, smul_add, LinearMap.add_apply]

lemma lift_add_right (B : BilinForm A W) (x y z : W) :
    lift (F := F) (E := E) A B x (y+z) = lift (F := F) (E := E) A B x y + lift (F := F) (E := E) A B x z := by
  apply trace_pairing_ext A
  intro a
  simp only [mul_add, map_add, trace_lift]

lemma lift_smul_left (B : BilinForm A W) (a : A ⊗[F] E) (x y : W) :
    lift (F := F) (E := E) A B (a • x) y = a * lift (F := F) (E := E) A B x y := by
  apply trace_pairing_ext A
  intro b
  rw [trace_lift, ← mul_assoc, trace_lift, mul_smul]

theorem preserves_iff (B : BilinForm A W) (C : BilinForm A W')
    (e : W ≃ₗ[A ⊗[F] E] W') :
    (∀ x y, C (e x) (e y) = B x y) ↔
      ∀ x y, lift (F := F) (E := E) A C (e x) (e y) = lift (F := F) (E := E) A B x y := by
  constructor
  · intro he x y
    apply trace_pairing_ext A
    intro a
    rw [trace_lift, trace_lift, ← e.map_smul, he]
  · intro he x y
    rw [← trace_lift_one (F := F) (E := E) A, ← trace_lift_one (F := F) (E := E) A, he]

lemma lift_unique (B : BilinForm A W) (h : W → W → A ⊗[F] E)
    (hh : ∀ a x y, Algebra.trace A (A ⊗[F] E) (a * h x y) = B (a • x) y) :
    h = lift (F := F) (E := E) A B := by
  funext x y
  apply trace_pairing_ext A
  intro a
  rw [hh, trace_lift]

end
end MultiplicityCounterexample.TraceBaseChange

namespace MultiplicityCounterexample.TensorEquivariant
noncomputable section
open TensorProduct
open TensorAlgebraModule
open scoped TensorAlgebraModule
variable {F E V W A : Type*} [CommRing F] [CommRing E] [Algebra F E]
    [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    [AddCommGroup W] [Module F W] [Module E W] [IsScalarTower F E W]
    [CommRing A] [Algebra F A]

lemma rightAction_algebraMap (r : F) (x : A ⊗[F] V) :
    rightAction (algebraMap F E r) x = r • x := by
  rw [AlgHom.commutes]
  rfl

def intertwiningScalars (f : (A ⊗[F] V) →ₗ[A] (A ⊗[F] W)) : Subalgebra F E where
  carrier := {e | ∀ x, f (rightAction e x) = rightAction e (f x)}
  zero_mem' := by intro x; simp
  one_mem' := by intro x; simp
  add_mem' ha hb := by
    intro x
    simp only [map_add, LinearMap.add_apply]
    exact congrArg₂ (· + ·) (ha x) (hb x)
  mul_mem' ha hb := by
    intro x
    simp only [map_mul, Module.End.mul_apply]
    exact (ha _).trans (congrArg _ (hb x))
  algebraMap_mem' r := by
    intro x
    rw [rightAction_algebraMap, rightAction_algebraMap]
    exact f.map_smul_of_tower r x

lemma intertwines_all (f : (A ⊗[F] V) →ₗ[A] (A ⊗[F] W))
    (z : E) (hgen : Algebra.adjoin F ({z} : Set E) = ⊤)
    (hz : ∀ x, f (rightAction z x) = rightAction z (f x))
    (e : E) (x : A ⊗[F] V) : f (rightAction e x) = rightAction e (f x) := by
  have hle : Algebra.adjoin F ({z} : Set E) ≤ intertwiningScalars f := by
    apply Algebra.adjoin_le
    intro a ha
    obtain rfl : a=z := Set.mem_singleton_iff.mp ha
    exact hz
  rw [hgen] at hle
  exact hle (show e ∈ (⊤ : Subalgebra F E) from trivial) x

lemma map_smul_tensor (f : (A ⊗[F] V) →ₗ[A] (A ⊗[F] W))
    (z : E) (hgen : Algebra.adjoin F ({z} : Set E) = ⊤)
    (hz : ∀ x, f (rightAction z x) = rightAction z (f x))
    (a : A ⊗[F] E) (x : A ⊗[F] V) : f (a • x) = a • f x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_smul, map_add, ha, hb]
  | tmul a e =>
    change f (a • rightAction e x) = a • rightAction e (f x)
    rw [map_smul, intertwines_all f z hgen hz]

def linearOverTensor (f : (A ⊗[F] V) →ₗ[A] (A ⊗[F] W))
    (z : E) (hgen : Algebra.adjoin F ({z} : Set E) = ⊤)
    (hz : ∀ x, f (rightAction z x) = rightAction z (f x)) :
    (A ⊗[F] V) →ₗ[A ⊗[F] E] (A ⊗[F] W) where
  toAddHom := f.toAddHom
  map_smul' a x := map_smul_tensor f z hgen hz a x

def equivOverTensor (f : (A ⊗[F] V) ≃ₗ[A] (A ⊗[F] W))
    (z : E) (hgen : Algebra.adjoin F ({z} : Set E) = ⊤)
    (hz : ∀ x, f (rightAction z x) = rightAction z (f x)) :
    (A ⊗[F] V) ≃ₗ[A ⊗[F] E] (A ⊗[F] W) :=
  LinearEquiv.ofBijective (linearOverTensor f.toLinearMap z hgen hz) f.bijective

end
end MultiplicityCounterexample.TensorEquivariant

namespace MultiplicityCounterexample.CompletionTraceDescent
noncomputable section
open TensorProduct
open LinearMap (BilinForm)
open scoped MultiplicityCounterexample.TensorAlgebraModule
open CompletionFactorDescent
variable {R F A V W : Type*} [Field R] [Field F] [Algebra R F]
  [FiniteDimensional R F] [Algebra.IsSeparable R F]
  [CommRing A] [Algebra R A]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]
  [AddCommGroup W] [Module R W] [Module F W] [IsScalarTower R F W]
local instance traceDescentRightAlgebra : Algebra F (A ⊗[R] F) :=
  Algebra.TensorProduct.rightAlgebra

def traceForm (B : BilinForm F V) : BilinForm R V where
  toFun x :=
    { toFun := fun y => Algebra.trace R F (B x y)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

omit [FiniteDimensional R F] [Algebra.IsSeparable R F] in
@[simp] lemma traceForm_apply (B : BilinForm F V) (x y : V) :
    traceForm (R := R) B x y = Algebra.trace R F (B x y) := rfl

omit [Algebra.IsSeparable R F] in
lemma trace_scalarAlgebraForm (B : BilinForm F V) (x y : A ⊗[R] V) :
    Algebra.trace A (A ⊗[R] F) (scalarAlgebraForm (R := R) (A := A) B x y) =
      (traceForm (R := R) B).baseChange A x y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b w =>
      simp only [scalarAlgebraForm_tmul, TraceBaseChange.trace_tmul,
        LinearMap.BilinForm.baseChange_tmul, traceForm_apply, Algebra.smul_def]
      ring

def scalarIsometryOfTrace (B₁ : BilinForm F V) (B₂ : BilinForm F W)
    (e : (A ⊗[R] V) ≃ₗ[A ⊗[R] F] (A ⊗[R] W))
    (he : ∀ x y, (traceForm (R := R) B₂).baseChange A (e x) (e y) =
      (traceForm (R := R) B₁).baseChange A x y) :
    (scalarAlgebraForm (R := R) (A := A) B₁).IsometryEquiv (scalarAlgebraForm (R := R) (A := A) B₂) where
  __ := e
  map_app' x y := by
    change scalarAlgebraForm (R := R) (A := A) B₂ (e x) (e y) =
      scalarAlgebraForm (R := R) (A := A) B₁ x y
    apply TraceBaseChange.trace_pairing_ext A
    intro c
    have h₂ : c * scalarAlgebraForm (R := R) (A := A) B₂ (e x) (e y) =
        scalarAlgebraForm (R := R) (A := A) B₂ (e (c • x)) (e y) := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have h₁ : c * scalarAlgebraForm (R := R) (A := A) B₁ x y =
        scalarAlgebraForm (R := R) (A := A) B₁ (c • x) y := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [h₂, h₁, trace_scalarAlgebraForm, trace_scalarAlgebraForm, he]

variable {K : Type*} [CommRing K] [Algebra R K] [Algebra A K] [Algebra F K]
  [IsScalarTower R A K] [IsScalarTower R F K]

def descendTraceAtPlace (B₁ : BilinForm F V) (B₂ : BilinForm F W)
    (z : F) (hzgen : Algebra.adjoin R ({z} : Set F) = ⊤)
    (e : (A ⊗[R] V) ≃ₗ[A] (A ⊗[R] W))
    (hz : ∀ x, e (TensorAlgebraModule.rightAction z x) =
      TensorAlgebraModule.rightAction z (e x))
    (he : ∀ x y, (traceForm (R := R) B₂).baseChange A (e x) (e y) =
      (traceForm (R := R) B₁).baseChange A x y) :
    (B₁.baseChange K).IsometryEquiv (B₂.baseChange K) :=
  descendAlongPlace (scalarIsometryOfTrace B₁ B₂
    (TensorEquivariant.equivOverTensor e z hzgen hz) he)

end
end MultiplicityCounterexample.CompletionTraceDescent

end OAI
