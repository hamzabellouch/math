import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorEquiv
import OAI.Algebra.AuslanderReiten.Bar.BarScalarCoordinates
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar
import OAI.Algebra.AuslanderReiten.Bar.BarBalancedCompatibility

namespace OAI

noncomputable section
namespace ArExplicit.BarBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} R)

abbrev canonicalEvaluated (n : ℕ) :=
  BalancedTensor k R (EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) X

private def canonicalObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (canonicalEvaluated k R X n)

private def nativeObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (evaluated k R X n)

private def scalarEvaluatedObject (n : ℕ)
    (μ : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) : ModuleCat.{u} R := by
  letI := μ
  letI := τ
  exact ModuleCat.of R
    (BalancedTensor k R (EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) X)

private def scalarEvaluatedElement (n : ℕ)
    (μ : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (z : AbsoluteBar.moduleObject k R n) (x : X) : scalarEvaluatedObject k R X n μ τ := by
  letI := μ
  letI := τ
  exact BalancedTensor.tmul (EnvelopingBimodule.mk z) x

private theorem scalarEvaluatedObject_eq (n : ℕ)
    (μ ν : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (υ : letI := ν; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) (h : μ=ν) :
    scalarEvaluatedObject k R X n μ τ = scalarEvaluatedObject k R X n ν υ := by
  subst ν
  rfl

private theorem scalarEvaluatedElement_transport (n : ℕ)
    (μ ν : Module k (AbsoluteBar.moduleObject k R n))
    (τ : letI := μ; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (υ : letI := ν; IsScalarTower k (AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n)) (h : μ=ν)
    (z : AbsoluteBar.moduleObject k R n) (x : X) :
    (eqToIso (scalarEvaluatedObject_eq k R X n μ ν τ υ h)).hom
      (scalarEvaluatedElement k R X n μ τ z x) =
    scalarEvaluatedElement k R X n ν υ z x := by
  subst ν
  rfl

private theorem canonicalScalar_eq (n : ℕ) :
    moduleCatBaseModule (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n) = AbsoluteBar.baseModule k R n := by
  let := AbsoluteBar.baseModule k R n
  let := AbsoluteBar.bimoduleTower k R n
  exact ExternalTensor.canonicalScalar_eq k (AbsoluteBar.Enveloping k R)
    (AbsoluteBar.moduleObject k R n)

private theorem canonicalObject_eq (n : ℕ) : canonicalObject k R X n = nativeObject k R X n :=
  scalarEvaluatedObject_eq k R X n _ _
    (moduleCatBaseTower (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (AbsoluteBar.bimoduleTower k R n) (canonicalScalar_eq k R n)

def canonicalTransport (n : ℕ) : canonicalEvaluated k R X n ≃ₗ[R] evaluated k R X n :=
  (eqToIso (canonicalObject_eq k R X n)).toLinearEquiv

private def nativeElement (n : ℕ) (z : AbsoluteBar.moduleObject k R n) (x : X) :
    evaluated k R X n := by
  letI := AbsoluteBar.baseModule k R n
  letI := AbsoluteBar.bimoduleTower k R n
  exact BalancedTensor.tmul (EnvelopingBimodule.mk z) x

@[simp] theorem canonicalTransport_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) (x : X) :
    canonicalTransport k R X n (BalancedTensor.tmul z x) = nativeElement k R X n z.value x :=
  scalarEvaluatedElement_transport k R X n _ _
    (moduleCatBaseTower (k := k) (R := AbsoluteBar.Enveloping k R)
      (AbsoluteBar.moduleObject k R n))
    (AbsoluteBar.bimoduleTower k R n) (canonicalScalar_eq k R n) z.value x

def canonicalEquiv (n : ℕ) : canonicalEvaluated k R X n ≃ₗ[R] ModuleBar.moduleObject k R X n :=
  (canonicalTransport k R X n).trans (equiv k R X n)

@[simp] theorem canonicalEquiv_tmul (n : ℕ)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)) (x : X) :
    canonicalEquiv k R X n (BalancedTensor.tmul z x) =
      rawEval k R X n (z.value ⊗ₜ[k] x) := by
  change equiv k R X n (canonicalTransport k R X n (BalancedTensor.tmul z x)) = _
  rw [canonicalTransport_tmul]
  rfl

def canonicalMap {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n) :
    canonicalEvaluated k R X m →ₗ[R] canonicalEvaluated k R X n :=
  EnvelopingBimodule.tensorMap X f

@[simp] theorem canonicalMap_tmul {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (z : EnvelopingBimodule k R (AbsoluteBar.moduleObject k R m)) (x : X) :
    canonicalMap k R X f (BalancedTensor.tmul z x) =
      BalancedTensor.tmul (EnvelopingBimodule.map f z) x := rfl

/-- Establish compatibility at arbitrary degrees so induction does not unfold the
iterated tensor products in successor degrees. -/
private theorem canonicalEquiv_map {m n : ℕ}
    (f : AbsoluteBar.moduleObject k R m ⟶ AbsoluteBar.moduleObject k R n)
    (g : ModuleBar.moduleObject k R X m →ₗ[R] ModuleBar.moduleObject k R X n)
    (h : ∀ (a : AbsoluteBar.moduleObject k R m) (x : X),
      rawEval k R X n (f a ⊗ₜ[k] x) = g (rawEval k R X m (a ⊗ₜ[k] x)))
    (z : canonicalEvaluated k R X m) :
    canonicalEquiv k R X n (canonicalMap k R X f z) =
      g (canonicalEquiv k R X m z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a x =>
    rw [canonicalMap_tmul, canonicalEquiv_tmul, canonicalEquiv_tmul]
    exact h a.value x

theorem canonicalEquiv_differential (n : ℕ) (z : canonicalEvaluated k R X (n+1)) :
    canonicalEquiv k R X n
      (canonicalMap k R X (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
        (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n)) z) =
    ModuleBar.differential k R X n (canonicalEquiv k R X (n+1) z) := by
  exact canonicalEquiv_map k R X (m := n+1) (n := n)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n))
    (ModuleBar.differential k R X n) (rawEval_boundary k R X n) z

/-- Naming this morphism keeps kernel checking from repeatedly expanding the
iterated tensor-module structures at successor degrees. -/
abbrev cubicHom (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    AbsoluteBar.moduleObject k R (n+4) ⟶ AbsoluteBar.moduleObject k R (n+1) :=
  ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+4))
    (Y := AbsoluteBar.moduleObject k R (n+1)) (AbsoluteBar.suffixComparisonMap k R p n)

private theorem rawEval_cubic_compatibility (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (a : AbsoluteBar.moduleObject k R (n+4)) (x : X) :
    rawEval k R X (n+1) (cubicHom k R p n a ⊗ₜ[k] x) =
      ModuleBar.suffixComparisonMap k R X p n (rawEval k R X (n+4) (a ⊗ₜ[k] x)) :=
  rawEval_suffix k R X p (n+1) a x

theorem canonicalEquiv_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (z : canonicalEvaluated k R X (n+4)) :
    canonicalEquiv k R X (n+1)
      (canonicalMap k R X (cubicHom k R p n) z) =
    ModuleBar.suffixComparisonMap k R X p n (canonicalEquiv k R X (n+4) z) := by
  exact canonicalEquiv_map k R X (m := n+4) (n := n+1)
    (cubicHom k R p n) (ModuleBar.suffixComparisonMap k R X p n)
    (rawEval_cubic_compatibility k R X p n) z

end ArExplicit.BarBalanced

end

end OAI
