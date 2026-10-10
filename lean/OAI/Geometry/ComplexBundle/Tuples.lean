import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Normalized Hermitian tuples, doubling, and unitary equivalence. -/

section
open scoped BigOperators ComplexOrder
namespace Kaplansky

/-- A normalized tuple with the adjoint identity proved for its displayed
reverse maps. No existence or topological obstruction is assumed here. -/
structure NormalizedHermitianTuple (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] where
  forward : Fin 24 → E →ₗ[ℂ] F
  reverse : Fin 24 → F →ₗ[ℂ] E
  adjoint_inner : ∀ i v w, inner ℂ (reverse i w) v = inner ℂ w (forward i v)
  column : ∑ i, (reverse i).comp (forward i) = LinearMap.id
  row : ∀ w, 0 ≤ inner ℂ w (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
    ∑ i, (forward i).comp (reverse i)) w)

namespace NormalizedHermitianTuple
variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Transport the actual tuple and its actual adjoints through unitary
coordinates. The row and column identities are preserved. -/
def congr (T : NormalizedHermitianTuple E F)
    (e : E ≃ₗᵢ[ℂ] E') (f : F ≃ₗᵢ[ℂ] F') : NormalizedHermitianTuple E' F' where
  forward i := f.toLinearEquiv.toLinearMap.comp ((T.forward i).comp e.symm.toLinearEquiv.toLinearMap)
  reverse i := e.toLinearEquiv.toLinearMap.comp ((T.reverse i).comp f.symm.toLinearEquiv.toLinearMap)
  adjoint_inner i v w := by
    change inner ℂ (e (T.reverse i (f.symm w))) v = inner ℂ w (f (T.forward i (e.symm v)))
    rw [← e.apply_symm_apply v, e.inner_map_map]
    rw [← f.apply_symm_apply w, f.inner_map_map]
    simp only [LinearIsometryEquiv.symm_apply_apply]
    exact T.adjoint_inner i (e.symm v) (f.symm w)
  column := by
    ext v
    have h := congrArg (fun a : E →ₗ[ℂ] E => e (a (e.symm v))) T.column
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sum, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using h
  row w := by
    have h := T.row (f.symm w)
    have he : inner ℂ w
        (((2/3 : ℂ) • (LinearMap.id : F' →ₗ[ℂ] F') -
          ∑ i, (f.toLinearEquiv.toLinearMap.comp ((T.forward i).comp e.symm.toLinearEquiv.toLinearMap)).comp
            (e.toLinearEquiv.toLinearMap.comp ((T.reverse i).comp f.symm.toLinearEquiv.toLinearMap))) w) =
        inner ℂ (f.symm w) (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
          ∑ i, (T.forward i).comp (T.reverse i)) (f.symm w)) := by
      rw [← f.inner_map_map]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.apply_symm_apply, map_sub, map_smul, map_sum]
    exact he ▸ h

/-- The reverse map is the unique adjoint, not an unconstrained witness. -/
theorem reverse_eq_adjoint [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : NormalizedHermitianTuple E F) (i : Fin 24) :
    T.reverse i = LinearMap.adjoint (T.forward i) := by
  ext w
  apply ext_inner_right ℂ
  intro v
  exact (T.adjoint_inner i v w).trans (LinearMap.adjoint_inner_left _ _ _).symm

end NormalizedHermitianTuple
end Kaplansky

end

section
open Bundle
namespace Kaplansky
variable {B : Type*} [TopologicalSpace B]

/-- A fiberwise unitary equivalence compatible with the actual total-space
topologies, even when the bundle models use different coordinates. -/
structure UnitaryBundleEquiv (U V : Type*) (E F : B → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)] where
  fiber : ∀ x, E x ≃ₗᵢ[ℂ] F x
  continuous_forward : Continuous (fun z : TotalSpace U E => TotalSpace.mk' V z.proj (fiber z.proj z.2))
  continuous_reverse : Continuous (fun z : TotalSpace V F => TotalSpace.mk' U z.proj ((fiber z.proj).symm z.2))

namespace UnitaryBundleEquiv
variable {U V W : Type*} {E F G : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [∀ x, NormedAddCommGroup (G x)] [∀ x, InnerProductSpace ℂ (G x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [TopologicalSpace (TotalSpace W G)]

def symm (e : UnitaryBundleEquiv U V E F) : UnitaryBundleEquiv V U F E where
  fiber x := (e.fiber x).symm
  continuous_forward := e.continuous_reverse
  continuous_reverse := e.continuous_forward

def trans (e : UnitaryBundleEquiv U V E F) (f : UnitaryBundleEquiv V W F G) :
    UnitaryBundleEquiv U W E G where
  fiber x := (e.fiber x).trans (f.fiber x)
  continuous_forward := f.continuous_forward.comp e.continuous_forward
  continuous_reverse := e.continuous_reverse.comp f.continuous_reverse
end UnitaryBundleEquiv

/-- The normalized maps and their true adjoints vary continuously over the
specified ordinary topological bundles. -/
structure ContinuousNormalizedStep (U V : Type*) (E F : B → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)] where
  tuple : ∀ x, NormalizedHermitianTuple (E x) (F x)
  continuous_forward : ∀ i, Continuous (fun z : TotalSpace U E =>
    TotalSpace.mk' V z.proj ((tuple z.proj).forward i z.2))
  continuous_reverse : ∀ i, Continuous (fun z : TotalSpace V F =>
    TotalSpace.mk' U z.proj ((tuple z.proj).reverse i z.2))

namespace ContinuousNormalizedStep
variable {U V U' V' : Type*} {E F E' F' : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
    [∀ x, NormedAddCommGroup (E' x)] [∀ x, InnerProductSpace ℂ (E' x)]
    [∀ x, NormedAddCommGroup (F' x)] [∀ x, InnerProductSpace ℂ (F' x)]
    [TopologicalSpace (TotalSpace U E)] [TopologicalSpace (TotalSpace V F)]
    [TopologicalSpace (TotalSpace U' E')] [TopologicalSpace (TotalSpace V' F')]

def congr (T : ContinuousNormalizedStep U V E F)
    (e : UnitaryBundleEquiv U U' E E') (f : UnitaryBundleEquiv V V' F F') :
    ContinuousNormalizedStep U' V' E' F' where
  tuple x := (T.tuple x).congr (e.fiber x) (f.fiber x)
  continuous_forward i := f.continuous_forward.comp ((T.continuous_forward i).comp e.continuous_reverse)
  continuous_reverse i := e.continuous_forward.comp ((T.continuous_reverse i).comp f.continuous_reverse)

end ContinuousNormalizedStep
end Kaplansky

end

open scoped BigOperators ComplexOrder
namespace Kaplansky

def twoOfTwentyFour {A : Type*} [Zero A] (a b : A) (i : Fin 24) : A :=
  if i=0 then a else if i=1 then b else 0

theorem sum_twoOfTwentyFour {A : Type*} [AddCommMonoid A] (a b : A) :
    ∑ i : Fin 24, twoOfTwentyFour a b i = a+b := by
  simp [twoOfTwentyFour, Finset.sum_ite, Finset.filter_eq']

def doublingScale : ℂ := (Real.sqrt (1/2 : ℝ) : ℂ)

theorem doublingScale_conj : star doublingScale = doublingScale := by simp [doublingScale]
theorem doublingScale_sq : doublingScale * doublingScale = (1/2 : ℂ) := by
  rw [doublingScale, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
  norm_num

/-- Two scaled orthogonal inclusions, padded by twenty-two zero maps.
These algebraic hypotheses are discharged by the actual sum coordinates. -/
def doublingTuple {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (I₀ I₁ : E →ₗ[ℂ] F) (P₀ P₁ : F →ₗ[ℂ] E)
    (h₀ : ∀ v w, inner ℂ (P₀ w) v = inner ℂ w (I₀ v))
    (h₁ : ∀ v w, inner ℂ (P₁ w) v = inner ℂ w (I₁ v))
    (hP₀ : P₀.comp I₀ = LinearMap.id) (hP₁ : P₁.comp I₁ = LinearMap.id)
    (hI : I₀.comp P₀ + I₁.comp P₁ = LinearMap.id) : NormalizedHermitianTuple E F where
  forward := twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁)
  reverse := twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁)
  adjoint_inner i v w := by
    by_cases hi : i=0
    · simp [twoOfTwentyFour,hi,inner_smul_left,inner_smul_right,doublingScale,h₀]
    · by_cases hj : i=1
      · simp [twoOfTwentyFour,hj,inner_smul_left,inner_smul_right,doublingScale,h₁]
      · simp [twoOfTwentyFour,hi,hj]
  column := by
    have he : (fun i => (twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁) i).comp
        (twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁) i)) =
        twoOfTwentyFour ((1/2 : ℂ) • LinearMap.id) ((1/2 : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) := by
      funext i
      by_cases hi : i=0
      · simp [twoOfTwentyFour,hi,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq,hP₀]
      · by_cases hj : i=1
        · simp [twoOfTwentyFour,hj,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq,hP₁]
        · simp [twoOfTwentyFour,hi,hj]
    rw [he,sum_twoOfTwentyFour,← add_smul]
    norm_num
  row w := by
    have he : (fun i => (twoOfTwentyFour (doublingScale • I₀) (doublingScale • I₁) i).comp
        (twoOfTwentyFour (doublingScale • P₀) (doublingScale • P₁) i)) =
        twoOfTwentyFour ((1/2 : ℂ) • I₀.comp P₀) ((1/2 : ℂ) • I₁.comp P₁) := by
      funext i
      by_cases hi : i=0
      · simp [twoOfTwentyFour,hi,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq]
      · by_cases hj : i=1
        · simp [twoOfTwentyFour,hj,LinearMap.smul_comp,LinearMap.comp_smul,smul_smul,doublingScale_sq]
        · simp [twoOfTwentyFour,hi,hj]
    rw [he,sum_twoOfTwentyFour,← smul_add,hI,← sub_smul]
    have hh : (2/3 : ℂ)-(1/2 : ℂ)=1/6 := by norm_num
    rw [hh,LinearMap.smul_apply,LinearMap.id_apply,inner_smul_right]
    exact mul_nonneg (by simp) (by simp)

end Kaplansky

end

end OAI
