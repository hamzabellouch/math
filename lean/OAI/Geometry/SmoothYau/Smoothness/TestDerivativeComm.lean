import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev smoothScalarAlgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Subalgebra ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  algebraMap_mem' c := by change ContDiff ℝ ∞ (fun _ : E => c); exact contDiff_const
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  one_mem' := by change ContDiff ℝ ∞ (fun _ : E => (1 : ℝ)); exact contDiff_const
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.mul hg

abbrev SmoothScalar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  smoothScalarAlgebra E

namespace SmoothScalar
instance : CoeFun (SmoothScalar E) (fun _ => E → ℝ) := ⟨Subtype.val⟩
lemma contDiff (f : SmoothScalar E) : ContDiff ℝ ∞ (f : E → ℝ) := f.property
variable (v : E)
def directional : SmoothScalar E →ₗ[ℝ] SmoothScalar E where
  toFun f := ⟨fun x => fderiv ℝ (f : E → ℝ) x v,
    by
      change ContDiff ℝ ∞ (fun x => fderiv ℝ (f : E → ℝ) x v)
      exact ((SmoothScalar.contDiff f).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp only [Subalgebra.coe_add, Pi.add_apply,
      fderiv_add ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt
        ((SmoothScalar.contDiff g).differentiable (by simp)).differentiableAt,
      add_apply]
  map_smul' c f := by
    apply Subtype.ext
    ext x
    simp only [Subalgebra.coe_smul, Pi.smul_apply,
      fderiv_const_smul ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt,
      smul_apply, RingHom.id_apply]

@[simp] lemma directional_apply (f : SmoothScalar E) (x : E) :
    directional v f x = fderiv ℝ (f : E → ℝ) x v := rfl
lemma directional_mul (f g : SmoothScalar E) :
    directional v (f * g) = directional v f * g + f * directional v g := by
  apply Subtype.ext
  ext x
  change fderiv ℝ ((f : E → ℝ) * (g : E → ℝ)) x v = _
  rw [fderiv_mul ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt
    ((SmoothScalar.contDiff g).differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply,
    smul_eq_mul, Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply,
    directional_apply]
  ring
end SmoothScalar

variable (K : Compacts E)
abbrev EllipticTest := 𝓓_{K}(E, ℝ)
def testDerivative (v : E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (ContDiffMapSupportedIn.postcompLM (ContinuousLinearMap.apply ℝ ℝ v)).comp
    (ContDiffMapSupportedIn.fderivLM ℝ ⊤ ⊤)

@[simp] lemma testDerivative_apply (v : E) (f : EllipticTest K) (x : E) :
    testDerivative K v f x = fderiv ℝ f x v := by
  simp [testDerivative]

def testMultiply (a : SmoothScalar E) : EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) (SmoothScalar.contDiff a)).toLinearMap
@[simp] lemma testMultiply_apply (a : SmoothScalar E) (f : EllipticTest K) (x : E) :
    testMultiply K a f x = a x * f x := by dsimp [testMultiply]; ring

lemma testProductRule (v : E) (a : SmoothScalar E) (f : EllipticTest K) :
    testDerivative K v (testMultiply K a f) =
      testMultiply K (SmoothScalar.directional v a) f + testMultiply K a (testDerivative K v f) := by
  ext x
  have he : (testMultiply K a f : E → ℝ) = fun x => a x * f x := by ext y; simp
  simp only [testDerivative_apply, he]
  change fderiv ℝ ((a : E → ℝ) * (f : E → ℝ)) x v = _
  rw [fderiv_mul ((SmoothScalar.contDiff a).differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul,
    testMultiply_apply, SmoothScalar.directional_apply,
    testDerivative_apply]
  ring

lemma testMultiply_add (a b : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (a + b) f = testMultiply K a f + testMultiply K b f := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_add, Pi.add_apply, add_apply, add_mul]
lemma testMultiply_smul (c : ℝ) (a : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (c • a) f = c • testMultiply K a f := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_smul, Pi.smul_apply, smul_apply, smul_eq_mul, mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma testPair_integrable (f g : EllipticTest K) :
    Integrable (fun x => f x * g x) (volume : Measure E) :=
  (f.contDiff.continuous.mul g.contDiff.continuous).integrable_of_hasCompactSupport
    (f.compact_supp.mul_right)

def testPair (f g : EllipticTest K) : ℝ := ∫ x, f x * g x

lemma testPair_comm (f g : EllipticTest K) : testPair K f g = testPair K g f := by
  simp only [testPair, mul_comm]
lemma testPair_add_left (f g h : EllipticTest K) :
    testPair K (f + g) h = testPair K f h + testPair K g h := by
  simp only [testPair, FunLike.coe_add, Pi.add_apply, add_mul]
  exact integral_add (testPair_integrable K f h) (testPair_integrable K g h)
lemma testPair_smul_left (c : ℝ) (f g : EllipticTest K) :
    testPair K (c • f) g = c * testPair K f g := by
  simp only [testPair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
lemma testPair_nonneg (f : EllipticTest K) : 0 ≤ testPair K f f :=
  integral_nonneg (fun _ => mul_self_nonneg _)

lemma testDerivative_skew (v : E) (f g : EllipticTest K) :
    testPair K (testDerivative K v f) g = -testPair K f (testDerivative K v g) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure E)) (v := v) (f := (f : E → ℝ)) (g := (g : E → ℝ))
    (testPair_integrable K (testDerivative K v f) g)
    (testPair_integrable K f (testDerivative K v g))
    (testPair_integrable K f g)
    (fun x _ => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _ => (g.contDiff.differentiable (by simp)).differentiableAt)
  change testPair K f (testDerivative K v g) = -testPair K (testDerivative K v f) g at h
  linarith

lemma testMultiply_symmetric (a : SmoothScalar E) (f g : EllipticTest K) :
    testPair K (testMultiply K a f) g = testPair K f (testMultiply K a g) := by
  unfold testPair
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [testMultiply_apply]
  ring

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E)

lemma testDerivative_comm (v w : E) (f : EllipticTest K) :
    testDerivative K v (testDerivative K w f) = testDerivative K w (testDerivative K v f) := by
  ext x
  have hdf := (f.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hfun (z : E) : (testDerivative K z f : E → ℝ) = fun y => fderiv ℝ f y z := by
    ext y; rfl
  simp only [testDerivative_apply, hfun,
    fderiv_clm_apply hdf.differentiableAt (differentiableAt_const w),
    fderiv_clm_apply hdf.differentiableAt (differentiableAt_const v)]
  simpa using (f.contDiff.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))).eq v w

lemma testMultiply_mul (a b : SmoothScalar E) (f : EllipticTest K) :
    testMultiply K (a * b) f = testMultiply K a (testMultiply K b f) := by
  ext x
  simp only [testMultiply_apply, Subalgebra.coe_mul, Pi.mul_apply, mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma testPair_add_right (f g h : EllipticTest K) :
    testPair K f (g + h) = testPair K f g + testPair K f h := by
  rw [testPair_comm, testPair_add_left, testPair_comm K g, testPair_comm K h]
lemma testPair_smul_right (c : ℝ) (f g : EllipticTest K) :
    testPair K f (c • g) = c * testPair K f g := by
  rw [testPair_comm, testPair_smul_left, testPair_comm]
@[simp] lemma testPair_zero_left (f : EllipticTest K) : testPair K 0 f = 0 := by simp [testPair]
@[simp] lemma testPair_zero_right (f : EllipticTest K) : testPair K f 0 = 0 := by simp [testPair]
lemma testPair_neg_left (f g : EllipticTest K) : testPair K (-f) g = -testPair K f g := by
  simpa only [neg_one_smul, neg_one_mul] using testPair_smul_left K (-1) f g
lemma testPair_neg_right (f g : EllipticTest K) : testPair K f (-g) = -testPair K f g := by
  rw [testPair_comm, testPair_neg_left, testPair_comm]
lemma testPair_sub_left (f g h : EllipticTest K) :
    testPair K (f-g) h = testPair K f h - testPair K g h := by
  simp only [sub_eq_add_neg, testPair_add_left, testPair_neg_left]
lemma testPair_sub_right (f g h : EllipticTest K) :
    testPair K f (g-h) = testPair K f g - testPair K f h := by
  simp only [sub_eq_add_neg, testPair_add_right, testPair_neg_right]
lemma testPair_sum_left {ι : Type*} (s : Finset ι) (f : ι → EllipticTest K) (g : EllipticTest K) :
    testPair K (∑ i ∈ s, f i) g = ∑ i ∈ s, testPair K (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, testPair_add_left, ih]
lemma testPair_sum_right {ι : Type*} (s : Finset ι) (f : EllipticTest K) (g : ι → EllipticTest K) :
    testPair K f (∑ i ∈ s, g i) = ∑ i ∈ s, testPair K f (g i) := by
  rw [testPair_comm, testPair_sum_left]
  congr 1
  ext i
  exact testPair_comm K _ _

lemma testPair_weighted_derivative (a : SmoothScalar E) (v : E) (f g : EllipticTest K) :
    testPair K (testMultiply K a (testDerivative K v f)) g +
      testPair K (testMultiply K a f) (testDerivative K v g) =
      -testPair K (testMultiply K (SmoothScalar.directional v a) f) g := by
  have h := testDerivative_skew K v (testMultiply K a f) g
  rw [testProductRule, testPair_add_left] at h
  linarith

lemma testPair_weighted_self_derivative (a : SmoothScalar E) (v : E) (f : EllipticTest K) :
    2 * testPair K (testMultiply K a f) (testDerivative K v f) =
      -testPair K (testMultiply K (SmoothScalar.directional v a) f) f := by
  have h := testPair_weighted_derivative K a v f f
  rw [testMultiply_symmetric, testPair_comm K (testDerivative K v f)] at h
  linarith



end YauCounterexamples
end

end OAI
