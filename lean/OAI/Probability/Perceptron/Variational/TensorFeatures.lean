import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

abbrev NormalizedSpin (N : ℕ) := Metric.sphere (0 : Spin N) 1
abbrev SpinTensorIndex (N p : ℕ) := Fin p → Fin N

def spinTensorFeature (N p : ℕ) (x : NormalizedSpin N) :
    EuclideanSpace ℝ (SpinTensorIndex N p) :=
  WithLp.toLp 2 (fun i => ∏ j, x.val (i j))

def spinOverlap {N : ℕ} (x y : NormalizedSpin N) : ℝ := inner ℝ x.val y.val

lemma spinTensorFeature_continuous (N p : ℕ) : Continuous (spinTensorFeature N p) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact continuous_finsetProd _ fun j _ =>
    (EuclideanSpace.proj (i j)).continuous.comp continuous_subtype_val

lemma spinTensorFeature_inner (N p : ℕ) (x y : NormalizedSpin N) :
    inner ℝ (spinTensorFeature N p x) (spinTensorFeature N p y) =
      spinOverlap x y ^ p := by
  change (∑ i : SpinTensorIndex N p, (∏ j, y.val (i j)) * (∏ j, x.val (i j))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (i : Fin N) => y.val i*x.val i)]
  change (∏ _ : Fin p, spinOverlap x y) = spinOverlap x y ^ p
  simp

lemma spinTensorFeature_norm (N p : ℕ) (x : NormalizedSpin N) :
    ‖spinTensorFeature N p x‖ = 1 := by
  have hx : ‖x.val‖=1 := by simp
  have h := spinTensorFeature_inner N p x x
  rw [real_inner_self_eq_norm_sq] at h
  simp only [spinOverlap,real_inner_self_eq_norm_sq,hx,one_pow] at h
  nlinarith [norm_nonneg (spinTensorFeature N p x)]

lemma spinTensorFeature_coordinate_bound (N p : ℕ) (x : NormalizedSpin N)
    (i : SpinTensorIndex N p) : |spinTensorFeature N p x i| ≤ 1 := by
  calc
    _ ≤ ‖spinTensorFeature N p x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (spinTensorFeature N p x) i
    _ = 1 := spinTensorFeature_norm N p x

lemma spinOverlap_abs_le {N : ℕ} (x y : NormalizedSpin N) : |spinOverlap x y| ≤ 1 := by
  have hx : ‖x.val‖=1 := by simp
  have hy : ‖y.val‖=1 := by simp
  simpa [spinOverlap,hx,hy] using abs_real_inner_le_norm x.val y.val

abbrev EnrichedIndex (N J : ℕ) (p : Fin J → ℕ) :=
  Fin N ⊕ (j : Fin J) × SpinTensorIndex N (p j)
abbrev EnrichedMark (N J : ℕ) (p : Fin J → ℕ) := EuclideanSpace ℝ (EnrichedIndex N J p)

def enrichedFeature (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) : EnrichedMark N J p :=
  WithLp.toLp 2 fun i => match i with
    | .inl i => a*x.val i
    | .inr ⟨j,t⟩ => c j*spinTensorFeature N (p j) x t

lemma enrichedFeature_continuous (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ) :
    Continuous (enrichedFeature N J p a c) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact continuous_const.mul ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
  | inr i => exact continuous_const.mul ((EuclideanSpace.proj i.2).continuous.comp
      (spinTensorFeature_continuous N (p i.1)))

lemma enrichedFeature_inner (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x y : NormalizedSpin N) :
    inner ℝ (enrichedFeature N J p a c x) (enrichedFeature N J p a c y)=
      a^2*spinOverlap x y+∑ j, (c j)^2*spinOverlap x y^(p j) := by
  change (∑ i : EnrichedIndex N J p,
    (enrichedFeature N J p a c y i)*(enrichedFeature N J p a c x i)) = _
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedFeature]
  have hlin : (∑ i : Fin N, a*y.val i*(a*x.val i))=a^2*spinOverlap x y := by
    change (∑ i : Fin N, a*y.val i*(a*x.val i)) = a^2*(∑ i : Fin N, y.val i*x.val i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hlin]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← spinTensorFeature_inner N (p j) x y]
  change (∑ i, c j*spinTensorFeature N (p j) y i*(c j*spinTensorFeature N (p j) x i))=
    (c j)^2*(∑ i, spinTensorFeature N (p j) y i*spinTensorFeature N (p j) x i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma enrichedFeature_norm_sq (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) :
    ‖enrichedFeature N J p a c x‖^2=a^2+∑ j, (c j)^2 := by
  rw [← real_inner_self_eq_norm_sq,enrichedFeature_inner]
  have hx : spinOverlap x x=1 := by
    have h : ‖x.val‖=1 := by simp
    simp [spinOverlap,h]
  simp [hx]

lemma enrichedFeature_norm (N J : ℕ) (p : Fin J → ℕ) (a : ℝ) (c : Fin J → ℝ)
    (x : NormalizedSpin N) :
    ‖enrichedFeature N J p a c x‖=Real.sqrt (a^2+∑ j, (c j)^2) := by
  rw [← enrichedFeature_norm_sq N J p a c x,Real.sqrt_sq (norm_nonneg _)]

def perturbationScale (N : ℕ) : ℝ := (N:ℝ)^(-(1:ℝ)/16)

def perturbationAmplitude (N : ℕ) (u : Fin N → ℝ) (j : Fin N) : ℝ :=
  Real.sqrt (N:ℝ)*perturbationScale N*(2:ℝ)^(-((j.val+1:ℕ):ℤ))*u j

def sourceEnrichedFeature (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ) :
    NormalizedSpin N → EnrichedMark N N p :=
  enrichedFeature N N p (Real.sqrt (N:ℝ)) (perturbationAmplitude N u)

variable {I : Type} [Fintype I]

def diagonalMarkLinear (c : I → ℝ) : EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun x := WithLp.toLp 2 fun i => c i*x i
  map_add' x y := by ext i; change c i*(x i+y i)=c i*x i+c i*y i; ring
  map_smul' r x := by ext i; change c i*(r*x i)=r*(c i*x i); ring

def diagonalMark (c : I → ℝ) : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I :=
  (diagonalMarkLinear c).toContinuousLinearMap

@[simp] lemma diagonalMark_apply (c : I → ℝ) (x : EuclideanSpace ℝ I) (i : I) :
    diagonalMark c x i=c i*x i := rfl

lemma diagonalMark_self_adjoint (c : I → ℝ) (x y : EuclideanSpace ℝ I) :
    inner ℝ (diagonalMark c x) y=inner ℝ x (diagonalMark c y) := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change y i*(c i*x i)=(c i*y i)*x i
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
