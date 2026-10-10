import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertCharts
import OAI.Geometry.CAT0Fillings.Geometry.Polarization
import OAI.Geometry.CAT0Fillings.Radial.MeasurableBound

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
theorem integrable_radialJacobian
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Integrable (fun z => |(C.multiplicity z : ℝ)| *
      C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z) (volume.restrict C.domain) := by
  obtain ⟨A,hA,hbound⟩ := C.radialJacobian_le_intrinsic_majorant p hp o hg hB hK hgb hrb
  have hmeas := C.aestronglyMeasurable_radialJacobian
    (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
    (measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm) o hg t
  apply (hρ.const_mul A).mono' (C.integrable.abs.aestronglyMeasurable.mul hmeas)
  filter_upwards [hbound t ht] with z hz
  rw [Real.norm_eq_abs,Pi.mul_apply,abs_mul,abs_abs]
  rw [abs_of_nonneg (show 0 ≤ C.radialJacobian _ o g t z from Real.sqrt_nonneg _)]
  calc
    _ ≤ |(C.multiplicity z : ℝ)| * (A * Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = _ := by ring
end CAT0Fillings.IntegerChart
namespace CAT0Fillings
open Set Metric
open scoped NNReal

variable {E X : Type*} [MetricSpace E] [MetricSpace X]

theorem radial_lipschitzOnWith
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set E} {f : E → X} {lam : E → ℝ} {K L R : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hl : LipschitzOnWith L lam s)
    (hla : ∀ x ∈ s, lam x ∈ Icc (0:ℝ) 1)
    (o : X) (hR : ∀ x ∈ s, dist o (f x) ≤ R) :
    LipschitzOnWith (K+R*L) (fun x => seg o (f x) (lam x)) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hsame : dist (seg o (f x) (lam x)) (seg o (f y) (lam x)) ≤
      lam x*dist (f x) (f y) := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg (hla _ hx).1 dist_nonneg)).mp
    calc
      _ ≤ (lam x*dist o (f x)-lam x*dist o (f y))^2+
        lam x*lam x*(dist (f x) (f y)^2-(dist o (f x)-dist o (f y))^2) :=
          hcomp o (f x) (f y) (lam x) (lam x) (hla _ hx) (hla _ hx)
      _ = _ := by ring
  have hlxy : |lam x-lam y| ≤ (L:ℝ)*dist x y := by
    simpa only [Real.dist_eq] using hl.dist_le_mul x hx y hy
  calc
    _ ≤ dist (seg o (f x) (lam x)) (seg o (f y) (lam x))+
        dist (seg o (f y) (lam x)) (seg o (f y) (lam y)) := dist_triangle _ _ _
    _ ≤ lam x*dist (f x) (f y)+|lam x-lam y| *dist o (f y) := by
      rw [hseg o (f y) (lam x) (lam y) (hla _ hx) (hla _ hy)]
      exact add_le_add hsame le_rfl
    _ ≤ dist (f x) (f y)+|lam x-lam y| *(R:ℝ) :=
      add_le_add (mul_le_of_le_one_left dist_nonneg (hla _ hx).2)
        (mul_le_mul_of_nonneg_left (hR _ hy) (abs_nonneg _))
    _ ≤ (K:ℝ)*dist x y+((L:ℝ)*dist x y)*(R:ℝ) :=
      add_le_add (hf.dist_le_mul x hx y hy) (mul_le_mul_of_nonneg_right hlxy R.coe_nonneg)
    _ = _ := by push_cast; ring

end CAT0Fillings
namespace CAT0Fillings
open Set Metric
open scoped NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem radial_lipschitzWith
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y => seg o y (1-t*g y)) := by
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  have hR : ∀ x : X, dist o x ≤ R := fun x =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)
  have hfrac : LipschitzWith (‖t‖₊*K) (fun x => 1-t*g x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show 1-t*g x-(1-t*g y) = -(t*(g x-g y)) by ring,
      abs_neg,abs_mul]
    have hh := mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (abs_nonneg t)
    simpa only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,Real.dist_eq,mul_assoc] using hh
  refine ⟨1+R*(‖t‖₊*K),?_⟩
  rw [←lipschitzOnWith_univ]
  exact radial_lipschitzOnWith seg hseg hcomp
    (LipschitzWith.id.lipschitzOnWith) hfrac.lipschitzOnWith (fun x _ => htg x) o
    (fun x _ => hR x)
end CAT0Fillings
end
end

end OAI
