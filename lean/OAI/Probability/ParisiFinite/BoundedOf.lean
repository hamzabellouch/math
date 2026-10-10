import Mathlib
import OAI.Probability.ParisiFinite.SpinTrace

namespace OAI

/-! Bounded Of. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def boundedOf (g : E → ℝ) (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    BoundedContinuousFunction E ℝ where
  toContinuousMap := ⟨g, hg⟩
  map_bounded' := ⟨2*M, fun x y => by
    change |g x-g y| ≤ _
    have h := abs_sub_le (g x) 0 (g y)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hM x, hM y]⟩

omit [NormedSpace ℝ E] in
lemma bounded_abs (g : BoundedContinuousFunction E ℝ) (x : E) : |g x| ≤ ‖g‖ := by
  simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x

 

def tiltMap (f : DirectionalField E) (a : ℝ) (c : E) :
    BoundedContinuousFunction E ℝ →ₗ[ℝ] BoundedContinuousFunction E ℝ where
  toFun g := boundedOf (ambientTilt a c f.val g)
    (continuous_ambientTilt f.lipschitz g.continuous (bounded_abs g) a c)
    (abs_ambientTilt_le f.lipschitz g.continuous (bounded_abs g) a c)
  map_add' g h := by
    ext x
    exact ambientTilt_add f.lipschitz g.continuous h.continuous (bounded_abs g) (bounded_abs h) a c x
  map_smul' k g := by
    ext x
    exact ambientTilt_const_mul a c f.val g x k

@[simp] lemma tiltMap_apply (f : DirectionalField E) (a : ℝ) (c : E)
    (g : BoundedContinuousFunction E ℝ) (x : E) :
    tiltMap f a c g x = ambientTilt a c f.val g x := rfl

lemma tiltMap_mono (f : DirectionalField E) (a : ℝ) (c : E)
    {g h : BoundedContinuousFunction E ℝ} (hgh : ∀ x, g x ≤ h x) :
    ∀ x, tiltMap f a c g x ≤ tiltMap f a c h x :=
  ambientTilt_mono f.lipschitz g.continuous h.continuous (bounded_abs g) (bounded_abs h) hgh a c

@[simp] lemma tiltMap_const (f : DirectionalField E) (a : ℝ) (c : E) (k : ℝ) :
    tiltMap f a c (BoundedContinuousFunction.const E k) = BoundedContinuousFunction.const E k := by
  ext x
  exact ambientTilt_const f.lipschitz a c x k

lemma tiltMap_nonneg (f : DirectionalField E) (a : ℝ) (c : E)
    {g : BoundedContinuousFunction E ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∀ x, 0 ≤ tiltMap f a c g x := by
  have h := tiltMap_mono f a c (g:=0) (h:=g) hg
  simpa only [map_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using h

lemma norm_tiltMap_le (f : DirectionalField E) (a : ℝ) (c : E)
    (g : BoundedContinuousFunction E ℝ) : ‖tiltMap f a c g‖ ≤ ‖g‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg g)).2
  intro x
  exact abs_ambientTilt_le f.lipschitz g.continuous (bounded_abs g) a c x

namespace DirectionalField

def firstBCF (f : DirectionalField E) (v : E) : BoundedContinuousFunction E ℝ :=
  boundedOf (f.first v) (f.continuousFirst v) (f.normFirst v)

def secondBCF (f : DirectionalField E) (v w : E) : BoundedContinuousFunction E ℝ :=
  boundedOf (f.second v w) (f.continuousSecond v w) (f.normSecond v w)

@[simp] lemma firstBCF_apply (f : DirectionalField E) (v x : E) : f.firstBCF v x = f.first v x := rfl
@[simp] lemma secondBCF_apply (f : DirectionalField E) (v w x : E) : f.secondBCF v w x = f.second v w x := rfl

lemma firstBCF_transform (f : DirectionalField E) (a : ℝ≥0) (c v : E) :
    (f.transform a c).firstBCF v = tiltMap f a c (f.firstBCF v) := rfl

lemma secondBCF_transform (f : DirectionalField E) (a : ℝ≥0) (c v w : E) :
    (f.transform a c).secondBCF v w = tiltMap f a c (f.secondBCF v w) +
      (a:ℝ) • (tiltMap f a c (f.firstBCF v*f.firstBCF w) -
        tiltMap f a c (f.firstBCF v)*tiltMap f a c (f.firstBCF w)) := rfl
end DirectionalField

namespace FieldFamily

def dotBCF (F : FieldFamily E) (t : ℝ) : BoundedContinuousFunction E ℝ :=
  boundedOf (F.dot t) (F.continuousDot.comp (continuous_const.prodMk continuous_id)) (F.normDot t)

@[simp] lemma dotBCF_apply (F : FieldFamily E) (t : ℝ) (x : E) : F.dotBCF t x = F.dot t x := rfl

lemma dotBCF_constant (f : DirectionalField E) (t : ℝ) : (constant f).dotBCF t = 0 := rfl

lemma dotBCF_transform (F : FieldFamily E) (a : ℝ≥0) (c : E) (s ds : ℝ → ℝ)
    (hs : Continuous s) (hds : Continuous ds) (hd : ∀ t, HasDerivAt s (ds t) t) (t : ℝ) :
    (F.transform a c s ds hs hds hd).dotBCF t =
      tiltMap (F.field t) a (s t • c) (F.dotBCF t) + (s t*ds t) •
      (tiltMap (F.field t) a (s t • c) ((F.field t).secondBCF c c) + (a:ℝ) •
        tiltMap (F.field t) a (s t • c) ((F.field t).firstBCF c ^ 2)) := by
  ext x
  rfl
end FieldFamily
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def transport (f : DirectionalField E) : List (MovingCoordinate E) → ℝ →
    (BoundedContinuousFunction E ℝ →ₗ[ℝ] BoundedContinuousFunction E ℝ)
  | [], _ => LinearMap.id
  | c::cs, t => (tiltMap ((hierarchy f cs).field t) c.gamma (c.scale t • c.direction)).comp
      (transport f cs t)

lemma transport_nonneg (f : DirectionalField E) (cs : List (MovingCoordinate E)) (t : ℝ)
    {g : BoundedContinuousFunction E ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∀ x, 0 ≤ transport f cs t g x := by
  induction cs with
  | nil => exact hg
  | cons c cs ih => exact tiltMap_nonneg _ _ _ ih

lemma transport_const (f : DirectionalField E) (cs : List (MovingCoordinate E)) (t k : ℝ) :
    transport f cs t (BoundedContinuousFunction.const E k) = BoundedContinuousFunction.const E k := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [transport, LinearMap.comp_apply, ih, tiltMap_const]

lemma hierarchy_firstBCF (f : DirectionalField E) (cs : List (MovingCoordinate E)) (t : ℝ) (v : E) :
    ((hierarchy f cs).field t).firstBCF v = transport f cs t (f.firstBCF v) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (((hierarchy f cs).field t).transform c.gamma (c.scale t • c.direction)).firstBCF v = _
    rw [DirectionalField.firstBCF_transform, ih]
    rfl

section FiniteSpin
variable {ι : Type*} [Fintype ι] [Nonempty ι]
open SKGaussian

 
def gibbsMap (β : ℝ) : (ι → ℝ) →ₗ[ℝ] BoundedContinuousFunction (ι → ℝ) ℝ where
  toFun v := boundedOf (fun x => gibbsMean β x v) (continuous_gibbsMean β v)
    (fun x => abs_gibbsMean_le β x v)
  map_add' v w := by
    ext x
    simp [boundedOf, gibbsMean, mul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    ext x
    simp [boundedOf, gibbsMean, mul_left_comm _ k, Finset.mul_sum]

@[simp] lemma gibbsMap_apply (β : ℝ) (v x : ι → ℝ) : gibbsMap β v x = gibbsMean β x v := rfl

lemma gibbsMap_nonneg (β : ℝ) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    ∀ x, 0 ≤ gibbsMap β v x := by
  intro x
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (weight_pos _ _).le (hv i))

lemma gibbsMap_const (β k : ℝ) : gibbsMap (ι:=ι) β (fun _ => k) =
    BoundedContinuousFunction.const (ι → ℝ) k := by
  ext x
  change (∑ i, weight (fun j => β*x j) i*k) = k
  rw [← Finset.sum_mul, sum_weight, one_mul]

 

def spinObserve (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    (ι → ℝ) →ₗ[ℝ] BoundedContinuousFunction (ι → ℝ) ℝ :=
  (transport (traceField β hβ) cs t).comp (gibbsMap β)

lemma spinObserve_nonneg (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) : ∀ x, 0 ≤ spinObserve β hβ cs t v x :=
  transport_nonneg _ _ _ (gibbsMap_nonneg β hv)

lemma spinObserve_const (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t k : ℝ) :
    spinObserve β hβ cs t (fun _ => k) = BoundedContinuousFunction.const (ι → ℝ) k := by
  simp only [spinObserve, LinearMap.comp_apply, gibbsMap_const, transport_const]

lemma spin_first_observe (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ)
    (v : ι → ℝ) : ((hierarchy (traceField β hβ) cs).field t).firstBCF v = spinObserve β hβ cs t v :=
  hierarchy_firstBCF _ _ _ _

 
def spinWeight [DecidableEq ι] (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) (i : ι) :
    BoundedContinuousFunction (ι → ℝ) ℝ := spinObserve β hβ cs t (Pi.single i 1)

lemma spinWeight_nonneg [DecidableEq ι] (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) (i : ι) (x : ι → ℝ) :
    0 ≤ spinWeight β hβ cs t i x := by
  apply spinObserve_nonneg
  intro j
  by_cases hij : j=i <;> simp [hij]

lemma spinObserve_eq_sum [DecidableEq ι] (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) (v : ι → ℝ) :
    spinObserve β hβ cs t v = ∑ i, v i • spinWeight β hβ cs t i := by
  have he : v = ∑ i, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply, apply_ite]
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, spinWeight]

lemma sum_spinWeight [DecidableEq ι] (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    ∑ i, spinWeight β hβ cs t i = BoundedContinuousFunction.const (ι → ℝ) 1 := by
  have he := spinObserve_eq_sum β hβ cs t (fun _ => 1)
  rw [spinObserve_const] at he
  simpa only [one_smul] using he.symm
end FiniteSpin
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

abbrev Noise (E : Type*) := List (ℝ × E)

def noiseGradient (f : DirectionalField E) : Noise E → BoundedContinuousFunction E ℝ
  | [] => 0
  | (k,v)::vs => k • (f.firstBCF v)^2 + noiseGradient f vs

def noiseHessian (f : DirectionalField E) : Noise E → BoundedContinuousFunction E ℝ
  | [] => 0
  | (k,v)::vs => k • f.secondBCF v v + noiseHessian f vs

def noiseResponse (f : DirectionalField E) (a : ℝ) (vs : Noise E) : BoundedContinuousFunction E ℝ :=
  noiseHessian f vs + a • noiseGradient f vs

lemma noiseResponse_nil (f : DirectionalField E) (a : ℝ) : noiseResponse f a [] = 0 := by
  simp [noiseResponse, noiseHessian, noiseGradient]

lemma noiseResponse_cons (f : DirectionalField E) (a k : ℝ) (v : E) (vs : Noise E) :
    noiseResponse f a ((k,v)::vs) = k • (f.secondBCF v v+a •(f.firstBCF v)^2)+noiseResponse f a vs := by
  simp only [noiseResponse, noiseHessian, noiseGradient]
  module

lemma noiseHessian_transform (f : DirectionalField E) (a : ℝ≥0) (c : E) (vs : Noise E) :
    noiseHessian (f.transform a c) vs = tiltMap f a c (noiseHessian f vs) + (a:ℝ) •
      (tiltMap f a c (noiseGradient f vs)-noiseGradient (f.transform a c) vs) := by
  induction vs with
  | nil => simp [noiseHessian, noiseGradient]
  | cons kv vs ih =>
    rcases kv with ⟨k,v⟩
    simp only [noiseHessian, noiseGradient, DirectionalField.secondBCF_transform, ih,
      map_add, map_smul, DirectionalField.firstBCF_transform, pow_two]
    module

 
lemma noiseResponse_transform (f : DirectionalField E) (b : ℝ≥0) (a : ℝ) (c : E) (vs : Noise E) :
    noiseResponse (f.transform b c) a vs =
      tiltMap f b c (noiseResponse f b vs) - ((b:ℝ)-a) • noiseGradient (f.transform b c) vs := by
  simp only [noiseResponse, noiseHessian_transform, map_add, map_smul]
  module

def coordinateNoise (c : MovingCoordinate E) (t : ℝ) : ℝ × E := (c.scale t*c.velocity t,c.direction)

def allNoise : List (MovingCoordinate E) → ℝ → Noise E → Noise E
  | [], _, vs => vs
  | c::cs, t, vs => allNoise cs t (coordinateNoise c t::vs)

lemma hierarchy_local_sum (f : DirectionalField E) (c : MovingCoordinate E)
    (cs : List (MovingCoordinate E)) (t a : ℝ) (vs : Noise E) :
    (hierarchy f (c::cs)).dotBCF t + noiseResponse ((hierarchy f (c::cs)).field t) a vs =
      tiltMap ((hierarchy f cs).field t) c.gamma (c.scale t • c.direction)
        ((hierarchy f cs).dotBCF t +
          noiseResponse ((hierarchy f cs).field t) c.gamma (coordinateNoise c t::vs)) -
        ((c.gamma:ℝ)-a) • noiseGradient ((hierarchy f (c::cs)).field t) vs := by
  change ((hierarchy f cs).transform c.gamma c.direction c.scale c.velocity
    c.continuousScale c.continuousVelocity c.hasScale).dotBCF t +
      noiseResponse (((hierarchy f cs).field t).transform c.gamma (c.scale t • c.direction)) a vs =
      tiltMap ((hierarchy f cs).field t) c.gamma (c.scale t • c.direction)
        ((hierarchy f cs).dotBCF t +
          noiseResponse ((hierarchy f cs).field t) c.gamma (coordinateNoise c t::vs)) -
        ((c.gamma:ℝ)-a) • noiseGradient
          (((hierarchy f cs).field t).transform c.gamma (c.scale t • c.direction)) vs
  rw [FieldFamily.dotBCF_transform, noiseResponse_transform]
  simp only [coordinateNoise, noiseResponse_cons, map_add, map_smul]
  module

 

def hierarchyRemainder (f : DirectionalField E) (β : ℝ) : List (MovingCoordinate E) → ℝ → ℝ →
    Noise E → BoundedContinuousFunction E ℝ
  | [], _, a, vs => (β-a) • noiseGradient f vs
  | c::cs, t, a, vs => ((c.gamma:ℝ)-a) • noiseGradient ((hierarchy f (c::cs)).field t) vs +
      tiltMap ((hierarchy f cs).field t) c.gamma (c.scale t • c.direction)
        (hierarchyRemainder f β cs t c.gamma (coordinateNoise c t::vs))

section FiniteSpin
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def diagonalNoise : Noise (ι → ℝ) → (ι → ℝ)
  | [] => 0
  | (k,v)::vs => k • v^2+diagonalNoise vs

lemma trace_firstBCF (β : ℝ≥0) (hβ : 0 < β) (v : ι → ℝ) :
    (traceField β hβ).firstBCF v = gibbsMap β v := rfl

lemma trace_secondBCF (β : ℝ≥0) (hβ : 0 < β) (v : ι → ℝ) :
    (traceField β hβ).secondBCF v v = (β:ℝ) • (gibbsMap β (v^2)-(gibbsMap β v)^2) := by
  ext x
  change (β:ℝ)*(gibbsMean β x (fun i => v i*v i)-gibbsMean β x v*gibbsMean β x v) =
    (β:ℝ)*(gibbsMean β x (v^2)-(gibbsMean β x v)^2)
  have he : (fun i => v i*v i) = v^2 := by ext i; simp [pow_two]
  rw [he]
  simp only [pow_two]

lemma trace_noiseResponse (β : ℝ≥0) (hβ : 0 < β) (a : ℝ) (vs : Noise (ι → ℝ)) :
    noiseResponse (traceField β hβ) a vs = (β:ℝ) • gibbsMap β (diagonalNoise vs) -
      ((β:ℝ)-a) • noiseGradient (traceField β hβ) vs := by
  induction vs with
  | nil => simp [noiseResponse_nil, diagonalNoise, noiseGradient]
  | cons kv vs ih =>
    rcases kv with ⟨k,v⟩
    rw [noiseResponse_cons, ih]
    simp only [diagonalNoise, noiseGradient, map_add, map_smul]
    rw [trace_secondBCF, trace_firstBCF]
    module

 

lemma hierarchy_sum_rule (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ)))
    (t a : ℝ) (vs : Noise (ι → ℝ)) :
    (hierarchy (traceField β hβ) cs).dotBCF t +
      noiseResponse ((hierarchy (traceField β hβ) cs).field t) a vs =
      (β:ℝ) • spinObserve β hβ cs t (diagonalNoise (allNoise cs t vs)) -
        hierarchyRemainder (traceField β hβ) β cs t a vs := by
  induction cs generalizing a vs with
  | nil =>
    change 0 + noiseResponse (traceField β hβ) a vs = _
    simpa only [zero_add, spinObserve, transport, LinearMap.comp_apply, LinearMap.id_apply,
      hierarchyRemainder, allNoise] using trace_noiseResponse β hβ a vs
  | cons c cs ih =>
    rw [hierarchy_local_sum, ih]
    simp only [map_sub, map_smul, hierarchyRemainder, allNoise, spinObserve,
      transport, LinearMap.comp_apply]
    module

lemma hierarchy_derivative_sum_rule (β : ℝ≥0) (hβ : 0 < β)
    (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => hierarchyValue (spinTrace β) cs s x)
      ((β:ℝ)*spinObserve β hβ cs t (diagonalNoise (allNoise cs t [])) x -
        hierarchyRemainder (traceField β hβ) β cs t 0 [] x) t := by
  have h := hierarchy_sum_rule β hβ cs t 0 []
  simp only [noiseResponse_nil, add_zero] at h
  have hd := hasDerivAt_hierarchyValue (traceField β hβ) cs t x
  change HasDerivAt _ ((hierarchy (traceField β hβ) cs).dotBCF t x) t at hd
  rw [h] at hd
  exact hd
end FiniteSpin
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

 
def replicaObserve (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    (ι → ι → ℝ) →ₗ[ℝ] BoundedContinuousFunction (ι → ℝ) ℝ where
  toFun K := ∑ i, ∑ j, K i j • (spinWeight β hβ cs t i * spinWeight β hβ cs t j)
  map_add' K L := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a K := by simp [mul_smul, Finset.smul_sum]

lemma replicaObserve_apply (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ)
    (K : ι → ι → ℝ) (x : ι → ℝ) :
    replicaObserve β hβ cs t K x = ∑ i, ∑ j, K i j * (spinWeight β hβ cs t i x * spinWeight β hβ cs t j x) := by
  simp [replicaObserve, BoundedContinuousFunction.sum_apply]

lemma sum_spinWeight_apply (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ)
    (x : ι → ℝ) : ∑ i, spinWeight β hβ cs t i x = 1 := by
  simpa using congrArg (fun w : BoundedContinuousFunction (ι → ℝ) ℝ => w x) (sum_spinWeight β hβ cs t)

lemma replicaObserve_nonneg (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ)
    {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (x : ι → ℝ) :
    0 ≤ replicaObserve β hβ cs t K x := by
  rw [replicaObserve_apply]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hK i j) (mul_nonneg (spinWeight_nonneg β hβ cs t i x) (spinWeight_nonneg β hβ cs t j x))))

@[simp] lemma replicaObserve_const (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ)))
    (t k : ℝ) : replicaObserve β hβ cs t (fun _ _ => k) = BoundedContinuousFunction.const (ι → ℝ) k := by
  ext x
  simp only [replicaObserve_apply, ← Finset.mul_sum, sum_spinWeight_apply, mul_one]
  rfl

lemma replicaObserve_rankOne (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ)))
    (t : ℝ) (v w : ι → ℝ) :
    replicaObserve β hβ cs t (fun i j => v i*w j) = spinObserve β hβ cs t v * spinObserve β hβ cs t w := by
  rw [spinObserve_eq_sum, spinObserve_eq_sum]
  ext x
  simp only [replicaObserve_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

 
def kernelNoise : Noise (ι → ℝ) → (ι → ι → ℝ)
  | [] => 0
  | (k,v)::vs => (fun i j => k*(v i*v j)) + kernelNoise vs

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
lemma kernelNoise_diagonal (vs : Noise (ι → ℝ)) (i : ι) : kernelNoise vs i i = diagonalNoise vs i := by
  induction vs with
  | nil => rfl
  | cons kv vs ih =>
    rcases kv with ⟨k,v⟩
    simp only [kernelNoise, diagonalNoise, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih, pow_two, Pi.mul_apply]

lemma noiseGradient_replica (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ)))
    (t : ℝ) (vs : Noise (ι → ℝ)) :
    noiseGradient ((hierarchy (traceField β hβ) cs).field t) vs =
      replicaObserve β hβ cs t (kernelNoise vs) := by
  induction vs with
  | nil => simp [noiseGradient, kernelNoise]
  | cons kv vs ih =>
    rcases kv with ⟨k,v⟩
    change k • (((hierarchy (traceField β hβ) cs).field t).firstBCF v)^2 +
      noiseGradient ((hierarchy (traceField β hβ) cs).field t) vs =
      replicaObserve β hβ cs t (k •(fun i j => v i*v j)+kernelNoise vs)
    rw [map_add, map_smul, replicaObserve_rankOne, spin_first_observe, ih, pow_two]

lemma replicaObserve_ge_const (β : ℝ≥0) (hβ : 0 < β) (cs : List (MovingCoordinate (ι → ℝ)))
    (t : ℝ) {K : ι → ι → ℝ} {k : ℝ} (hK : ∀ i j, k ≤ K i j) (x : ι → ℝ) :
    k ≤ replicaObserve β hβ cs t K x := by
  have h := replicaObserve_nonneg β hβ cs t (K:=K-(fun _ _ => k)) (fun i j => sub_nonneg.mpr (hK i j)) x
  simpa only [map_sub, replicaObserve_const, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.const_apply, sub_nonneg] using h
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def prefixTransport (f : DirectionalField E) (tail : List (MovingCoordinate E)) :
    List (MovingCoordinate E) → ℝ →
      (BoundedContinuousFunction E ℝ →ₗ[ℝ] BoundedContinuousFunction E ℝ)
  | [], _ => LinearMap.id
  | c::cs, t => (tiltMap ((hierarchy f (cs++tail)).field t) c.gamma (c.scale t • c.direction)).comp
      (prefixTransport f tail cs t)

lemma prefixTransport_const (f : DirectionalField E) (tail pre : List (MovingCoordinate E)) (t k : ℝ) :
    prefixTransport f tail pre t (BoundedContinuousFunction.const E k) = BoundedContinuousFunction.const E k := by
  induction pre with
  | nil => rfl
  | cons c cs ih => simp only [prefixTransport, LinearMap.comp_apply, ih, tiltMap_const]

lemma prefixTransport_nonneg (f : DirectionalField E) (tail pre : List (MovingCoordinate E)) (t : ℝ)
    {g : BoundedContinuousFunction E ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∀ x, 0 ≤ prefixTransport f tail pre t g x := by
  induction pre with
  | nil => exact hg
  | cons c cs ih => exact tiltMap_nonneg _ _ _ ih

lemma transport_append (f : DirectionalField E) (pre tail : List (MovingCoordinate E)) (t : ℝ) :
    transport f (pre++tail) t = (prefixTransport f tail pre t).comp (transport f tail t) := by
  induction pre with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, transport, prefixTransport, ih, LinearMap.comp_assoc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma allNoise_append (pre tail : List (MovingCoordinate E)) (t : ℝ) (vs : Noise E) :
    allNoise (pre++tail) t vs = allNoise tail t (allNoise pre t vs) := by
  induction pre generalizing vs with
  | nil => rfl
  | cons c cs ih => simpa only [List.cons_append, allNoise] using ih (coordinateNoise c t::vs)

 

lemma remainder_constant_prefix (f : DirectionalField E) (β : ℝ) (b : ℝ≥0)
    (pre tail : List (MovingCoordinate E)) (t : ℝ) (vs : Noise E)
    (hb : ∀ c ∈ pre, c.gamma = b) :
    hierarchyRemainder f β (pre++tail) t b vs = prefixTransport f tail pre t
      (hierarchyRemainder f β tail t b (allNoise pre t vs)) := by
  induction pre generalizing vs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hb c (by simp)
    have hcs : ∀ d ∈ cs, d.gamma = b := fun d hd => hb d (by simp [hd])
    simp only [List.cons_append, hierarchyRemainder, hc, sub_self, zero_smul, zero_add,
      allNoise, prefixTransport, LinearMap.comp_apply, ih (coordinateNoise c t::vs) hcs]

lemma remainder_nonempty_constant_prefix (f : DirectionalField E) (β a : ℝ) (b : ℝ≥0)
    (c : MovingCoordinate E) (pre tail : List (MovingCoordinate E)) (t : ℝ) (vs : Noise E)
    (hb : ∀ d ∈ c::pre, d.gamma = b) :
    hierarchyRemainder f β ((c::pre)++tail) t a vs =
      ((b:ℝ)-a) • noiseGradient ((hierarchy f ((c::pre)++tail)).field t) vs +
        prefixTransport f tail (c::pre) t
          (hierarchyRemainder f β tail t b (allNoise (c::pre) t vs)) := by
  have hc := hb c (by simp)
  have hpre : ∀ d ∈ pre, d.gamma = b := fun d hd => hb d (by simp [hd])
  simp only [List.cons_append, hierarchyRemainder, hc, prefixTransport, LinearMap.comp_apply, allNoise]
  rw [remainder_constant_prefix f β b pre tail t (coordinateNoise c t::vs) hpre]
end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace ParisiFinite
variable {ι : Type*}

def coordinatesKernel (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) : ι → ι → ℝ :=
  (cs.map (fun c => fun i j => (c.scale t*c.velocity t)*(c.direction i*c.direction j))).sum

lemma coordinatesKernel_nil (t : ℝ) : coordinatesKernel ([] : List (MovingCoordinate (ι → ℝ))) t = 0 := rfl

lemma coordinatesKernel_cons (c : MovingCoordinate (ι → ℝ)) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    coordinatesKernel (c::cs) t = (fun i j => (c.scale t*c.velocity t)*(c.direction i*c.direction j)) + coordinatesKernel cs t := rfl

lemma coordinatesKernel_append (pre tail : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    coordinatesKernel (pre++tail) t = coordinatesKernel pre t + coordinatesKernel tail t := by
  simp [coordinatesKernel, List.sum_append]

lemma coordinatesKernel_ofFn {k : ℕ} (c : Fin k → MovingCoordinate (ι → ℝ)) (t : ℝ) (i j : ι) :
    coordinatesKernel (List.ofFn c) t i j = ∑ l, (c l).scale t*(c l).velocity t*((c l).direction i*(c l).direction j) := by
  simp [coordinatesKernel, List.map_ofFn, List.sum_ofFn]

lemma kernelNoise_allNoise [Fintype ι] [Nonempty ι] (cs : List (MovingCoordinate (ι → ℝ)))
    (t : ℝ) (vs : Noise (ι → ℝ)) :
    kernelNoise (allNoise cs t vs) = kernelNoise vs + coordinatesKernel cs t := by
  induction cs generalizing vs with
  | nil => simp [allNoise, coordinatesKernel_nil]
  | cons c cs ih =>
    rw [allNoise, ih, coordinatesKernel_cons]
    ext i j
    simp only [kernelNoise, coordinateNoise, Pi.add_apply]
    ring

 

def dummyCoordinate (a : ℝ≥0) : MovingCoordinate (ι → ℝ) := MovingCoordinate.constant a 0 0

lemma coordinatesKernel_dummy (a : ℝ≥0) (cs : List (MovingCoordinate (ι → ℝ))) (t : ℝ) :
    coordinatesKernel (dummyCoordinate a::cs) t = coordinatesKernel cs t := by
  ext i j
  simp [coordinatesKernel_cons, dummyCoordinate, MovingCoordinate.constant]
end ParisiFinite

namespace ParisiGuerra
open ParisiFinite SKQAOA SKGaussian ParisiInterpolation

def costBlock (n : ℕ) : List (MovingCoordinate (Configuration n → ℝ)) :=
  dummyCoordinate 0 :: List.ofFn (fun k : Fin (Fintype.card (Edge n)) =>
    MovingCoordinate.sine 0 (fun σ => skCoeff n σ ((Fintype.equivFin (Edge n)).symm k)))

def siteBlock (n : ℕ) (l : ℝ≥0 × ℝ≥0) : List (MovingCoordinate (Configuration n → ℝ)) :=
  dummyCoordinate l.1 :: List.ofFn (fun i : Fin n =>
    MovingCoordinate.cosine l.1 (fun σ => Real.sqrt l.2*spin σ i))

def siteCoordinates (n : ℕ) (ls : Schedule) : List (MovingCoordinate (Configuration n → ℝ)) :=
  ls.flatMap (siteBlock n)

def coordinates (n : ℕ) (ls : Schedule) := costBlock n ++ siteCoordinates n ls

def pressureCurve (n : ℕ) (β : ℝ) (ls : Schedule) (t : ℝ) : ℝ :=
  hierarchyValue (spinTrace β) (coordinates n ls) t 0

lemma costBlock_gamma (n : ℕ) : ∀ c ∈ costBlock n, c.gamma = 0 := by
  intro c hc
  simp only [costBlock, List.mem_cons, List.mem_ofFn] at hc
  rcases hc with rfl | ⟨i,rfl⟩ <;> rfl

lemma siteBlock_gamma (n : ℕ) (l : ℝ≥0 × ℝ≥0) : ∀ c ∈ siteBlock n l, c.gamma = l.1 := by
  intro c hc
  simp only [siteBlock, List.mem_cons, List.mem_ofFn] at hc
  rcases hc with rfl | ⟨i,rfl⟩ <;> rfl

lemma costBlock_kernel (n : ℕ) (t : ℝ) (σ τ : Configuration n) :
    coordinatesKernel (costBlock n) t σ τ =
      Real.sin t*Real.cos t*(∑ e, skCoeff n σ e*skCoeff n τ e) := by
  rw [costBlock, coordinatesKernel_dummy, coordinatesKernel_ofFn]
  simp only [MovingCoordinate.sine]
  rw [← Finset.mul_sum]
  congr 1
  exact ((Fintype.equivFin (Edge n)).symm.sum_comp (fun e => skCoeff n σ e*skCoeff n τ e))

lemma siteBlock_kernel (n : ℕ) (l : ℝ≥0 × ℝ≥0) (t : ℝ) (σ τ : Configuration n) :
    coordinatesKernel (siteBlock n l) t σ τ =
      -(Real.sin t*Real.cos t)*(l.2:ℝ)*overlapSum σ τ := by
  rw [siteBlock, coordinatesKernel_dummy, coordinatesKernel_ofFn]
  have hs := Real.sq_sqrt l.2.coe_nonneg
  have he (i : Fin n) : Real.cos t*(-Real.sin t)*
      ((Real.sqrt l.2*spin σ i)*(Real.sqrt l.2*spin τ i)) =
      (-(Real.sin t*Real.cos t)*(l.2:ℝ))*(spin σ i*spin τ i) := by
    calc
      _ = (-(Real.sin t*Real.cos t))*(Real.sqrt l.2)^2*(spin σ i*spin τ i) := by ring
      _ = _ := by rw [hs]
  simp only [MovingCoordinate.cosine, he, ← Finset.mul_sum, overlapSum]

 
def frontierKernel (n : ℕ) (q t : ℝ) (σ τ : Configuration n) : ℝ :=
  Real.sin t*Real.cos t*((n:ℝ)/2*(overlap σ τ-q)^2-(n:ℝ)/2*q^2-1/2)

lemma costBlock_frontier {n : ℕ} (hn : 0 < n) (t : ℝ) :
    coordinatesKernel (costBlock n) t = frontierKernel n 0 t := by
  ext σ τ
  rw [costBlock_kernel, coeff_covariance hn]
  unfold frontierKernel overlap
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']
  ring

lemma frontier_add_site {n : ℕ} (hn : 0 < n) (q t : ℝ) (l : ℝ≥0 × ℝ≥0) :
    frontierKernel n q t + coordinatesKernel (siteBlock n l) t = frontierKernel n (q+l.2) t := by
  ext σ τ
  simp only [Pi.add_apply, siteBlock_kernel]
  unfold frontierKernel overlap
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']
  ring
end ParisiGuerra

end

end OAI
