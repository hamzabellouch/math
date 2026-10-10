import OAI.Geometry.SurfaceImmersion.Correction.TensorOperatorSmooth
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorMetric
import OAI.Geometry.SurfaceImmersion.Geometry.ShortMetricPath

namespace OAI

/-! Actual finite smooth primitive families and their partial-cycle metrics.
Different cycles may use different supports and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance familyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance familyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance familyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance familyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance familySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance familySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

structure SmoothPrimitiveFamily (ι : Type*) [Fintype ι]
    (u : ∀ p : M, CovariantTwoTensor p) where
  amplitude : ι → M → ℝ
  phase : ι → M → ℝ
  smoothAmplitude : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (amplitude a)
  smoothPhase : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phase a)
  sum_eq : ∀ p, (∑ a, (amplitude a p)^2 •
    SmoothingAtlas.phaseDifferentialSquare (phase a) p) = u p

namespace SmoothPrimitiveFamily
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u)

def term (a : ι) (p : M) : CovariantTwoTensor p :=
  (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_apply (a : ι) (p : M) (v w : TangentSpace planeModel p) :
    d.term a p v w = (d.amplitude a p)^2 *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v) *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p w) := by
  change (d.amplitude a p)^2 *
    ((show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v) *
      (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p w)) = _
  ring

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_symmetric (a : ι) (p : M) (v w : TangentSpace planeModel p) :
    d.term a p v w = d.term a p w v := by
  rw [d.term_apply,d.term_apply]
  ring

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma term_nonneg (a : ι) (p : M) (v : TangentSpace planeModel p) :
    0 ≤ d.term a p v v := by
  rw [d.term_apply]
  nlinarith [sq_nonneg (d.amplitude a p),
    sq_nonneg (show ℝ from mfderiv planeModel 𝓘(ℝ) (d.phase a) p v)]

lemma term_smooth (A : SmoothingAtlas M) (a : ι) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (d.term a p)) :=
  ((d.smoothAmplitude a).pow 2).smul_section (A.phaseDifferentialSquare_smooth _ (d.smoothPhase a))

include d in
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma tensor_nonneg (p : M) (v : TangentSpace planeModel p) : 0 ≤ u p v v := by
  rw [← d.sum_eq p]
  simp only [sum_apply]
  exact Finset.sum_nonneg (fun a _ => d.term_nonneg a p v)

include d in
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma tensor_symmetric (p : M) (v w : TangentSpace planeModel p) : u p v w = u p w v := by
  rw [← d.sum_eq p]
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun a _ => d.term_symmetric a p v w)

include d in
lemma tensor_smooth (A : SmoothingAtlas M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)) := by
  have he : u = fun p => ∑ a, d.term a p := funext (fun p => (d.sum_eq p).symm)
  rw [he]
  exact ContMDiff.sum_section (fun a _ => d.term_smooth A a)

/-- The completed-cycle contribution plus any subset of the current cycle. -/
def cycleTensor (N c : ℕ) (s : Finset ι) (p : M) : CovariantTwoTensor p :=
  ((c : ℝ)/(N : ℝ)) • u p+(N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_empty (N c : ℕ) (p : M) :
    d.cycleTensor N c ∅ p = ((c : ℝ)/(N : ℝ)) • u p := by
  simp only [cycleTensor,Finset.sum_empty,smul_zero,add_zero]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_complete (N c : ℕ) (p : M) :
    d.cycleTensor N c Finset.univ p = (((c+1 : ℕ) : ℝ)/(N : ℝ)) • u p := by
  change ((c : ℝ)/(N : ℝ)) • u p+(N : ℝ)⁻¹ • (∑ a, d.term a p) = _
  rw [show (∑ a, d.term a p) = u p from d.sum_eq p,← add_smul]
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,add_mul,one_mul]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_insert [DecidableEq ι] (N c : ℕ) (s : Finset ι) (a : ι) (ha : a ∉ s) (p : M) :
    d.cycleTensor N c (insert a s) p = d.cycleTensor N c s p+(N : ℝ)⁻¹ • d.term a p := by
  simp only [cycleTensor,Finset.sum_insert ha,smul_add]
  abel

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_nonneg (N c : ℕ) (s : Finset ι) (p : M) (v : TangentSpace planeModel p) :
    0 ≤ d.cycleTensor N c s p v v := by
  change 0 ≤ (c : ℝ)/(N : ℝ)*u p v v+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) v v
  apply add_nonneg
  · exact mul_nonneg (by positivity) (d.tensor_nonneg p v)
  · apply mul_nonneg (by positivity)
    simp only [sum_apply]
    exact Finset.sum_nonneg (fun a _ => d.term_nonneg a p v)

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma cycleTensor_symmetric (N c : ℕ) (s : Finset ι) (p : M) (v w : TangentSpace planeModel p) :
    d.cycleTensor N c s p v w = d.cycleTensor N c s p w v := by
  change (c : ℝ)/(N : ℝ)*u p v w+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) v w =
    (c : ℝ)/(N : ℝ)*u p w v+(N : ℝ)⁻¹*(∑ a ∈ s, d.term a p) w v
  simp only [sum_apply]
  rw [d.tensor_symmetric p v w]
  congr 2
  exact Finset.sum_congr rfl (fun a _ => d.term_symmetric a p v w)

lemma cycleTensor_smooth (A : SmoothingAtlas M) (N c : ℕ) (s : Finset ι) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (d.cycleTensor N c s p)) :=
  (d.tensor_smooth A).const_smul_section.add_section
    ((ContMDiff.sum_section (fun a _ => d.term_smooth A a)).const_smul_section)

def cycleMetric (A : SmoothingAtlas M) (g : SmoothMetric M) (N c : ℕ) (s : Finset ι) : SmoothMetric M :=
  positiveTensorMetric (g.inner+d.cycleTensor N c s)
    (g.contMDiff.add_section (d.cycleTensor_smooth A N c s))
    (by
      intro p v w
      change g.inner p v w+d.cycleTensor N c s p v w =
        g.inner p w v+d.cycleTensor N c s p w v
      rw [g.symm,d.cycleTensor_symmetric])
    (by
      intro p v hv
      exact add_pos_of_pos_of_nonneg (g.pos p v hv) (d.cycleTensor_nonneg N c s p v))

lemma cycleMetric_lower (A : SmoothingAtlas M) (g : SmoothMetric M)
    (N c : ℕ) (s : Finset ι) (p : M) (v : TangentSpace planeModel p) :
    g.inner p v v ≤ (d.cycleMetric A g N c s).inner p v v :=
  le_add_of_nonneg_right (d.cycleTensor_nonneg N c s p v)

end SmoothPrimitiveFamily

namespace SmoothingAtlas
open PhaseGeometry
variable (A : SmoothingAtlas M)

def correctedSmoothPrimitiveFamily
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi phi : (A.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hsupport : ∀ a, tsupport (psi a) ⊆ (chart (a.1 : M)).source)
    (hQ : ∀ a p, p ∈ tsupport (psi a) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p)) :
    SmoothPrimitiveFamily (A.centers × Fin 3) u where
  amplitude := A.correctedPrimitiveAmplitude P psi phi u
  phase := phi
  smoothAmplitude := A.correctedPrimitiveAmplitude_smooth_of_data P psi phi
    hpsi hphi hsupport hQ houter hinv u hu hpos
  smoothPhase := hphi
  sum_eq := A.correctedPrimitiveAmplitude_reconstruct P psi phi hinv u hsymm
    (fun a p hp => (hpos a p hp).le)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
