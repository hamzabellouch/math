import OAI.Geometry.SurfaceImmersion.Atlas.TensorFiberCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBasisPerturbation

namespace OAI

/-! The finite rank-one correction acts on symmetric tensors. Adding the
identity on the antisymmetric summand gives an honest invertible operator
on the full four-dimensional tensor fiber, without an orientation choice. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance primitiveInverseFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance primitiveInverseFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete : CompleteSpace TensorFiber := inferInstance
local instance primitiveInverseDualAdd : ContinuousAdd (Plane →L[ℝ] ℝ) := inferInstance
local instance primitiveInverseDualSmul : ContinuousSMul ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance primitiveInverseFiberGroup : AddCommGroup TensorFiber :=
  primitiveInverseFiberNormed.toAddCommGroup

/-- Intrinsic symmetrization of a bilinear form. -/
def tensorSymmetrizer : TensorFiber →L[ℝ] TensorFiber :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ TensorFiber +
    (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearMap)

lemma tensorSymmetrizer_apply (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = (B v w+B w v)/2 := by
  change (1/2 : ℝ)*(B v w+B w v) = (B v w+B w v)/2
  ring

lemma tensorSymmetrizer_symmetric (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = tensorSymmetrizer B w v := by
  rw [tensorSymmetrizer_apply,tensorSymmetrizer_apply,add_comm]

lemma tensorSymmetrizer_eq_self {B : TensorFiber} (hB : ∀ v w, B v w = B w v) :
    tensorSymmetrizer B = B := by
  ext v w
  rw [tensorSymmetrizer_apply,hB v w]
  ring

lemma tensorSymmetrizer_idempotent (B : TensorFiber) :
    tensorSymmetrizer (tensorSymmetrizer B) = tensorSymmetrizer B :=
  tensorSymmetrizer_eq_self (tensorSymmetrizer_symmetric B)

variable {ι : Type*} [Fintype ι]

/-- The actual finite supported primitive operator, in one fiber. -/
def finitePrimitiveOperator (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) : TensorFiber →L[ℝ] TensorFiber :=
  ∑ i, (psi i)^2 • ((q i).comp tensorSymmetrizer).smulRight ((xi i).smulRight (xi i))

lemma finitePrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi B =
      ∑ i, ((psi i)^2*q i (tensorSymmetrizer B)) • ((xi i).smulRight (xi i)) := by
  simp only [finitePrimitiveOperator,sum_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,smul_smul]

lemma finitePrimitiveOperator_symmetric (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) (v w : Plane) :
    finitePrimitiveOperator q psi xi B v w = finitePrimitiveOperator q psi xi B w v := by
  simp only [finitePrimitiveOperator_apply,sum_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finitePrimitiveOperator_symmetrizer (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi (tensorSymmetrizer B) = finitePrimitiveOperator q psi xi B := by
  simp only [finitePrimitiveOperator_apply,tensorSymmetrizer_idempotent]

def completedPrimitiveOperator (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) : TensorFiber →L[ℝ] TensorFiber :=
  finitePrimitiveOperator q psi xi + ContinuousLinearMap.id ℝ TensorFiber - tensorSymmetrizer

lemma completedPrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      finitePrimitiveOperator q psi xi B+B-tensorSymmetrizer B := rfl

lemma completedPrimitiveOperator_eq_id
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (hbase : ∀ B : TensorFiber, (∀ v w, B v w = B w v) →
      finitePrimitiveOperator q psi xi B = B) :
    completedPrimitiveOperator q psi xi = ContinuousLinearMap.id ℝ TensorFiber := by
  ext B v w
  have hb := hbase (tensorSymmetrizer B) (tensorSymmetrizer_symmetric B)
  rw [finitePrimitiveOperator_symmetrizer] at hb
  rw [completedPrimitiveOperator_apply,hb]
  simp only [add_apply,sub_apply,ContinuousLinearMap.id_apply]
  ring

/-- The inverse of the completed operator solves precisely the original
symmetric rank-one equation; the auxiliary antisymmetric identity vanishes. -/
theorem completedPrimitiveOperator_inverse_symmetric
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (hinv : (completedPrimitiveOperator q psi xi).IsInvertible)
    {H : TensorFiber} (hH : ∀ v w, H v w = H w v) :
    let B := (completedPrimitiveOperator q psi xi).inverse H
    (∀ v w, B v w = B w v) ∧ finitePrimitiveOperator q psi xi B = H := by
  dsimp only
  let B := (completedPrimitiveOperator q psi xi).inverse H
  have hsolve : completedPrimitiveOperator q psi xi B = H := hinv.self_apply_inverse H
  have hsym : ∀ v w, B v w = B w v := by
    intro v w
    have hvw := congrArg (fun C : TensorFiber => C v w) hsolve
    have hwv := congrArg (fun C : TensorFiber => C w v) hsolve
    have hfin := finitePrimitiveOperator_symmetric q psi xi B v w
    rw [completedPrimitiveOperator_apply] at hvw hwv
    simp only [add_apply,sub_apply] at hvw hwv
    have hs := tensorSymmetrizer_symmetric B v w
    have ht := hH v w
    linarith
  refine ⟨hsym,?_⟩
  rw [completedPrimitiveOperator_apply,tensorSymmetrizer_eq_self hsym,add_sub_cancel_right] at hsolve
  exact hsolve

abbrev PrimitiveFiberParameters (ι : Type*) := (ι → ℝ) × (ι → Plane →L[ℝ] ℝ)

lemma completedPrimitiveOperator_smooth (q : ι → TensorFiber →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun z : PrimitiveFiberParameters ι => completedPrimitiveOperator q z.1 z.2) := by
  have hs : ContDiff ℝ ∞
      (fun z : PrimitiveFiberParameters ι => finitePrimitiveOperator q z.1 z.2) := by
    apply ContDiff.sum
    intro i _
    have hp : ContDiff ℝ ∞ (fun z : PrimitiveFiberParameters ι => z.1 i) :=
      (contDiff_apply ℝ ℝ i).comp contDiff_fst
    have hv : ContDiff ℝ ∞ (fun z : PrimitiveFiberParameters ι => z.2 i) :=
      (contDiff_apply ℝ (Plane →L[ℝ] ℝ) i).comp contDiff_snd
    have hq : ContDiff ℝ ∞ (fun _ : PrimitiveFiberParameters ι => (q i).comp tensorSymmetrizer) :=
      contDiff_const
    exact (hp.pow 2).smul (hq.smulRight (hv.smulRight hv))
  exact (hs.add contDiff_const).sub contDiff_const

/-- Invertibility and positivity are obtained on an actual open neighborhood
of the reference cutoff/covector data, uniformly for a compact target set. -/
theorem compact_positive_primitive_inverse
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi₀ : ι → ℝ) (xi₀ : ι → Plane →L[ℝ] ℝ)
    (hbase : ∀ B : TensorFiber, (∀ v w, B v w = B w v) →
      finitePrimitiveOperator q psi₀ xi₀ B = B)
    {K : Set TensorFiber} (hK : IsCompact K)
    (hpos : ∀ H ∈ K, ∀ i, 0 < q i H) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ z : PrimitiveFiberParameters ι,
      ‖z-(psi₀,xi₀)‖ < eps →
      (completedPrimitiveOperator q z.1 z.2).IsInvertible ∧
        ∀ H ∈ K, ∀ i, 0 < q i ((completedPrimitiveOperator q z.1 z.2).inverse H) := by
  let z₀ : PrimitiveFiberParameters ι := (psi₀,xi₀)
  have heq := completedPrimitiveOperator_eq_id q psi₀ xi₀ hbase
  have hi : (completedPrimitiveOperator q psi₀ xi₀).IsInvertible := by
    rw [heq]
    exact ⟨ContinuousLinearEquiv.refl ℝ TensorFiber,rfl⟩
  have hs := completedPrimitiveOperator_smooth q
  have hiNear : ∀ᶠ z in 𝓝 z₀, (completedPrimitiveOperator q z.1 z.2).IsInvertible :=
    hs.continuous.continuousAt.eventually hi.eventually_nhds
  have hpNear : ∀ᶠ z in 𝓝 z₀, ∀ H ∈ K, ∀ i,
      0 < q i ((completedPrimitiveOperator q z.1 z.2).inverse H) := by
    apply hK.eventually_forall_of_forall_eventually
    intro H hH
    rw [Filter.eventually_all]
    intro i
    have hmaps : ContDiffAt ℝ ∞
        (fun z : PrimitiveFiberParameters ι × TensorFiber =>
          completedPrimitiveOperator q z.1.1 z.1.2) (z₀,H) :=
      hs.contDiffAt.comp (z₀,H) contDiffAt_fst
    have hv := (hi.contDiffAt_map_inverse.comp (z₀,H) hmaps).clm_apply contDiffAt_snd
    have hq := ((q i).contDiff.contDiffAt.comp (z₀,H) hv).continuousAt
    have hp : 0 < q i ((completedPrimitiveOperator q z₀.1 z₀.2).inverse H) := by
      simpa only [z₀,heq,ContinuousLinearMap.inverse_id,ContinuousLinearMap.id_apply] using hpos H hH i
    exact hq.eventually (lt_mem_nhds hp)
  obtain ⟨eps,heps,hsmall⟩ := Metric.eventually_nhds_iff.mp (hiNear.and hpNear)
  refine ⟨eps,heps,fun z hz => hsmall (y := z) ?_⟩
  simpa only [dist_eq_norm,z₀] using hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
