import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.InverseProfile
import OAI.Analysis.BiholderTransport.LinearAlgebra.MixedOperator
import OAI.Analysis.BiholderTransport.Coordinates.ExpReciprocity
import OAI.Analysis.BiholderTransport.Coordinates.NormalEndpointJoin

namespace OAI

noncomputable section
namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local instance productNormedSpace : NormedSpace ℝ (F×E) := Prod.normedSpace
local instance productNormedGroup : NormedAddCommGroup (F×E) := Prod.normedAddCommGroup
local instance productDualNormedGroup : NormedAddCommGroup ((F×E) →L[ℝ] ℝ) := inferInstance
local instance productDualNormedSpace : NormedSpace ℝ ((F×E) →L[ℝ] ℝ) := inferInstance

def negativeMixedForm (H : (F×E) →L[ℝ] (F×E) →L[ℝ] ℝ) : F →L[ℝ] E →L[ℝ] ℝ := by
  let I : F →L[ℝ] F×E := (ContinuousLinearMap.id ℝ F).prod 0
  let K : E →L[ℝ] F×E := (0:E →L[ℝ] F).prod (ContinuousLinearMap.id ℝ E)
  exact -((H.comp I).flip.comp K).flip

@[simp] lemma negativeMixedForm_apply (H : (F×E) →L[ℝ] (F×E) →L[ℝ] ℝ)
    (v : F) (w : E) : negativeMixedForm H v w= -H (v,0) (0,w) := rfl
end WeakMTWTransport




open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

local instance tangentFiniteNormalMixed (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

local instance endpointProductNormedGroup (x y : M) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedAddCommGroup
local instance endpointProductNormedSpace (x y : M) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) :=
  Prod.normedSpace
local instance endpointDualNormedGroup (x y : M) :
    NormedAddCommGroup ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance
local instance endpointDualNormedSpace (x y : M) :
    NormedSpace ℝ ((TangentSpace 𝓘(ℝ,Model n) y × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ) :=
  inferInstance

def normalEndpointMixedOperator (x y : M) (h : ℝ)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x :=
  mixedOperator (negativeMixedForm
    (fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p)))

@[simp] lemma normalEndpointMixedOperator_inner (x y : M) (h : ℝ)
    (p k : TangentSpace 𝓘(ℝ,Model n) x) (d : TangentSpace 𝓘(ℝ,Model n) y) :
    inner ℝ (normalEndpointMixedOperator x y h p d) k=
      -fderiv ℝ (fderiv ℝ (normalEndpointJoinAction x y h)) (0,p) (d,0) (0,k) := by
  rw [normalEndpointMixedOperator,mixedOperator_inner,negativeMixedForm_apply]

variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalEndpoint_operator_adjoint_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    {L : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hend : riemannianExp x p=y)
    (hleft : h • p∈injectivityDomain x)
    (hright : (1-h) • (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hL : ContDiffAt ℝ ∞ L p) (hLp : L p=0)
    (hLi : ∀ᶠ v in 𝓝 p, riemannianExp y (L v)=riemannianExp x v) :
    fixedJoinOperator x h 1 p=(fderiv ℝ L p).adjoint.comp
      (normalEndpointMixedOperator x y h p).adjoint := by
  have hB := (fixedJoinAction_contDiffAt hh1.ne' hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply mixed_factor_adjoint (fixedJoinOperator_symmetric hB)
  intro d k
  rw [fixedJoinOperator_inner,normalEndpointMixedOperator_inner]
  exact normalEndpointJoinAction_factor hh hh1 hend hleft hright hL hLp hLi d k

lemma exists_reverse_exp_fixedJoin_factor {x y : M} {h : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) y}
    (hh : 0<h) (hh1 : h<1) (hp : p∈injectivityDomain x)
    (hq : q∈injectivityDomain y) (hpx : riemannianExp x p=y)
    (hqy : riemannianExp y q=x) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ R q ∧ R q=0 ∧
      (∀ᶠ w in 𝓝 q, riemannianExp x (R w)=riemannianExp y w) ∧
      fixedJoinOperator x h 1 p=(fderiv ℝ R q).comp
        (normalEndpointMixedOperator x y h p).adjoint := by
  obtain ⟨L,R,hL,hR,hLp,hRq,hLi,hRi,hrec⟩ :=
    exists_reciprocal_normal_exp_coordinates hp hq hpx hqy
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) hh hh1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp hh.le hh1
  refine ⟨R,hR,hRq,hRi,?_⟩
  rw [normalEndpoint_operator_adjoint_factor hh hh1 hpx hleft hright hL hLp hLi]
  congr 1
  ext w
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℝ w (fderiv ℝ L p v)=inner ℝ (fderiv ℝ L p v) w := real_inner_comm _ _
    _=inner ℝ v (fderiv ℝ R q w) := hrec v w
    _=inner ℝ (fderiv ℝ R q w) v := real_inner_comm _ _

end WeakMTWTransport

end

end OAI
