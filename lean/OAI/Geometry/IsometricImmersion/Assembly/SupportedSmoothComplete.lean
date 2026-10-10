import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Sequences
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace
open scoped BoundedContinuousFunction

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev SupportedJetProduct (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  Π k : ℕ, Coord →ᵇ (Coord [×k]→L[ℝ] V)

def supportedJetMap (K : Compacts Coord) :
    ContDiffMapSupportedIn Coord V ⊤ K →L[ℝ] SupportedJetProduct V :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

omit [CompleteSpace V] in
theorem supportedJetMap_isUniformEmbedding (K : Compacts Coord) :
    IsUniformEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
  ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜 := ℝ) (n := ⊤)

omit [CompleteSpace V] in
theorem supportedJetMap_isClosed_range (K : Compacts Coord) :
    IsClosed (Set.range (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu ht
  choose f hf using hu
  have hfconv : Tendsto (fun n => supportedJetMap K (f n)) atTop (𝓝 v) := by
    simpa only [hf] using ht
  have hconv (k : ℕ) : TendstoUniformly
      (fun n => iteratedFDeriv ℝ k (f n)) (v k) atTop := by
    have hcoord := ((continuous_apply k).tendsto v).comp hfconv
    change Tendsto (fun n => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (f n))
      atTop (𝓝 (v k)) at hcoord
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcoord
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using h
  let C (k : ℕ) :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Coord) V
  have hderivative (k : ℕ) (x : Coord) :
      HasFDerivAt (fun y => v k y) (C k (v (k + 1) x)) x := by
    have hnext : TendstoUniformly
        (fun n => C k ∘ iteratedFDeriv ℝ (k + 1) (f n)) (C k ∘ v (k + 1)) atTop :=
      (C k).isometry.uniformContinuous.comp_tendstoUniformly (hconv (k + 1))
    have hfn (n : ℕ) (y : Coord) : HasFDerivAt (iteratedFDeriv ℝ k (f n))
        (C k (iteratedFDeriv ℝ (k + 1) (f n) y)) y := by
      have hs : ContDiff ℝ ∞ (f n) := (f n).contDiff
      have hd := ((hs.contDiffAt (x := y)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply, C] using hd
    exact hasFDerivAt_of_tendstoUniformly hnext hfn (fun y => (hconv k).tendsto_at y) x
  let C0 := continuousMultilinearCurryFin0 ℝ Coord V
  let g : Coord → V := fun x => C0 (v 0 x)
  have hjet : ∀ k : ℕ, iteratedFDeriv ℝ k g = (v k : Coord → Coord [×k]→L[ℝ] V) := by
    intro k
    induction k with
    | zero =>
        funext x
        change C0.symm (C0 (v 0 x)) = v 0 x
        exact C0.symm_apply_apply _
    | succ k ih =>
        rw [iteratedFDeriv_succ_eq_comp_left, ih]
        funext x
        change (C k).symm (fderiv ℝ (fun y => v k y) x) = v (k + 1) x
        rw [(hderivative k x).fderiv]
        exact (C k).symm_apply_apply _
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_continuous_differentiable.mpr
    constructor
    · intro k _
      rw [hjet k]
      exact (v k).continuous
    · intro k _
      rw [hjet k]
      exact fun x => (hderivative k x).differentiableAt
  have hzero : EqOn g 0 (K : Set Coord)ᶜ := by
    intro x hx
    have hlim := (hconv 0).tendsto_at x
    have hconst : Tendsto (fun n => iteratedFDeriv ℝ 0 (f n) x) atTop (𝓝 0) := by
      have hz (n : ℕ) : iteratedFDeriv ℝ 0 (f n) x = 0 :=
        (f n).iteratedFDeriv_zero_on_compl hx
      simpa only [hz] using (tendsto_const_nhds (x := (0 : Coord [×0]→L[ℝ] V)))
    have hvzero : v 0 x = 0 := tendsto_nhds_unique hlim hconst
    change C0 (v 0 x) = 0
    rw [hvzero, map_zero]
  let φ : ContDiffMapSupportedIn Coord V ⊤ K := ⟨g, hg, hzero⟩
  refine ⟨φ, ?_⟩
  funext k
  apply BoundedContinuousFunction.ext
  intro x
  change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ x = v k x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrFun (hjet k) x

theorem supportedSmooth_completeSpace (K : Compacts Coord) :
    CompleteSpace (ContDiffMapSupportedIn Coord V ⊤ K) :=
  (supportedJetMap_isUniformEmbedding (V := V) K).isUniformInducing.completeSpace
    (supportedJetMap_isClosed_range (V := V) K).isComplete

theorem supportedSmooth_completelyMetrizable (K : Compacts Coord) :
    IsCompletelyMetrizableSpace (ContDiffMapSupportedIn Coord V ⊤ K) := by
  have (k : ℕ) : IsCompletelyMetrizableSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := by
    have hc : CompleteSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := inferInstance
    refine ⟨⟨inferInstance, ?_, ?_⟩⟩
    · rfl
    · exact hc
  have : IsCompletelyMetrizableSpace (SupportedJetProduct V) := inferInstance
  have he : Topology.IsClosedEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
    ⟨(supportedJetMap_isUniformEmbedding K).isEmbedding, supportedJetMap_isClosed_range K⟩
  exact he.IsCompletelyMetrizableSpace

theorem symmetricPerturbation_completeSpace : CompleteSpace SymmetricPerturbation := by
  let : CompleteSpace SupportedTensor := supportedSmooth_completeSpace patchCompact
  let : IsClosed (symmetricSupportedSubmodule : Set SupportedTensor) :=
    symmetricSupportedSubmodule_isClosed
  infer_instance

theorem symmetricPerturbation_completelyMetrizable :
    IsCompletelyMetrizableSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SupportedTensor := supportedSmooth_completelyMetrizable patchCompact
  exact symmetricSupportedSubmodule_isClosed.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

theorem symmetricPerturbation_baire : BaireSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SymmetricPerturbation := symmetricPerturbation_completelyMetrizable
  infer_instance

end SmoothLocal.Perturbation

end

end OAI
