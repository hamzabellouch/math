import Mathlib
import OAI.Analysis.SymmetricDomains.Vector

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Flatten
open Set Filter
open scoped Topology

def realEmbedding (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

def realPart (k : ℕ) : (Fin k → ℂ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i))

def imaginaryPart (k : ℕ) : (Fin k → ℂ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => Complex.imCLM.comp (ContinuousLinearMap.proj i))

lemma complexLinear_zero_of_real {k m : ℕ} (L : (Fin k → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : ∀ x : Fin k → ℝ, L (realEmbedding k x) = 0) : L = 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro z
  have hsingle (i : Fin k) : realEmbedding k (Pi.single i 1) = Pi.single i (1 : ℂ) := by
    ext j
    by_cases hji : j = i <;> simp [realEmbedding,hji]
  have he : z = ∑ i : Fin k, (z i) • realEmbedding k (Pi.single i 1) := by
    ext j
    simp [hsingle,Finset.sum_apply,Pi.single_apply]
  rw [he,map_sum]
  simp only [map_smul,h,smul_zero,Finset.sum_const_zero,zero_apply]

lemma complexification_deriv_zero {k m : ℕ} {f : (Fin k → ℝ) → Fin m → ℝ}
    {g : (Fin k → ℂ) → Fin m → ℂ} (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), g (realEmbedding k x) = realEmbedding m (f x))
    (hf : HasFDerivAt f (0 : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ)) 0) : HasFDerivAt g (0 : (Fin k → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
  have hg' := hg.differentiableAt.hasFDerivAt
  have h1 := ((hg'.restrictScalars ℝ).comp 0 (realEmbedding k).hasFDerivAt)
  have h2 := ((realEmbedding m).hasFDerivAt.comp 0 hf)
  have h3 : (fderiv ℂ g 0).restrictScalars ℝ ∘L realEmbedding k = 0 := by
    have h1' : HasFDerivAt (fun x => realEmbedding m (f x))
        ((fderiv ℂ g 0).restrictScalars ℝ ∘L realEmbedding k) 0 :=
      h1.congr_of_eventuallyEq (he.mono fun x hx => hx.symm)
    simpa using h1'.unique h2
  have hzero : fderiv ℂ g 0 = 0 := by
    apply complexLinear_zero_of_real
    intro x
    exact congrArg (fun L : (Fin k → ℝ) →L[ℝ] (Fin m → ℂ) => L x) h3
  simpa only [hzero] using hg'

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

theorem horizontal_graph_complexification {k : ℕ} {φ : (Fin k → ℝ) → Fin k → ℝ}
    (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0) (hdφ : HasFDerivAt φ (0 : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0) :
    ∃ e : OpenPartialHomeomorph (Fin k → ℂ) (Fin k → ℂ),
      (0 : Fin k → ℂ) ∈ e.source ∧ e 0 = 0 ∧
      AnalyticAt ℂ e 0 ∧ AnalyticAt ℂ e.symm 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
        e (realEmbedding k x) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ) := by
  obtain ⟨Φ,hΦ,hΦeq⟩ := Release061.Complexify.vector hφ
  have hEq : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), Φ (realEmbedding k x) = realEmbedding k (φ x) := hΦeq
  have hΦ0 : Φ 0 = 0 := by
    have h := hEq.self_of_nhds
    simpa only [map_zero,hφ0] using h
  have hΦd := complexification_deriv_zero hΦ hEq hdφ
  let Q : (Fin k → ℂ) → Fin k → ℂ := fun z => z + Complex.I • Φ z
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.add (hΦ.const_smul (c := Complex.I))
  have hQ0 : Q 0 = 0 := by simp only [Q,hΦ0,smul_zero,add_zero]
  have hQd : HasFDerivAt Q (ContinuousLinearEquiv.refl ℂ (Fin k → ℂ)).toContinuousLinearMap 0 := by
    simpa [Q] using
      (hasFDerivAt_id (𝕜 := ℂ) (0 : Fin k → ℂ)).add (hΦd.const_smul Complex.I)
  have hs : HasStrictFDerivAt Q (ContinuousLinearEquiv.refl ℂ (Fin k → ℂ)).toContinuousLinearMap 0 := by
    simpa only [hQd.fderiv] using hQa.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph Q
  have he : (e : (Fin k → ℂ) → Fin k → ℂ) = Q := hs.toOpenPartialHomeomorph_coe
  have hem : (0 : Fin k → ℂ) ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  obtain ⟨p,hp⟩ := hQa
  have hc : p 1 = (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).symm
      (ContinuousLinearEquiv.refl ℂ _).toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ (Fin k → ℂ) (Fin k → ℂ)).injective
    simpa using hp.hasFDerivAt.unique hQd
  have hia := (e.hasFPowerSeriesAt_symm hem (he ▸ hp) hc).analyticAt
  refine ⟨e,hem,by rw [he,hQ0],he ▸ hp.analyticAt,?_,?_⟩
  · simpa only [he,hQ0] using hia
  · filter_upwards [hEq] with x hx
    rw [he]
    dsimp [Q]
    rw [hx]
    rfl

end Release061.Flatten

end

end OAI
