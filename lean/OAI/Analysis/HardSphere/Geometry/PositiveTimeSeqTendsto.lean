import Mathlib
import OAI.Analysis.HardSphere.Geometry.BufferedAllowed
import OAI.Analysis.HardSphere.PathBounds.PathTailConstant
import OAI.Analysis.HardSphere.Conditioning.PartialAlgebra

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology

lemma positiveTimeSeq_tendsto :
    Tendsto (fun n : ℕ ↦ 1/((n:ℝ)+1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun _ ↦ by simp only [mem_Ioi]; positivity⟩

lemma SmoothTest.killed_generator {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    Tendsto (fun n : ℕ ↦ (((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) •
      (f.jet.1-killedTransition N L a (1/((n:ℝ)+1)) f.jet.1))
      atTop (𝓝 (smoothLaplacian f.asSmooth)) := by
  have ht := positiveTimeSeq_tendsto
  have hb := (killedTransition_free_firstOrder N L a f.asSmooth.val f.support_allowed).comp ht
  rw [← f.scalar_toLp] at hb
  have hf := f.free_generator (fun n : ℕ ↦ by positivity : ∀ n : ℕ,0<1/((n:ℝ)+1))
    tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_inv] at hb
  have h := hf.sub hb
  simp only [sub_zero] at h
  convert h using 1
  funext n
  dsimp only [Function.comp_apply]
  simp only [Complex.ofReal_inv]
  module

lemma SmoothTest.allowedProjection {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    allowedProjection N L a f.jet.1=f.jet.1 := by
  apply Lp.ext
  filter_upwards [allowedProjection_ae N L a f.jet.1,f.memLp.coeFn_toLp] with X hP hf
  rw [hP]
  by_cases hX : X∈allowed N L a
  · rw [Set.indicator_of_mem hX]
  · rw [Set.indicator_of_notMem hX]
    change 0=f.memLp.toLp f.toFun X
    rw [hf]
    exact (image_eq_zero_of_notMem_tsupport (fun hs ↦ hX (f.support_allowed hs))).symm

lemma SmoothTest.killedLaplace_pairing {N : ℕ} {L : Length} {a : ℝ} (g : SmoothTest N L a)
    (f : ScalarL2 N L) :
    inner ℂ (smoothLaplacian g.asSmooth) (killedLaplace N L a f)=
      inner ℂ g.jet.1 f-inner ℂ g.jet.1 (killedLaplace N L a f) := by
  let u := killedLaplace N L a f
  have hL := g.killed_generator.inner (𝕜 := ℂ) (tendsto_const_nhds (x := u))
  have hR := (tendsto_const_nhds (x := g.jet.1)).inner (𝕜 := ℂ)
    ((killedLaplace_difference_tendsto N L a f).comp positiveTimeSeq_tendsto)
  have he (n : ℕ) : inner ℂ ((((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) •
      (g.jet.1-killedTransition N L a (1/((n:ℝ)+1)) g.jet.1)) u=
      inner ℂ g.jet.1 ((((1/((n:ℝ)+1))⁻¹:ℝ):ℂ) • (u-killedTransition N L a (1/((n:ℝ)+1)) u)) := by
    rw [inner_smul_left,inner_smul_right,inner_sub_left,inner_sub_right]
    have hs : inner ℂ ((killedTransition N L a (1/((n:ℝ)+1))) g.jet.1) u =
        inner ℂ g.jet.1 ((killedTransition N L a (1/((n:ℝ)+1))) u) :=
      (isSelfAdjoint_iff_isSymmetric.mp (killedTransition_selfAdjoint N L a (1/((n:ℝ)+1)))) g.jet.1 u
    rw [hs]
    simp only [Complex.conj_ofReal]
  simp_rw [he] at hL
  simp only [Complex.ofReal_inv] at hL
  have hh := tendsto_nhds_unique hL hR
  rw [inner_sub_right] at hh
  have hp : inner ℂ g.jet.1 (HardSphere.allowedProjection N L a f)=inner ℂ g.jet.1 f := by
    rw [← killedTransition_zero]
    have hs : inner ℂ (killedTransition N L a 0 g.jet.1) f=
        inner ℂ g.jet.1 (killedTransition N L a 0 f) :=
      (isSelfAdjoint_iff_isSymmetric.mp (killedTransition_selfAdjoint N L a 0)) g.jet.1 f
    rw [← hs]
    rw [killedTransition_zero,g.allowedProjection]
  exact hh.trans (by rw [hp])

lemma killedLaplace_variational {N : ℕ} {L : Length} {a : ℝ} (f : ScalarL2 N L)
    {u : hilbertDomain N L a} (hu : scalarEmbedding N L a u=killedLaplace N L a f)
    {v : Jet N L} (hv : v∈dirichletDomain N L a) :
    inner ℂ v.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
      (∑ p : Direction N,inner ℂ (v.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
      inner ℂ v.1 f := by
  have hc : IsClosed {w : Jet N L | inner ℂ w.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
      (∑ p : Direction N,inner ℂ (w.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
      inner ℂ w.1 f} := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  apply closure_minimal (t := {w : Jet N L | _}) ?_ hc hv
  rintro _ ⟨g,rfl⟩
  change inner ℂ g.jet.1 (hilbertJetEquiv N L (u : HilbertJet N L)).1+
    (∑ p : Direction N,inner ℂ (g.jet.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=_
  have hp := g.form_pairing u.property
  change (∑ p : Direction N,inner ℂ (g.jet.2 p) ((hilbertJetEquiv N L (u : HilbertJet N L)).2 p))=
    inner ℂ (smoothLaplacian g.asSmooth) (scalarEmbedding N L a u) at hp
  rw [hp,hu]
  change inner ℂ g.jet.1 (scalarEmbedding N L a u)+_=_
  rw [hu,g.killedLaplace_pairing]
  abel

lemma killedLaplace_eq_formResolvent (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    killedLaplace N L a f=formResolvent N L a f := by
  obtain ⟨u,hu,_⟩ := killedLaplace_graph N L a f
  have he : u=(scalarEmbedding N L a).adjoint f := by
    apply ext_inner_left ℂ
    intro v
    rw [adjoint_inner_right]
    change inner ℂ (v : HilbertJet N L) (u : HilbertJet N L)=_
    rw [hilbertJet_inner]
    exact killedLaplace_variational f hu v.property
  rw [← hu,he]
  rfl

end HardSphere

end

end OAI
