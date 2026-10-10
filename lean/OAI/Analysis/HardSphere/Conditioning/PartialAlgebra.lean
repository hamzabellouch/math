import Mathlib
import OAI.Analysis.HardSphere.Operators.FreeResolventDenseRange
import OAI.Analysis.HardSphere.Geometry.GeneratorScalar

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

lemma smoothPartial_smooth {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    smoothPartial f p∈smoothAlgebra N L := by
  change ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ coordDerivative N L f.val p (project N L X))
  simp_rw [coordDerivative_project]
  have hf : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f.val (project N L X)) := f.property
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

def partialAlgebra {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    smoothAlgebra N L := ⟨smoothPartial f p,smoothPartial_smooth f p⟩

def smoothLaplacian {N : ℕ} {L : Length} (f : smoothAlgebra N L) : ScalarL2 N L :=
  -∑ p : Direction N, ContinuousMap.toLp 2 volume ℂ (smoothPartial (partialAlgebra f p) p)

lemma smooth_form_pairing {N : ℕ} {L : Length} {a : ℝ} {v : Jet N L}
    (hv : v∈dirichletDomain N L a) (f : smoothAlgebra N L) :
    (∑ p : Direction N, inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) (v.2 p))=
      inner ℂ (smoothLaplacian f) v.1 := by
  rw [smoothLaplacian,inner_neg_left,sum_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact eq_neg_of_add_eq_zero_left (weak_derivative hv (partialAlgebra f p) p)

def SmoothTest.asSmooth {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    smoothAlgebra N L := ⟨⟨f.toFun,f.continuous⟩,f.smooth⟩

lemma SmoothTest.scalar_toLp {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    f.jet.1=ContinuousMap.toLp 2 volume ℂ f.asSmooth.val := by
  apply Lp.ext
  exact f.memLp.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f.asSmooth.val).symm

lemma SmoothTest.derivative_toLp {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a)
    (p : Direction N) : f.jet.2 p=ContinuousMap.toLp 2 volume ℂ (smoothPartial f.asSmooth p) := by
  apply Lp.ext
  exact (f.partial_memLp p).coeFn_toLp.trans
    (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (smoothPartial f.asSmooth p)).symm

lemma SmoothTest.form_pairing {N : ℕ} {L : Length} {a b : ℝ} (f : SmoothTest N L a)
    {v : Jet N L} (hv : v∈dirichletDomain N L b) :
    (∑ p : Direction N, inner ℂ (f.jet.2 p) (v.2 p))=inner ℂ (smoothLaplacian f.asSmooth) v.1 := by
  simp_rw [f.derivative_toLp]
  exact smooth_form_pairing hv f.asSmooth

def SmoothTest.freeTest {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    SmoothTest N L (-1) where
  toFun := f.toFun
  smooth := f.smooth
  compact := f.compact
  support_allowed := by rw [allowed_of_neg N L (by norm_num : (-1:ℝ)<0)]; exact subset_univ _
  memLp := f.memLp
  partial_memLp := f.partial_memLp

lemma SmoothTest.free_resolvent {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    formResolvent N L (-1) (f.jet.1+smoothLaplacian f.asSmooth)=f.jet.1 := by
  let ug : hilbertDomain N L (-1) := ⟨(hilbertJetEquiv N L).symm f.jet,by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm f.jet)∈dirichletDomain N L (-1)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact subset_closure ⟨f.freeTest,rfl⟩⟩
  have heq : (scalarEmbedding N L (-1)).adjoint (f.jet.1+smoothLaplacian f.asSmooth)=ug := by
    apply ext_inner_right ℂ
    intro v
    rw [adjoint_inner_left,inner_add_left]
    change _=inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L)
    rw [hilbertJet_inner]
    have hgu : hilbertJetEquiv N L (ug : HilbertJet N L)=f.jet := by simp [ug]
    rw [hgu]
    congr 1
    exact (f.form_pairing v.property).symm
  change scalarEmbedding N L (-1) ((scalarEmbedding N L (-1)).adjoint _)=_
  rw [heq]
  change (hilbertJetEquiv N L ((hilbertJetEquiv N L).symm f.jet)).1=f.jet.1
  rw [ContinuousLinearEquiv.apply_symm_apply]

lemma SmoothTest.free_generator {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a)
    {ι : Type*} {l : Filter ι} {d : ι→ℝ} (hd : ∀ i,0<d i) (ht : Tendsto d l (𝓝 0)) :
    Tendsto (fun i ↦ ((d i)⁻¹ : ℂ) • (f.jet.1-freeTransition N L (d i) f.jet.1))
      l (𝓝 (smoothLaplacian f.asSmooth)) := by
  rcases subsingleton_or_nontrivial (ScalarL2 N L) with h | h
  · convert tendsto_const_nhds (x := smoothLaplacian f.asSmooth) using 1
  have hlim := heat_difference_resolvent_tendsto hd ht (formResolvent_isPositive N L (-1))
    (formResolvent_norm_le_one N L (-1)) (freeResolvent_denseRange N L (-1) (by norm_num))
    (f.jet.1+smoothLaplacian f.asSmooth)
  simp only [f.free_resolvent] at hlim
  change Tendsto (fun i ↦ ((d i)⁻¹:ℂ) • (f.jet.1-formHeat N L (-1) (d i) f.jet.1))
    l (𝓝 (f.jet.1+smoothLaplacian f.asSmooth-f.jet.1)) at hlim
  simp_rw [← freeTransition_eq_formHeat N L (-1) (by norm_num) (hd _)] at hlim
  simpa only [add_sub_cancel_left] using hlim

end HardSphere

end

end OAI
