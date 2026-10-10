import Mathlib
import OAI.Analysis.SymmetricDomains.SmallAutomorphismsHaveNonzero

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def ambientFirstJet (p : U) (a : Biholomorph U U) :
    Affine n × (Affine n →L[ℂ] Affine n) := (a.ambientAut p.val,a.derivativeAt p)

theorem ambientFirstJet_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (ambientFirstJet p) := by
  have hv : Continuous (fun a : Biholomorph U U => a.ambientAut p.val) := by
    simpa only [Function.comp_def,ambientAut_apply] using continuous_subtype_val.comp (continuous_evaluation p)
  exact hv.prodMk (derivativeAt_continuous hU p)

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (p : U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU hc hbd Γ hhol

theorem projected_jet_sequences_not_coincident
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (hP : ∀ X : Affine n → Affine n, IsCompleteGenerator U X →
      P (X p.val,fderiv ℂ X p.val)=0 → X=0)
    (a b : ℕ → Biholomorph U U) (ha : Tendsto a atTop (𝓝 1))
    (hb : Tendsto b atTop (𝓝 1)) (hne : ∀ i, a i≠b i)
    (heq : ∀ i, P (ambientFirstJet p (a i))=P (ambientFirstJet p (b i))) : False := by
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.property)
  let q : ℕ → Biholomorph U U := fun i => a i*(b i)⁻¹
  have hq : Tendsto q atTop (𝓝 1) := by simpa only [mul_one,inv_one] using ha.mul hb.inv
  have hqne (i : ℕ) : q i≠1 := by
    intro he
    apply hne i
    calc
      a i = q i*b i := by simp [q]
      _ = b i := by rw [he,one_mul]
  obtain ⟨h,hp,hh,X,hX,hXne,φ,hφ,hconv⟩ := small_automorphisms_have_nonzero_complete_tangent
    hU hc hbd Γ hhol q hq hqne p hR hRU
  let y : ℕ → U := fun i => (b (φ i)).toHomeomorph p
  have hy : Tendsto (fun i => (y i).val) atTop (𝓝 p.val) := by
    simpa only [Function.comp_def,one_apply,y] using
      (continuous_subtype_val.comp (continuous_evaluation p)).continuousAt.tendsto.comp (hb.comp hφ.tendsto_atTop)
  have hyb : Tendsto (fun i => (y i).val) atTop (𝓝[ball p.val R] p.val) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy,hy (ball_mem_nhds _ hR)⟩
  let f : ℕ → Affine n → Affine n := fun i x => (h (φ i))⁻¹ • ((q (φ i)).ambientAut x-x)
  have hfd (i : ℕ) : DifferentiableOn ℂ (f i) U := by
    intro x hx
    exact ((((q (φ i)).ambientAut_analytic hU x hx).differentiableAt.sub differentiableAt_id).const_smul (h (φ i))⁻¹).differentiableWithinAt
  have hder := tendstoLocallyUniformlyOn_fderiv isOpen_ball hconv
    (fun x hx => ⟨ball p.val R,isOpen_ball.mem_nhds hx,Eventually.of_forall
      (fun i => (hfd i).mono (ball_subset_closedBall.trans hRU))⟩)
  have hXa := hX.analyticOnNhd hU hbd
  have hval := hconv.tendsto_comp (hXa p.val p.property).continuousAt.continuousWithinAt (mem_ball_self hR) hyb
  have hd := hder.tendsto_comp (hXa p.val p.property).fderiv.continuousAt.continuousWithinAt (mem_ball_self hR) hyb
  have hDb : Tendsto (fun i => (b (φ i)).derivativeAt p) atTop (𝓝 1) := by
    simpa only [Function.comp_def,derivativeAt_one hU] using
      (derivativeAt_continuous hU p).continuousAt.tendsto.comp (hb.comp hφ.tendsto_atTop)
  have hcomp : Continuous (fun z : (Affine n →L[ℂ] Affine n) × (Affine n →L[ℂ] Affine n) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have hj := hval.prodMk_nhds (hcomp.continuousAt.tendsto.comp (hd.prodMk_nhds hDb))
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id] at hj
  have hv (i : ℕ) : f i (y i).val=(h (φ i))⁻¹ • ((a (φ i)).ambientAut p.val-(b (φ i)).ambientAut p.val) := by
    have hab : q (φ i)*b (φ i)=a (φ i) := by simp [q]
    dsimp only [f]
    rw [ambientAut_apply (q (φ i)) (y i),ambientAut_apply (b (φ i)) p]
    congr 2
    change ((q (φ i)*b (φ i)).toHomeomorph p).val=(a (φ i)).ambientAut p.val
    rw [hab,ambientAut_apply]
  have hD (i : ℕ) : (fderiv ℂ (f i) (y i).val).comp ((b (φ i)).derivativeAt p)=
      (h (φ i))⁻¹ • ((a (φ i)).derivativeAt p-(b (φ i)).derivativeAt p) := by
    have hab : q (φ i)*b (φ i)=a (φ i) := by simp [q]
    have hmul := derivativeAt_mul hU (q (φ i)) (b (φ i)) p
    rw [hab] at hmul
    change (fderiv ℂ ((h (φ i))⁻¹ • ((q (φ i)).ambientAut-id)) (y i).val).comp ((b (φ i)).derivativeAt p) = _
    rw [fderiv_const_smul (((q (φ i)).ambientAut_analytic hU (y i).val (y i).property).differentiableAt.sub differentiableAt_id),
      fderiv_sub ((q (φ i)).ambientAut_analytic hU (y i).val (y i).property).differentiableAt differentiableAt_id,fderiv_id]
    simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.id_comp]
    change (a (φ i)).derivativeAt p=(fderiv ℂ (q (φ i)).ambientAut (y i).val).comp ((b (φ i)).derivativeAt p) at hmul
    rw [←hmul]
  have hj' : Tendsto (fun i => (h (φ i))⁻¹ • (ambientFirstJet p (a (φ i))-ambientFirstJet p (b (φ i))))
      atTop (𝓝 (X p.val,fderiv ℂ X p.val)) := by
    convert hj using 1
    funext i
    exact Prod.ext (hv i).symm (hD i).symm
  have ht := P.continuous.continuousAt.tendsto.comp hj'
  have hz (i : ℕ) : P ((h (φ i))⁻¹ • (ambientFirstJet p (a (φ i))-ambientFirstJet p (b (φ i))))=0 := by
    rw [map_smul,map_sub,heq,sub_self,smul_zero]
  simp only [Function.comp_def,hz] at ht
  exact hXne (hP X hX (tendsto_nhds_unique ht tendsto_const_nhds))
end Biholomorph
end Release061

end

end OAI
