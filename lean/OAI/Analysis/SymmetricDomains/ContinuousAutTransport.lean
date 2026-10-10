import Mathlib
import OAI.Analysis.SymmetricDomains.OpenChartLeftTranslate

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

namespace Biholomorph

section
open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_chart_nonzero_translation_jacobian :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ (g h : Biholomorph U U) y, y∈e.target →
        ContDiffAt ℝ 1 (fun t => e (g*e.symm t*h)) y) ∧
      ∀ (g : Biholomorph U U) y, y∈e.target → g*e.symm y∈e.source →
        LinearMap.det (M := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
          (fderiv ℝ (fun t => e (g*e.symm t)) y).toLinearMap ≠ 0 := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨P,e,he,he1,_,hC⟩ := exists_actual_aut_chart_COne_translations hU hc hbd Γ hhol p
  refine ⟨P,e,he,he1,hC,?_⟩
  intro g y hy hg
  apply openChart_leftTranslate_det_ne_zero (E := R) e _ g y hy hg
  intro a t ht
  simpa only [mul_one] using hC a 1 t ht
end

open Set Filter Topology

variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def autTransport (e : Biholomorph U D) (a : Biholomorph U U) : Biholomorph D D :=
  (e.symm.trans a).trans e

@[simp] theorem autTransport_apply (e : Biholomorph U D) (a : Biholomorph U U) (p : D) :
    (autTransport e a).toHomeomorph p=
      e.toHomeomorph (a.toHomeomorph (e.toHomeomorph.symm p)) := rfl

@[simp] theorem autTransport_one (e : Biholomorph U D) : autTransport e 1=1 := by
  apply Biholomorph.ext
  intro p
  exact e.toHomeomorph.apply_symm_apply p

@[simp] theorem autTransport_mul (e : Biholomorph U D) (a b : Biholomorph U U) :
    autTransport e (a*b)=autTransport e a*autTransport e b := by
  apply Biholomorph.ext
  intro p
  simp only [autTransport_apply,mul_apply,e.toHomeomorph.symm_apply_apply]

@[simp] theorem autTransport_inv (e : Biholomorph U D) (a : Biholomorph U U) :
    autTransport e a⁻¹=(autTransport e a)⁻¹ := rfl

@[simp] theorem autTransport_symm_cancel (e : Biholomorph U D) (a : Biholomorph U U) :
    autTransport e.symm (autTransport e a)=a := by
  apply Biholomorph.ext
  intro p
  change e.toHomeomorph.symm (e.toHomeomorph (a.toHomeomorph
    (e.toHomeomorph.symm (e.toHomeomorph p))))=a.toHomeomorph p
  simp only [e.toHomeomorph.symm_apply_apply]

theorem continuous_of_joint_evaluation {T : Type*} [TopologicalSpace T]
    (a : T → Biholomorph U U)
    (hf : Continuous fun p : T × U => (a p.1).toHomeomorph p.2)
    (hi : Continuous fun p : T × U => (a p.1).toHomeomorph.symm p.2) :
    Continuous a := by
  apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
  exact (ContinuousMap.continuous_of_continuous_uncurry _ hf).prodMk
    (ContinuousMap.continuous_of_continuous_uncurry _ hi)

theorem continuous_joint_evaluation [LocallyCompactSpace U] :
    Continuous fun p : Biholomorph U U × U => p.1.toHomeomorph p.2 := by
  exact continuous_eval.comp
    ((continuous_compactOpenPair.fst.comp continuous_fst).prodMk continuous_snd)

theorem continuous_joint_inverse_evaluation [LocallyCompactSpace U] :
    Continuous fun p : Biholomorph U U × U => p.1.toHomeomorph.symm p.2 := by
  exact continuous_eval.comp
    ((continuous_compactOpenPair.snd.comp continuous_fst).prodMk continuous_snd)

theorem continuous_autTransport [LocallyCompactSpace U]
    (e : Biholomorph U D) : Continuous (autTransport e) := by
  apply continuous_of_joint_evaluation
  · exact e.toHomeomorph.continuous.comp (continuous_joint_evaluation.comp
      (continuous_fst.prodMk (e.toHomeomorph.symm.continuous.comp continuous_snd)))
  · exact e.toHomeomorph.continuous.comp (continuous_joint_inverse_evaluation.comp
      (continuous_fst.prodMk (e.toHomeomorph.symm.continuous.comp continuous_snd)))

end Biholomorph
end Release061

end

end OAI
