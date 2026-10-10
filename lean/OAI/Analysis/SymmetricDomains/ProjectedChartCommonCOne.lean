import Mathlib
import OAI.Analysis.SymmetricDomains.CompleteGeneratorJetProjection
import OAI.Analysis.SymmetricDomains.ProjectedChartObservableStrict
import OAI.Analysis.SymmetricDomains.FiniteFlowParametrization
import OAI.Analysis.SymmetricDomains.ProjectedChartObservableCont

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
open Set Filter Topology Metric
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_firstJet_COne_chart :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      ∀ p' : U, ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) (e 1) := by
  let R : Type := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  let _ : CompleteSpace R := FiniteDimensional.complete ℝ R
  obtain ⟨P,hP,hPinj⟩ := exists_complete_generator_jet_projection hU hbd Γ hhol p hc
  obtain ⟨W,hW,hinj⟩ := projected_firstJet_locally_injective (E := R)
    hU hc.isPreconnected hbd Γ hhol p P hPinj
  obtain ⟨F,hF,hF0,hd,_,hreg⟩ := exists_finite_flow_parametrization_with_regular_jets hU hc hbd Γ hhol p P hP
  obtain ⟨e,he,he1⟩ := openChart_of_projected_parametrization (A := Biholomorph U U) (E := R)
    (fun a => P (ambientFirstJet p a)) (P.continuous.comp (ambientFirstJet_continuous hU p))
    1 W hW hinj F hF hF0 hd
  have hjet (p' : U) : ContDiff ℝ 1 (fun t : R => ambientFirstJet p' (F t)) :=
    contDiff_one_of_everywhere_strict _ (hreg p')
  have hproj : ContDiffAt ℝ 1 (fun t : R => e (F t)) 0 := by
    have hPdiff := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R) P
    simpa only [Function.comp_def,he] using (hPdiff.comp (hjet p)).contDiffAt (x := (0:R))
  refine ⟨P,e,he,he1,hP,?_⟩
  intro p'
  apply projected_chart_observable_contDiffAt (E := R) e 1 he1 F hF hF0 _ hproj
    (ambientFirstJet p') (hjet p').contDiffAt
  simpa only [he] using hd
end Biholomorph

open Set Filter Topology

theorem projected_chart_common_COne_restriction
    {A : Type*} [TopologicalSpace A] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : OpenPartialHomeomorph A E) (a : A) (ha : a∈e.source)
    (F : E → A) (hF : Continuous F) (hF0 : F 0=a)
    (hd : HasStrictFDerivAt (fun x => e (F x)) (ContinuousLinearMap.id ℝ E) 0)
    (hD : ContDiffAt ℝ 1 (fun x => e (F x)) 0)
    {Q : Type*} (G : Q → A → H) (hG : ∀ q, ContDiff ℝ 1 (fun x => G q (F x))) :
    ∃ c : OpenPartialHomeomorph A E, (c : A → E)=e ∧ a∈c.source ∧
      ∀ q y, y∈c.target → ContDiffAt ℝ 1 (fun t => G q (c.symm t)) y := by
  have hd' : HasStrictFDerivAt (fun x => e (F x))
      ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) 0 := hd
  let I := hd'.localInverse (fun x => e (F x)) (ContinuousLinearEquiv.refl ℝ E) 0
  have hI : HasStrictFDerivAt I (ContinuousLinearMap.id ℝ E) (e a) := by
    simpa [I,hF0] using hd'.to_localInverse
  have hIC1 : ContDiffAt ℝ 1 I (e a) := by
    simpa only [ContDiffAt.localInverse,hF0] using hD.to_localInverse hd'.hasFDerivAt (by decide : (1 : WithTop ℕ∞)≠0)
  have hI0 : I (e a)=0 := by
    simpa only [hF0] using hd'.localInverse_apply_image
  have hFI : Tendsto (fun y => F (I y)) (𝓝 (e a)) (𝓝 a) := by
    have ht := hF.continuousAt.tendsto.comp hI.continuousAt.tendsto
    simpa only [Function.comp_def,hI0,hF0] using ht
  have hmem : ∀ᶠ y in 𝓝 (e a), F (I y)∈e.source :=
    hFI (e.open_source.mem_nhds ha)
  have hright : ∀ᶠ y in 𝓝 (e a), e (F (I y))=y := by
    simpa only [hF0] using hd'.eventually_right_inverse
  have hgood : ∀ᶠ y in 𝓝 (e a), ContDiffAt ℝ 1 I y ∧ F (I y)∈e.source ∧ e (F (I y))=y := by
    filter_upwards [hIC1.eventually (by simp),hmem,hright] with y hy hm hr using ⟨hy,hm,hr⟩
  obtain ⟨W,hW,hWo,haW⟩ := _root_.mem_nhds_iff.mp hgood
  let c : OpenPartialHomeomorph A E := (e.symm.restrOpen W hWo).symm
  have hac : a∈c.source := by
    have hh := (e.symm.restrOpen W hWo).map_source (show e a∈e.target∩W from ⟨e.map_source ha,haW⟩)
    change a∈(e.symm.restrOpen W hWo).target
    simpa only [OpenPartialHomeomorph.coe_restrOpen,e.left_inv ha] using hh
  refine ⟨c,rfl,hac,?_⟩
  intro q y hy
  have hyW : y∈W := hy.2
  have hcomp : ContDiffAt ℝ 1 (fun t => G q (F (I t))) y :=
    (hG q).contDiffAt.comp y (hW hyW).1
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hWo.mem_nhds hyW] with t ht
  have hs := (hW ht).2
  have he : e.symm t=F (I t) := by
    calc
      e.symm t=e.symm (e (F (I t))) := congrArg e.symm hs.2.symm
      _=F (I t) := e.left_inv hs.1
  change G q (e.symm t)=G q (F (I t))
  rw [he]
end Release061

end

end OAI
