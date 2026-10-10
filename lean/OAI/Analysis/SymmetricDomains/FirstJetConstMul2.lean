import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectedChartCommonCOne

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

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem exists_actual_aut_firstJet_COne_neighborhood :
    ∃ P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
    ∃ e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)),
      (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)) ∧
      1∈e.source ∧
      (∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X)).val=
          completeGeneratorFirstJet hU hc hbd Γ hhol p X) ∧
      ∀ (p' : U) y, y∈e.target → ContDiffAt ℝ 1 (fun t => ambientFirstJet p' (e.symm t)) y := by
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
  obtain ⟨c,hce,hc1,hcC1⟩ := projected_chart_common_COne_restriction (E := R) e 1 he1
    F hF hF0 (by simpa only [he] using hd) hproj ambientFirstJet hjet
  exact ⟨P,c,hce.trans he,hc1,hP,hcC1⟩
end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU

theorem firstJet_mul_const_contDiffAt
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (hc : ContDiffAt ℝ 1 (fun t => ambientFirstJet (g.toHomeomorph p) (c t)) t₀) :
    ContDiffAt ℝ 1 (fun t => ambientFirstJet p (c t*g)) t₀ := by
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.contDiff (n := 1)).contDiffAt.comp t₀
    (hc.snd.prodMk (show ContDiffAt ℝ 1 (fun _ : E => g.derivativeAt p) t₀ from contDiffAt_const))
  have hpair := hc.fst.prodMk hB
  have he : (fun t => ambientFirstJet p (c t*g)) =
      (fun t => ((c t).ambientAut (g.toHomeomorph p).val,
        ((c t).derivativeAt (g.toHomeomorph p)).comp (g.derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · exact derivativeAt_mul hU (c t) g p
  rw [he]
  exact hpair

theorem firstJet_const_mul_contDiffAt
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (hc : ContDiffAt ℝ 1 (fun t => ambientFirstJet p (c t)) t₀) :
    ContDiffAt ℝ 1 (fun t => ambientFirstJet p (g*c t)) t₀ := by
  have hy : (c t₀).ambientAut p.val∈U := by
    rw [ambientAut_apply]
    exact ((c t₀).toHomeomorph p).property
  have hA := ((g.ambientAut_analytic hU _ hy).contDiffAt (n := 1)).restrict_scalars ℝ
  have hD := ((g.ambientAut_analytic hU _ hy).fderiv.contDiffAt (n := 1)).restrict_scalars ℝ
  have hAv := hA.comp t₀ hc.fst
  have hDv := hD.comp t₀ hc.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.contDiff (n := 1)).contDiffAt.comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have he : (fun t => ambientFirstJet p (g*c t)) =
      (fun t => (g.ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (c t) p
  rw [he]
  exact hpair
end Biholomorph
end Release061

end

end OAI
