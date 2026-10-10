import Mathlib
import OAI.Geometry.PrescribedPotential.AffineFamilyJets
import OAI.Geometry.PrescribedPotential.MetricFamilyBootstrap
import OAI.Geometry.PrescribedPotential.PathMetricCompactC1

namespace OAI

/-! Path Metric Bootstrap. -/

section

noncomputable section
open Set Filter Topology Matrix Metric Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open KaehlerCalculus EllipticKernel
variable {n : ℕ}
local instance pathMetricECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)
local instance pathMetricHMIP : InnerProductSpace ℝ (HM n) := InnerProductSpace.rclikeToReal ℂ (HM n)
def encodeCLM (n : ℕ) : (Fin n → Fin n → ℂ) →L[ℝ] HM n := (encode n).toContinuousLinearMap
lemma encoded_fderiv_bound {M : V n → Fin n → Fin n → ℂ} {x : EC n}
    (hM : ContDiffAt ℝ ∞ M (coordinateEquiv n x)) :
    ‖fderiv ℝ (fun y => encode n (M (coordinateEquiv n y))) x‖ ≤
      ‖encodeCLM n‖*‖fderiv ℝ M (coordinateEquiv n x)‖*‖(coordinateEquiv n).toContinuousLinearMap‖ := by
  have hd := (encode n).hasFDerivAt.comp x ((hM.differentiableAt (by simp)).hasFDerivAt.comp x (coordinateEquiv n).hasFDerivAt)
  have hn := congrArg norm hd.fderiv
  calc
    _ = _ := hn
    _ ≤ _ := ((encodeCLM n).opNorm_comp_le _).trans
      (by nlinarith [ContinuousLinearMap.opNorm_comp_le (fderiv ℝ M (coordinateEquiv n x)) (coordinateEquiv n).toContinuousLinearMap,
        norm_nonneg (encodeCLM n)])
end MetricSystem
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel MetricSystem HigherJet
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  {A : ComplexAtlas d X}
local instance pathBootstrapECIP : InnerProductSpace ℝ (EC d) := InnerProductSpace.rclikeToReal ℂ (EC d)
local instance pathBootstrapHMIP : InnerProductSpace ℝ (HM d) := InnerProductSpace.rclikeToReal ℂ (HM d)

lemma path_metric_higher_bounds (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) :
    ∀ m, 1 ≤ m → ∀ K : Set (EC d), IsCompact K → K ⊆ (A.euclideanChart i).target →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : PathSolution g h) x, x ∈ K →
        ‖iteratedFDeriv ℝ m (fun y => encode d (s.metric.matrix i (coordinateEquiv d y))) x‖ ≤ C := by
  let U := (A.euclideanChart i).target
  have hU : IsOpen U := (A.euclideanChart i).open_target
  have hc (x : EC d) : x ∈ U → coordinateEquiv d x ∈ (A.chart i).target := by
    intro hx
    simpa only [U,ComplexAtlas.euclideanChart_target,Set.mem_preimage] using hx
  let f : EC d → HM d := fun x => encode d ((g.localField i).ricciHessian (coordinateEquiv d x))
  let q : EC d → HM d := fun x => encode d (PotentialKaehler.potentialMatrix (h.weight i) (coordinateEquiv d x))
  have hf : ContDiffOn ℝ ∞ f U := by
    intro x hx
    exact ((encode d).contDiff.contDiffAt.comp x (((g.localField i).ricciHessian_smooth.contDiffAt
      ((A.chart i).open_target.mem_nhds (hc x hx))).comp x (coordinateEquiv d).contDiff.contDiffAt)).contDiffWithinAt
  have hq : ContDiffOn ℝ ∞ q U := by
    intro x hx
    exact ((encode d).contDiff.contDiffAt.comp x ((PotentialKaehler.potentialMatrix_smooth
      ((h.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds (hc x hx)))).comp x
      (coordinateEquiv d).contDiff.contDiffAt)).contDiffWithinAt
  let r : PathSolution g h → EC d → HM d := fun s x => (1-s.t) • f x-s.t • q x
  apply metric_family_bootstrap hU (fun s : PathSolution g h => s.metric.localField i) r
    (fun _ x hx => hc x hx) (fun s => (hf.const_smul (1-s.t)).sub (hq.const_smul s.t))
  · intro s x hx
    have he := volumePath_logdet_hessian g h s.solves s.solves.choose i (hc x hx)
    change encode d (PotentialKaehler.potentialMatrix (fun y => Real.log (s.metric.matrix i y).det.re) (coordinateEquiv d x)) = _
    have hh := congrArg (encode d) he
    calc
      _ = encode d (pathLogDetHessian g h i s.t (coordinateEquiv d x)) := hh
      _ = _ := ?_
    change encode d ((1-s.t) • (g.localField i).ricciHessian (coordinateEquiv d x)-s.t • PotentialKaehler.potentialMatrix (h.weight i) (coordinateEquiv d x)) = _
    rw [map_sub,map_smul,map_smul]
  · intro K hK hKU
    obtain ⟨C,hC,hbound⟩ := path_metric_compact_C1 g h i hK hKU
    refine ⟨‖encodeCLM d‖*C*‖(coordinateEquiv d).toContinuousLinearMap‖,fun s x hx => ?_⟩
    apply (encoded_fderiv_bound ((s.metric.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds (hc x (hKU hx))))).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound s x hx).2 (norm_nonneg _)) (norm_nonneg _)
  · intro K hK hKU
    obtain ⟨R,H,hR,hH,hell⟩ := volumePath_relative_ellipticity g h
    let L := coordinateEquiv d '' K
    have hL : IsCompact L := hK.image (coordinateEquiv d).continuous
    have hLU : L ⊆ (A.chart i).target := by rintro _ ⟨x,hx,rfl⟩; exact hc x (hKU hx)
    obtain ⟨B,hB,hbound⟩ := compact_normalizing_frames hL (g.matrix i)
      ((g.smooth i).continuousOn.mono hLU) (fun z hz => g.positive i z (hLU hz)) hR.le hH.le
    refine ⟨B,hB,fun s x hx C D hCD hDC hN => ?_⟩
    obtain ⟨hl,hu⟩ := hell s.t s.b s.potential s.time s.solves i _ (hc x (hKU hx))
    exact hbound _ ⟨x,hx,rfl⟩ _ C D hl hu hCD hN
  · intro m K hK hKU
    obtain ⟨C,hbound⟩ := affine_family_jets hU hf hq m hK hKU
    exact ⟨C,fun j hj s x hx => hbound j hj s.t s.time x hx⟩
end Anticanonical.SourceSmooth

end
end

end OAI
