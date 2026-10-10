import Mathlib
import OAI.Geometry.PrescribedPotential.CutoffHigher
import OAI.Geometry.PrescribedRicci.CalabiMetricC1
import OAI.Geometry.PrescribedRicci.CompactPathBounds
import OAI.Geometry.PrescribedRicci.CutoffJetBound
import OAI.Geometry.PrescribedRicci.LocalizedPathData

namespace OAI

/-! Path Localized Metric Bounds. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical ComplexOrder MatrixOrder Matrix.Norms.Elementwise ENNReal
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart TameInterpolation MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
  {g : KaehlerMetric A}

omit [ConnectedSpace X] in
lemma cutMetric_uniform_sobolev (line : SemipositiveAnticanonicalMetric A) (q : Fin A.count)
    (σ τ : ChartCutoff (A.euclideanChart q).target)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (k : ℕ) (hF : UniformSobolev ((k:ℝ)+2) (fun z : g.NormalizedPathSolution line =>
      localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal z.potential))) (i j : Fin d) :
    UniformSobolev (k:ℝ) (fun z : g.NormalizedPathSolution line =>
      cutMetric (g.deform z.potential z.positive) q σ i j) := by
  simp_rw [cutMetric_deform g q σ τ hτ]
  exact (UniformSobolev.const _ _).add
    ((hF.of_coreBound (hessianEntrySchwartz_bound (k:ℝ) i j)).of_coreBound
      (coreBound_product_integer σ.val k))

lemma cutMetric_uniform_C1 (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : g.NormalizedPathSolution line, ∀ i j : Fin d,
      (∀ y, ‖cutMetric (g.deform z.potential z.positive) q σ i j y‖ ≤ B) ∧
      (∀ a y, ‖fderiv ℝ (cutMetric (g.deform z.potential z.positive) q σ i j) y
        (stdOrthonormalBasis ℝ (EC d) a)‖ ≤ B) := by
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (BasisIndex d) := ⟨⟨0,Module.finrank_pos⟩⟩
  let K := coordinateEquiv d '' tsupport (σ : EC d → ℂ)
  have hK : IsCompact K := σ.compact.image (coordinateEquiv d).continuous
  have hKt : K ⊆ (A.chart q).target := by
    rintro _ ⟨y,hy,rfl⟩
    simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using σ.support_sub hy
  obtain ⟨M,hM,hm⟩ := g.volumePath_metric_bounds_on_compact line hd q hK hKt
  obtain ⟨P,hP,hp⟩ := g.volumePath_metric_C1_on_compact line hd q hK hKt
  let Q := P*‖(coordinateEquiv d).toContinuousLinearMap‖
  have hQ : 0 ≤ Q := mul_nonneg hP.le (norm_nonneg _)
  let f (z : g.NormalizedPathSolution line) (i j : Fin d) (y : EC d) :=
    (g.deform z.potential z.positive).matrix q (coordinateEquiv d y) i j
  have hs (z : g.NormalizedPathSolution line) (i j : Fin d) :
      ContDiffOn ℝ ∞ (f z i j) (A.euclideanChart q).target :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (GluingData.metric_euclidean_smooth _ q) i) j
  have h0 (i j : Fin d) (z : g.NormalizedPathSolution line) (y : EC d)
      (hy : y ∈ tsupport (σ : EC d → ℂ)) : ‖f z i j y‖ ≤ M :=
    (norm_entry_le_entrywise_sup_norm ((g.deform z.potential z.positive).matrix q (coordinateEquiv d y))).trans
      (hm z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation _
        (mem_image_of_mem _ hy)).1
  have h1 (i j : Fin d) (z : g.NormalizedPathSolution line) (y : EC d)
      (hy : y ∈ tsupport (σ : EC d → ℂ)) (a : BasisIndex d) :
      ‖fderiv ℝ (f z i j) y (stdOrthonormalBasis ℝ (EC d) a)‖ ≤ Q := by
    let H := fun x => (g.deform z.potential z.positive).matrix q x i j
    have hdy : DifferentiableAt ℝ H (coordinateEquiv d y) :=
      ((contDiffOn_pi.mp (contDiffOn_pi.mp ((g.deform z.potential z.positive).smooth q) i) j).contDiffAt
        ((A.chart q).open_target.mem_nhds (hKt (mem_image_of_mem _ hy)))).differentiableAt (by simp)
    have he : fderiv ℝ (f z i j) y = (fderiv ℝ H (coordinateEquiv d y)).comp
        (coordinateEquiv d).toContinuousLinearMap :=
      (hdy.hasFDerivAt.comp y (coordinateEquiv d).hasFDerivAt).fderiv
    rw [he,ContinuousLinearMap.comp_apply]
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply (mul_le_mul (hp z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation _
      (mem_image_of_mem _ hy) i j)
      ((coordinateEquiv d).toContinuousLinearMap.le_opNorm _)
      (norm_nonneg _) hP.le).trans_eq
    simp only [OrthonormalBasis.norm_eq_one,mul_one]
    rfl
  have hb (i j : Fin d) := σ.uniform_C1 (A.euclideanChart q).open_target
    (stdOrthonormalBasis ℝ (EC d)) (fun z => f z i j) (fun z => hs z i j)
    hM.le hQ (h0 i j) (h1 i j)
  choose B hB hb using hb
  refine ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hB i j,?_⟩
  intro z i j
  have hle : B i j ≤ ∑ i, ∑ j, B i j :=
    (Finset.single_le_sum (fun j _ => hB i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hB i j) (Finset.mem_univ i))
  exact ⟨fun y => ((hb i j z).1 y).trans hle,fun a y => ((hb i j z).2 a y).trans hle⟩

lemma cutMetric_uniform_initialJet [Nonempty (Fin d)] [Nonempty (BasisIndex d)]
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (q : Fin A.count) (σ : ChartCutoff (A.euclideanChart q).target) (π : Equiv.Perm (Fin d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : g.NormalizedPathSolution line,
      familyJetNorm (stdOrthonormalBasis ℝ (EC d)) (realComponents
        (initialJet (stdOrthonormalBasis ℝ (EC d))
          (fun i y => cutMetric (g.deform z.potential z.positive) q σ (π i) i y))) 0 ∞ ≤ B := by
  obtain ⟨B,hB,hb⟩ := cutMetric_uniform_C1 (g:=g) line hd q σ
  exact ⟨B,hB,fun z => initialJet_zero_bound _ _ hB (fun i => (hb z (π i) i).1)
    (fun i => (hb z (π i) i).2)⟩
end GlobalElliptic

end
end

end OAI
