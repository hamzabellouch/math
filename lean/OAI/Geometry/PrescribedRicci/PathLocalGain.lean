import Mathlib
import OAI.Geometry.PrescribedRicci.LocalDeterminantGain
import OAI.Geometry.PrescribedRicci.MatrixCompactBounds
import OAI.Geometry.PrescribedRicci.PathLocalizedDensity
import OAI.Geometry.PrescribedRicci.PathLocalizedMetricBounds
import OAI.Geometry.PrescribedRicci.PathUniformAtlas
import OAI.Geometry.PrescribedRicci.UniformLocalGain

namespace OAI

/-! Path Local Gain. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff SchwartzMap Classical ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace SobolevChart
lemma UniformSobolev.cutoff_integer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
    (κ : 𝓢(E,ℂ)) (k : ℕ) {f : Z → 𝓢(E,ℂ)} (hf : UniformSobolev (k:ℝ) f) :
    UniformSobolev (k:ℝ) (fun z => SchwartzMap.smulLeftCLM ℂ κ (f z)) :=
  hf.of_coreBound (coreBound_product_integer κ k)
lemma UniformSobolev.cutoff_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
    (κ : 𝓢(E,ℂ)) {f : Z → 𝓢(E,ℂ)} (hf : UniformSobolev 0 f) :
    UniformSobolev 0 (fun z => SchwartzMap.smulLeftCLM ℂ κ (f z)) := by
  exact hf.of_coreBound (by simpa only [Nat.cast_zero] using coreBound_product_integer κ 0)
lemma UniformSobolev.cutoff_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
    (κ : 𝓢(E,ℂ)) {f : Z → 𝓢(E,ℂ)} (hf : UniformSobolev 2 f) :
    UniformSobolev 2 (fun z => SchwartzMap.smulLeftCLM ℂ κ (f z)) := by
  exact hf.of_coreBound (by simpa only [Nat.cast_ofNat] using coreBound_product_integer κ 2)
end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart MetricLocalization FrozenPoisson
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
  {g : KaehlerMetric A}
namespace GluingData
variable (D : GluingData g ι)

lemma cutoff_nested_one {U : Set (EC d)} (κ σ τ : ChartCutoff U)
    (hσ : ∀ y ∈ tsupport (κ : EC d → ℂ), (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1) :
    ∀ y ∈ tsupport (κ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1 := by
  intro y hy
  apply hτ
  apply subset_tsupport
  change σ y ≠ 0
  rw [(hσ y hy).eq_of_nhds]
  exact one_ne_zero

omit [ConnectedSpace X] in
lemma path_cutoff_identity (q : Fin A.count) (κ τ : ChartCutoff (A.euclideanChart q).target)
    (hτ : ∀ y ∈ tsupport (κ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (φ : SmoothRealFunction A) :
    localize A q (cutoffGlobal q κ) (cutoffGlobal_support q κ) (Smooth.ofReal φ) =
      SchwartzMap.smulLeftCLM ℂ κ.val
        (localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal φ)) := by
  ext y
  rw [localize_cutoff_product,ChartCutoff.product_apply,
    SchwartzMap.smulLeftCLM_apply_apply κ.val.hasTemperateGrowth,smul_eq_mul]
  by_cases hy : y ∈ tsupport (κ : EC d → ℂ)
  · rw [(localize_cutoff_germ q τ (Smooth.ofReal φ) (κ.support_sub hy) (hτ y hy)).eq_of_nhds]
  · simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

omit [ConnectedSpace X] in
lemma path_cutoff_bound (line : SemipositiveAnticanonicalMetric A) (q : Fin A.count)
    (τ : ChartCutoff (A.euclideanChart q).target) (k : ℕ)
    (hprev : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed (k:ℝ) (Smooth.ofReal z.potential)‖ ≤ C) :
    UniformSobolev (k:ℝ) (fun z : g.NormalizedPathSolution line =>
      localize A q (cutoffGlobal q τ) (cutoffGlobal_support q τ) (Smooth.ofReal z.potential)) := by
  obtain ⟨C,hC,hb⟩ := hprev
  obtain ⟨B,hB,hlocal⟩ := D.localization_integer_bound q
    (cutoffGlobal q τ) (cutoffGlobal_support q τ) k
  exact ⟨B*C,mul_nonneg hB hC,fun z => (hlocal (Smooth.ofReal z.potential)).trans
    (mul_le_mul_of_nonneg_left (hb z) hB)⟩

include D in
lemma path_local_word_differential (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (p : UniformPathPatch g line)
    (κ σ τ : ChartCutoff (A.euclideanChart p.index).target)
    (hκp : tsupport (κ : EC d → ℂ) ⊆ p.domain)
    (hκr : ∀ y, (κ y).im = 0) (hτr : ∀ y, (τ y).im = 0)
    (hσ : ∀ y ∈ tsupport (κ : EC d → ℂ), (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (ws : List (BasisIndex d)) (hw0 : ws ≠ [])
    (hF : UniformSobolev ((ws.length:ℝ)+1) (fun z : g.NormalizedPathSolution line =>
      localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential))) :
    UniformSobolev 0 (fun z : g.NormalizedPathSolution line =>
      schwartzDifferential (extendedCoefficient
        ((g.deform z.potential z.positive).matrix p.index (coordinateEquiv d p.center))
        (coefficientBCF (p.coefficient z)))
        (SchwartzMap.smulLeftCLM ℂ κ.val (schwartzWord (ws.map (stdOrthonormalBasis ℝ (EC d)))
          (localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential))))) := by
  let : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (BasisIndex d) := ⟨⟨0,Module.finrank_pos⟩⟩
  let f (z : g.NormalizedPathSolution line) :=
    localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential)
  let F (z : g.NormalizedPathSolution line) := SchwartzMap.smulLeftCLM ℂ κ.val
    (schwartzWord (ws.map (stdOrthonormalBasis ℝ (EC d))) (f z))
  have hτκ := cutoff_nested_one κ σ τ hσ hτ
  let H (z : g.NormalizedPathSolution line) := cutMetric (g.deform z.potential z.positive) p.index σ
  let G (_ : g.NormalizedPathSolution line) := cutMetric g p.index σ
  let c (z : g.NormalizedPathSolution line) :=
    extendedCoefficient ((g.deform z.potential z.positive).matrix p.index (coordinateEquiv d p.center))
      (coefficientBCF (p.coefficient z))
  have hc (z : g.NormalizedPathSolution line) (i j) : (c z i j : EC d → ℂ).HasTemperateGrowth :=
    extendedCoefficient_temperate _ _ (fun i j => ((p.coefficient z) i j).hasTemperateGrowth) i j
  have heH (z : g.NormalizedPathSolution line) (y : EC d) (hy : y ∈ tsupport (κ : EC d → ℂ)) :
      (show Matrix (Fin d) (Fin d) ℂ from fun i j => H z i j y) =
      (g.deform z.potential z.positive).matrix p.index (coordinateEquiv d y) := by
    ext i j
    change σ y*_ = _
    rw [(hσ y hy).eq_of_nhds,one_mul]
  let K := coordinateEquiv d '' tsupport (κ : EC d → ℂ)
  have hKt : K ⊆ (A.chart p.index).target := by
    rintro _ ⟨y,hy,rfl⟩
    simpa using κ.support_sub hy
  obtain ⟨B,hB,hb⟩ := g.volumePath_metric_bounds_on_compact line hd p.index
    (κ.compact.image (coordinateEquiv d).continuous) hKt
  obtain ⟨J,hJ,hj⟩ := MongeAmpere.compact_matrix_bound
    (show Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => ‖M.det‖) from continuous_id.matrix_det.norm) B
  change UniformSobolev 0 (fun z => schwartzDifferential (c z) (F z))
  apply uniform_determinant_word_differential (stdOrthonormalBasis ℝ (EC d)) ws hw0
    κ.val f (cutPathDensity g line p.index σ) G H c hc
  · intro z y hy i j
    rw [heH z y hy]
    exact p.equals z y (hκp hy) i j
  · intro z y
    rw [SchwartzMap.smulLeftCLM_apply_apply κ.val.hasTemperateGrowth]
    change (κ y*schwartzWord _ (f z) y).im = 0
    rw [Complex.mul_im,hκr,schwartzWord_real _ _ (localize_cutoff_real p.index τ hτr z.potential)]
    ring
  · intro z y hy i j
    exact cutMetric_deform_germ g p.index σ τ z.potential z.positive
      (κ.support_sub hy) (hσ y hy) (hτκ y hy) i j
  · intro z y hy
    exact cutPathDensity_germ line p.index σ z (κ.support_sub hy) (hσ y hy)
  · intro z y hy
    rw [heH z y hy]
    exact isUnit_iff_ne_zero.mpr ((g.deform z.potential z.positive).positive p.index _
      (by simpa using κ.support_sub hy)).det_pos.ne'
  · exact hB.le
  · exact hJ.le
  · intro z y hy i j
    rw [heH z y hy]
    exact (norm_entry_le_entrywise_sup_norm _).trans
      (hb z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation _
        (mem_image_of_mem _ hy)).2
  · intro z y hy
    rw [heH z y hy,← Ring.inverse_eq_inv,← Matrix.det_nonsing_inv]
    exact hj _ (hb z.potential z.positive z.mean_zero z.time z.constant z.time_mem z.equation _
      (mem_image_of_mem _ hy)).2
  · exact hF
  · exact cutPathDensity_uniform D line p.index σ ws.length
  · intro i j
    exact UniformSobolev.const _ _
  · intro z i j
    exact σ.product_compact _
  · exact cutMetric_uniform_initialJet line hd p.index σ
  · intro i j
    have hn : 1 ≤ ws.length := List.length_pos_iff.mpr hw0
    have hncast : ((ws.length-1:ℕ):ℝ) = (ws.length:ℝ)-1 := by rw [Nat.cast_sub hn]; norm_num
    have hlow : UniformSobolev (((ws.length-1:ℕ):ℝ)+2) f := hF.mono (by rw [hncast]; linarith)
    simpa only [hncast] using cutMetric_uniform_sobolev line p.index σ τ hτ (ws.length-1) hlow i j

include D in
lemma path_local_word_H2 (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (p : UniformPathPatch g line)
    (κ σ τ : ChartCutoff (A.euclideanChart p.index).target)
    (hκp : tsupport (κ : EC d → ℂ) ⊆ p.domain)
    (hκr : ∀ y, (κ y).im = 0) (hτr : ∀ y, (τ y).im = 0)
    (hσ : ∀ y ∈ tsupport (κ : EC d → ℂ), (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (ws : List (BasisIndex d))
    (hF : UniformSobolev ((ws.length:ℝ)+1) (fun z : g.NormalizedPathSolution line =>
      localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential)))
    (hF2 : UniformSobolev 2 (fun z : g.NormalizedPathSolution line =>
      localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential))) :
    UniformSobolev 2 (fun z : g.NormalizedPathSolution line =>
      SchwartzMap.smulLeftCLM ℂ κ.val (schwartzWord (ws.map (stdOrthonormalBasis ℝ (EC d)))
        (localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential)))) := by
  have hword := hF.word (t:=0) (ws.map (stdOrthonormalBasis ℝ (EC d)))
    (by simp only [List.length_map]; linarith)
  have hfword := hword.cutoff_zero κ.val
  by_cases hw0 : ws = []
  · subst ws
    simpa only [List.map_nil,schwartzWord,ContinuousLinearMap.id_apply] using
      hF2.cutoff_two κ.val
  have hD := D.path_local_word_differential line hd p κ σ τ hκp hκr hτr hσ hτ ws hw0 hF
  exact uniform_schwartz_H2_of_differential (Z:=g.NormalizedPathSolution line) (n:=d) p.bound_pos.le
    (fun z => (g.deform z.potential z.positive).matrix p.index (coordinateEquiv d p.center))
    (fun z => (g.deform z.potential z.positive).positive p.index _ (by simpa using p.center_target))
    p.matrix_bound (fun z => coefficientBCF (p.coefficient z))
    (fun z i j => (p.coefficient z i j).hasTemperateGrowth) p.small _ hfword hD

lemma path_local_gain (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d)
    (p : UniformPathPatch g line)
    (κ σ τ : ChartCutoff (A.euclideanChart p.index).target)
    (hκp : tsupport (κ : EC d → ℂ) ⊆ p.domain)
    (hκr : ∀ y, (κ y).im = 0) (hτr : ∀ y, (τ y).im = 0)
    (hσ : ∀ y ∈ tsupport (κ : EC d → ℂ), (σ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (hτ : ∀ y ∈ tsupport (σ : EC d → ℂ), (τ : EC d → ℂ) =ᶠ[𝓝 y] fun _ => 1)
    (k : ℕ) (hk : 1 ≤ k)
    (hprev : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : g.NormalizedPathSolution line,
      ‖D.localizers.embed ((k:ℝ)+1) (Smooth.ofReal z.potential)‖ ≤ C) :
    UniformSobolev ((k:ℝ)+2) (fun z : g.NormalizedPathSolution line =>
      localize A p.index (cutoffGlobal p.index κ) (cutoffGlobal_support p.index κ)
        (Smooth.ofReal z.potential)) := by
  let f (z : g.NormalizedPathSolution line) :=
    localize A p.index (cutoffGlobal p.index τ) (cutoffGlobal_support p.index τ) (Smooth.ofReal z.potential)
  have hF : UniformSobolev ((k:ℝ)+1) f := by
    have he : (k:ℝ)+1 = ((k+1:ℕ):ℝ) := by simp
    rw [he] at hprev ⊢
    exact D.path_cutoff_bound line p.index τ (k+1) hprev
  have heF (z : g.NormalizedPathSolution line) := path_cutoff_identity p.index κ τ
    (cutoff_nested_one κ σ τ hσ hτ) z.potential
  simp_rw [heF]
  apply uniform_cutoff_word_gain κ.val k hF
  intro ws hw
  have hlen : (ws.length:ℝ) ≤ k := by exact_mod_cast hw
  exact D.path_local_word_H2 line hd p κ σ τ hκp hκr hτr hσ hτ ws
    (hF.mono (by linarith)) (hF.mono (by exact_mod_cast (show 2 ≤ k+1 by omega)))
end GluingData
end GlobalElliptic

end
end

end OAI
