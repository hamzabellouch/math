import Mathlib
import OAI.Geometry.PrescribedRicci.PathLocalizedDensity
import OAI.Geometry.PrescribedRicci.SmoothPathLimit

namespace OAI

/-! Positive Path Limit. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
  {g : KaehlerMetric A}

omit [ConnectedSpace X] in
lemma path_determinant_source (line : SemipositiveAnticanonicalMetric A)
    (z : g.NormalizedPathSolution line) (q : Fin A.count) {x : X}
    (hx : x ∈ (A.chart q).source) :
    ((g.deform z.potential z.positive).matrix q (A.chart q x)).det =
      (g.matrix q (A.chart q x)).det *
        (Real.exp (z.time*(prescribedForcing g line).value x+z.constant):ℂ) := by
  have hxe : x ∈ (A.euclideanChart q).source := by simpa using hx
  have h := path_determinant_equation line z q ((A.euclideanChart q).mapsTo hxe)
  have he : coordinateEquiv d (A.euclideanChart q x) = A.chart q x :=
    (coordinateEquiv d).apply_symm_apply _
  rw [he,(A.euclideanChart q).left_inv hxe] at h
  exact h

namespace GluingData
variable (D : GluingData g ι)

omit [ConnectedSpace X] in
lemma path_limit_matrix (line : SemipositiveAnticanonicalMetric A)
    (z : ℕ → g.NormalizedPathSolution line) (φ : SmoothRealFunction A)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (z n).potential))
      atTop (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))))
    (p : ι) {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    Tendsto (fun n => (g.deform (z n).potential (z n).positive).matrix
      (D.patch p).index (A.chart (D.patch p).index x)) atTop
      (𝓝 (g.matrix (D.patch p).index (A.chart (D.patch p).index x)+
        φ.hessian (D.patch p).index (A.chart (D.patch p).index x))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add (D.hessian_of_sobolev _ φ hlim p hx i j)

omit [ConnectedSpace X] in
lemma path_limit_determinant (line : SemipositiveAnticanonicalMetric A)
    (z : ℕ → g.NormalizedPathSolution line) (φ : SmoothRealFunction A) (t b : ℝ)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (z n).potential))
      atTop (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))))
    (ht : Tendsto (fun n => (z n).time) atTop (𝓝 t))
    (hb : Tendsto (fun n => (z n).constant) atTop (𝓝 b))
    (p : ι) {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    (g.matrix (D.patch p).index (A.chart (D.patch p).index x)+
      φ.hessian (D.patch p).index (A.chart (D.patch p).index x)).det =
      (g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det *
        (Real.exp (t*(prescribedForcing g line).value x+b):ℂ) := by
  have hs : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hx
  have hdet := (show Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => M.det) from
    continuous_id.matrix_det).continuousAt.tendsto.comp (D.path_limit_matrix line z φ hlim p hx)
  have hex := Real.continuous_exp.continuousAt.tendsto.comp
    ((ht.mul_const ((prescribedForcing g line).value x)).add hb)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hex
  have hr := hc.const_mul ((g.matrix (D.patch p).index (A.chart (D.patch p).index x)).det)
  have he (n : ℕ) := path_determinant_source line (z n) (D.patch p).index hs
  simp only [Function.comp_def] at hdet hr
  simp_rw [he] at hdet
  exact tendsto_nhds_unique hdet hr

omit [ConnectedSpace X] in
lemma path_limit_positive (line : SemipositiveAnticanonicalMetric A)
    (z : ℕ → g.NormalizedPathSolution line) (φ : SmoothRealFunction A) (t b : ℝ)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (z n).potential))
      atTop (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))))
    (ht : Tendsto (fun n => (z n).time) atTop (𝓝 t))
    (hb : Tendsto (fun n => (z n).constant) atTop (𝓝 b)) : g.PositivePotential φ := by
  have hpos (p : ι) (x : X) (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
      (g.matrix (D.patch p).index (A.chart (D.patch p).index x)+
        φ.hessian (D.patch p).index (A.chart (D.patch p).index x)).PosDef := by
    have hs : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hx
    have hz := (A.chart (D.patch p).index).mapsTo hs
    apply (Matrix.PosSemidef.posDef_iff_det_ne_zero ?_).mpr
    · rw [D.path_limit_determinant line z φ t b hlim ht hb p hx]
      exact mul_ne_zero (g.positive _ _ hz).det_pos.ne' (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        ((g.positive _ _ hz).isHermitian.add (φ.hessian_hermitian _ hz))
      intro v
      have hc : Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => star v ⬝ᵥ (M *ᵥ v)) := by fun_prop
      have h := hc.continuousAt.tendsto.comp (D.path_limit_matrix line z φ hlim p hx)
      exact isClosed_Ici.mem_of_tendsto h (Eventually.of_forall (fun n =>
        ((z n).positive _ _ hz).posSemidef.dotProduct_mulVec_nonneg v))
  intro i y hy
  let x := (A.chart i).symm y
  have hi : x ∈ (A.chart i).source := (A.chart i).mapsTo_symm hy
  have hiy : A.chart i x = y := (A.chart i).right_inv hy
  obtain ⟨p,hp⟩ := D.exists_weight_supportViaEnergy x
  have hj : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hp
  rw [← hiy,g.compatibility i (D.patch p).index x hi hj,
    φ.hessian_compatibility i (D.patch p).index hi hj,← add_mul,← mul_add]
  exact (hpos p x hp).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_det_ne_zero
    (g.transition_det_isUnit i (D.patch p).index hi hj).ne_zero)

omit [ConnectedSpace X] in
lemma path_limit_solves (line : SemipositiveAnticanonicalMetric A)
    (z : ℕ → g.NormalizedPathSolution line) (φ : SmoothRealFunction A) (t b : ℝ)
    (hlim : ∀ k : ℕ, Tendsto (fun n => D.localizers.embed (k:ℝ) (Smooth.ofReal (z n).potential))
      atTop (𝓝 (D.localizers.embed (k:ℝ) (Smooth.ofReal φ))))
    (ht : Tendsto (fun n => (z n).time) atTop (𝓝 t))
    (hb : Tendsto (fun n => (z n).constant) atTop (𝓝 b)) : SolvesVolumePath g line t φ b := by
  let hp := D.path_limit_positive line z φ t b hlim ht hb
  refine ⟨hp,fun x => ?_⟩
  obtain ⟨p,hpX⟩ := D.exists_weight_supportViaEnergy x
  have hs : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hpX
  let q := (D.patch p).index
  have hz := (A.chart q).mapsTo hs
  have he := congrArg Complex.re (D.path_limit_determinant line z φ t b hlim ht hb p hpX)
  have hv : (g.deform φ hp).volumeCoefficient q (A.chart q x) =
      g.volumeCoefficient q (A.chart q x)*Real.exp (t*(prescribedForcing g line).value x+b) := by
    simpa only [KaehlerMetric.volumeCoefficient,KaehlerMetric.deform,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using he
  change g.logRatioValue (g.deform φ hp) x = _
  rw [g.logRatioValue_local _ q hs,hv,
    Real.log_mul (g.volumeCoefficient_pos q hz).ne' (Real.exp_ne_zero _),Real.log_exp]
  ring
end GluingData
end GlobalElliptic

end
end

end OAI
