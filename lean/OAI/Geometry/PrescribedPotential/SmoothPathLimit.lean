import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixLimit
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.VolumePath
import OAI.Geometry.PrescribedPotential.SmoothPathOpenness
import OAI.Geometry.PrescribedPotential.PositiveOpenness
import OAI.Geometry.PrescribedPotential.CompletedVolume
import OAI.Geometry.PrescribedPotential.RealSmoothCompactness

namespace OAI

/-! Smooth Path Limit. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma solvesVolumePath_density (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (he : SolvesVolumePath g h t φ b) (x : X) :
    (g.potentialDensity φ).value x = Real.exp (t * (prescribedForcing g h).value x + b) := by
  have hh := congrArg Real.exp (he.2 x)
  rw [g.logRatio_deform_eq_logDensity φ he.1 x,
    Real.exp_log (g.potentialDensity_pos φ he.1 x)] at hh
  exact hh

lemma solvesVolumePath_of_density (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hp : g.PositivePotential φ)
    (he : ∀ x, (g.potentialDensity φ).value x =
      Real.exp (t * (prescribedForcing g h).value x + b)) : SolvesVolumePath g h t φ b := by
  refine ⟨hp,fun x => ?_⟩
  rw [g.logRatio_deform_eq_logDensity φ hp x,he x,Real.log_exp]

end Anticanonical.SourceSmooth
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance smoothLimitNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance smoothLimitNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace

lemma realMatrix_tendsto (k : ℕ) (f : ℕ → RealSmooth A) (fLim : RealSmooth A)
    (hf : Tendsto (fun n => D.localizers.embed ((k : ℝ)+2) (f n).val) atTop
      (𝓝 (D.localizers.embed ((k : ℝ)+2) fLim.val))) (p : ι) (x : X) :
    Tendsto (fun n => D.weakMatrix k (D.localizers.realEmbed ((k : ℝ)+2) (f n)) p x)
      atTop (𝓝 (D.weakMatrix k (D.localizers.realEmbed ((k : ℝ)+2) fLim) p x)) := by
  have hr : Tendsto (fun n => D.localizers.realEmbed ((k : ℝ)+2) (f n)) atTop
      (𝓝 (D.localizers.realEmbed ((k : ℝ)+2) fLim)) := tendsto_subtype_rng.mpr hf
  have hc : Continuous (fun u : D.localizers.RealSobolev ((k : ℝ)+2) => D.weakMatrix k u p x) :=
    (D.weakMatrix_continuous k p).comp (continuous_id.prodMk continuous_const)
  exact hc.tendsto _ |>.comp hr

lemma completedVolume_realSmooth_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (f : RealSmooth A) :
    D.completedVolume k hk (D.localizers.embed ((k : ℝ)+2) f.val) =
      D.localizers.embed (k : ℝ) (Smooth.ofReal (g.potentialDensity f.source)) := by
  rw [← f.ofReal_source,D.completedVolume_embed]

lemma potentialDensity_tendsto (f : ℕ → RealSmooth A) (fLim : RealSmooth A)
    (hf : ∀ s : ℝ, Tendsto (fun n => D.localizers.embed s (f n).val) atTop
      (𝓝 (D.localizers.embed s fLim.val))) (x : X) :
    Tendsto (fun n => (g.potentialDensity (f n).source).value x) atTop
      (𝓝 ((g.potentialDensity fLim.source).value x)) := by
  let k := Module.finrank ℝ (EC d)+1
  have hk : Module.finrank ℝ (EC d) < k := Nat.lt_succ_self _
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hkr : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith only [hkr,Nat.cast_nonneg (α := ℝ) k]
  have hc := (D.completedVolume_contDiff k hk).continuous.tendsto
    (D.localizers.embed ((k : ℝ)+2) fLim.val) |>.comp (hf ((k : ℝ)+2))
  simp only [Function.comp_def,D.completedVolume_realSmooth_embed k hk] at hc
  have hv := D.localizers.smooth_value_tendsto (k : ℝ) hs
    (fun n => Smooth.ofReal (g.potentialDensity (f n).source))
    (Smooth.ofReal (g.potentialDensity fLim.source)) hc x
  have hr := (Complex.continuous_re.tendsto
    ((Smooth.ofReal (g.potentialDensity fLim.source)) x)).comp hv
  simpa only [Function.comp_def,Smooth.ofReal_apply,Complex.ofReal_re] using hr

lemma positivePotential_of_smooth_limit (f : ℕ → RealSmooth A) (fLim : RealSmooth A)
    (hf : ∀ s : ℝ, Tendsto (fun n => D.localizers.embed s (f n).val) atTop
      (𝓝 (D.localizers.embed s fLim.val)))
    (hp : ∀ n, g.PositivePotential (f n).source)
    (hd : ∀ x, 0 < (g.potentialDensity fLim.source).value x) : g.PositivePotential fLim.source := by
  let k := Module.finrank ℝ (EC d)+1
  have hk : Module.finrank ℝ (EC d) < k := Nat.lt_succ_self _
  apply (D.weakPositive_embed_iff k hk fLim).mp
  intro p x hx
  have hi : x ∈ (A.chart (D.patch p).index).source := by simpa using D.patch_source p hx
  have hdet : (D.weakMatrix k (D.localizers.realEmbed ((k : ℝ)+2) fLim) p x).det ≠ 0 := by
    rw [D.weakMatrix_embed k hk fLim p hx]
    intro he
    have hh := hd x
    rw [g.potentialDensity_quotient fLim.source (D.patch p).index hi,he,
      Complex.zero_re,zero_div] at hh
    exact lt_irrefl 0 hh
  exact CompactMatrixPositivity.posDef_of_tendsto_det_ne_zero
    (D.weakMatrix_hermitian k hk _ p hx)
    (fun n => (D.weakPositive_embed_iff k hk (f n)).mpr (hp n) p x hx)
    (D.realMatrix_tendsto k f fLim (hf ((k : ℝ)+2)) p x) hdet

 

theorem smooth_path_limit_solution (h : SemipositiveAnticanonicalMetric A)
    (t b : ℕ → ℝ) (tLim bLim : ℝ) (ht : Tendsto t atTop (𝓝 tLim))
    (hb : Tendsto b atTop (𝓝 bLim)) (f : ℕ → RealSmooth A) (fLim : RealSmooth A)
    (hf : ∀ s : ℝ, Tendsto (fun n => D.localizers.embed s (f n).val) atTop
      (𝓝 (D.localizers.embed s fLim.val)))
    (hsol : ∀ n, SolvesVolumePath g h (t n) (f n).source (b n)) :
    SolvesVolumePath g h tLim fLim.source bLim := by
  have he (x : X) : (g.potentialDensity fLim.source).value x =
      Real.exp (tLim * (prescribedForcing g h).value x + bLim) := by
    have hl := D.potentialDensity_tendsto f fLim hf x
    have hn : (fun n => (g.potentialDensity (f n).source).value x) =
        (fun n => Real.exp (t n * (prescribedForcing g h).value x + b n)) :=
      funext (fun n => solvesVolumePath_density g h (hsol n) x)
    rw [hn] at hl
    exact tendsto_nhds_unique hl (Real.continuous_exp.tendsto _ |>.comp
      ((ht.mul_const ((prescribedForcing g h).value x)).add hb))
  apply solvesVolumePath_of_density g h _ he
  exact D.positivePotential_of_smooth_limit f fLim hf (fun n => (hsol n).1)
    (fun x => (he x).symm ▸ Real.exp_pos _)

end GluingData
end GlobalElliptic

end
end

end OAI
