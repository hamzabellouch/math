import Mathlib
import OAI.Geometry.PrescribedPotential.ChernLuIdentity
import OAI.Geometry.PrescribedPotential.TracePositivity

namespace OAI

/-! Inverse Trace Function. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

def inverseTrace (M G : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) : ℝ :=
  ((M z)⁻¹*G z).trace.re

lemma matrix_trace_smooth {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) : ContDiffAt ℝ ∞ (fun y => (M y).trace) z :=
  ContDiffAt.sum (fun k _ => entry_smooth hM k k)

lemma inverseTrace_smooth {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) (hG : ContDiffOn ℝ ∞ G U) :
    ContDiffOn ℝ ∞ (inverseTrace M G) U := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  apply Complex.reCLM.contDiff.contDiffAt.comp z
  exact matrix_trace_smooth (matrix_smooth_mul
    ((MatrixSmoothGeneral.inverse hM (fun y hy => ne_of_gt (hp y hy).det_pos)).contDiffAt (hU.mem_nhds hz))
    (hG.contDiffAt (hU.mem_nhds hz)))

lemma inverseTrace_real {M G : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : (M z).PosDef) (hG : (G z).IsHermitian) :
    (inverseTrace M G z : ℂ) = ((M z)⁻¹*G z).trace :=
  trace_mul_real hM.inv.isHermitian hG

lemma inverseTrace_pos [Nonempty (Fin n)] {M G : V n → Matrix (Fin n) (Fin n) ℂ}
    {z : V n} (hM : (M z).PosDef) (hG : (G z).PosDef) :
    0 < inverseTrace M G z := trace_mul_pos hM.inv hG

lemma second_wderiv_congr {f g : V n → ℂ} {z : V n} (he : f =ᶠ[𝓝 z] g)
    (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v f) z = wderiv b u (wderiv a v g) z := by
  exact wderiv_congr (he.eventually_nhds.mono (fun _ h => wderiv_congr h a v)) b u

lemma inverseTrace_dz_at_one {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) (hG : ContDiffOn ℝ ∞ G U)
    (hGh : ∀ y ∈ U, (G y).IsHermitian) {z : V n} (hz : z ∈ U) (hMz : M z = 1)
    (v : V n) : dz v (fun y => (inverseTrace M G y : ℂ)) z =
      (mderiv (-Complex.I) v G z-mderiv (-Complex.I) v M z*G z).trace := by
  have he : (fun y => (inverseTrace M G y : ℂ)) =ᶠ[𝓝 z]
      (fun y => ((M y)⁻¹*G y).trace) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact inverseTrace_real (hp y hy) (hGh y hy)
  have hi := (MatrixSmoothGeneral.inverse hM (fun y hy => ne_of_gt (hp y hy).det_pos)).contDiffAt (hU.mem_nhds hz)
  have hg := hG.contDiffAt (hU.mem_nhds hz)
  change wderiv (-Complex.I) v _ z = _
  rw [wderiv_congr he,mderiv_trace (matrix_smooth_mul hi hg),mderiv_mul hi hg,
    mderiv_inverse hU hM (fun y hy => ne_of_gt (hp y hy).det_pos) hz,hMz]
  simp only [inv_one,neg_mul,one_mul,mul_one]
  congr 1
  abel

lemma inverseTrace_second_at_one {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    (hG : ContDiffOn ℝ ∞ G U) (hGh : ∀ y ∈ U, (G y).IsHermitian)
    {z : V n} (hz : z ∈ U) (hMz : M z = 1) :
    (PotentialKaehler.potentialMatrix (inverseTrace M G) z).trace.re =
      -(PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z*G z).trace.re +
      ∑ k, (mderiv (-Complex.I) (e k) M z*(mderiv (-Complex.I) (e k) M z)ᴴ*G z -
        mderiv (-Complex.I) (e k) M z*(mderiv (-Complex.I) (e k) G z)ᴴ -
        (mderiv (-Complex.I) (e k) M z)ᴴ*mderiv (-Complex.I) (e k) G z +
        mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) G) z).trace.re := by
  have he : (fun y => (inverseTrace M G y : ℂ)) =ᶠ[𝓝 z]
      (fun y => ((M y)⁻¹*G y).trace) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact inverseTrace_real (hp y hy) (hGh y hy)
  have hs := (inverseTrace_smooth hU hM hp hG).contDiffAt (hU.mem_nhds hz)
  have htr : (PotentialKaehler.potentialMatrix (inverseTrace M G) z).trace =
      ∑ k, dzbar (e k) (dz (e k) (fun y => ((M y)⁻¹*G y).trace)) z := by
    apply Finset.sum_congr rfl
    intro k _
    change PotentialKaehler.potentialMatrix (inverseTrace M G) z k k = _
    rw [potentialMatrix_eq_dzbar_dz hs]
    exact second_wderiv_congr he _ _ _ _
  rw [htr,inverse_trace_ricci_identity_at_one hU hM hp hclosed hG hGh hz hMz]
  simp only [Complex.add_re,Complex.neg_re,Complex.re_sum]
end KaehlerCalculus

end
end

end OAI
