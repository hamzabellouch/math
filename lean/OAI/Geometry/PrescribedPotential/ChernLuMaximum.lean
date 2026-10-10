import Mathlib
import OAI.Geometry.PrescribedPotential.ChernLuFrameInequality
import OAI.Geometry.PrescribedPotential.PotentialLinearCalculus

namespace OAI

/-! Chern Lu Maximum. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma pullMetric_potential_relation (B : V n →L[ℂ] V n)
    (M G : V n → Matrix (Fin n) (Fin n) ℂ) (f : V n → ℝ) (w : V n)
    (hf : ContDiffAt ℝ ∞ f (B w))
    (he : M (B w) = G (B w)+PotentialKaehler.potentialMatrix f (B w)) :
    pullMetric B M w = pullMetric B G w+PotentialKaehler.potentialMatrix (fun y => f (B y)) w := by
  rw [potentialMatrix_linear B hf]
  unfold pullMetric
  rw [he,mul_add,add_mul]

lemma trace_potential_in_frame (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    (M G : V n → Matrix (Fin n) (Fin n) ℂ) (f : V n → ℝ) (w : V n)
    (hf : ContDiffAt ℝ ∞ f (B w))
    (he : M (B w) = G (B w)+PotentialKaehler.potentialMatrix f (B w))
    (hM1 : pullMetric B M w = 1) :
    (PotentialKaehler.potentialMatrix (fun y => f (B y)) w).trace.re =
      (n:ℝ)-inverseTrace M G (B w) := by
  have hh := congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => H.trace.re)
    (pullMetric_potential_relation B M G f w hf he)
  rw [hM1,Matrix.trace_one,Matrix.trace_add,Complex.add_re] at hh
  have hs := inverseTrace_eq_frameGram B hB M G w hM1
  change inverseTrace M G (B w) = (pullMetric B G w).trace.re at hs
  simp only [Fintype.card_fin,Complex.natCast_re] at hh
  linarith

lemma scalar_trace_maximum {C S L D : ℝ} (hp : 0 < S)
    (hr : -C*S^2 ≤ S*L) (hm : L-(C+1)*(D-S) ≤ 0) : S ≤ (C+1)*D := by
  have he : S*(S-(C+1)*D) ≤ 0 := by nlinarith
  by_contra h
  have hmul := mul_pos hp (sub_pos.mpr (lt_of_not_ge h))
  linarith

lemma inverseTrace_at_localMax_bound [Nonempty (Fin n)]
    {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    (hG : ContDiffOn ℝ ∞ G U) (hGp : ∀ y ∈ U, (G y).PosDef)
    {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {z : V n} (hz : z ∈ U)
    (he : M z = G z+PotentialKaehler.potentialMatrix f z)
    (C : ℝ) (hbound : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      -C*(frameGram (G z) B)^2 ≤ frameResidual
        (PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z)
        (G z) (curvatureDiagonal G z) B)
    (hmax : IsLocalMax (fun y => Real.log (inverseTrace M G y)-(C+1)*f y) z) :
    inverseTrace M G z ≤ (C+1)*n := by
  obtain ⟨B,w,hB,hw,hM1⟩ := normalized_frame M z (hp z hz)
  have hwU : B w ∈ U := hw ▸ hz
  have hfs := hf.contDiffAt (hU.mem_nhds hz)
  have hSpos : 0 < inverseTrace M G z := inverseTrace_pos (hp z hz) (hGp z hz)
  have hSs := (inverseTrace_smooth hU hM hp hG).contDiffAt (hU.mem_nhds hz)
  have hlog := hSs.log (ne_of_gt hSpos)
  have hbℝ := (B.restrictScalars ℝ).contDiff.contDiffAt (x := w) (n := ∞)
  have hfc : ContDiffAt ℝ ∞ (fun y => f (B y)) w := by
    exact (hw ▸ hfs).comp w hbℝ
  have hlc : ContDiffAt ℝ ∞ (fun y => Real.log (inverseTrace M G (B y))) w := by
    exact (hw ▸ hlog).comp w hbℝ
  have hmaxc : IsLocalMax (fun y => Real.log (inverseTrace M G (B y))-(C+1)*f (B y)) w := by
    have ht : Tendsto B (𝓝 w) (𝓝 z) := hw ▸ B.continuous.continuousAt
    change ∀ᶠ y in 𝓝 w, Real.log (inverseTrace M G (B y))-(C+1)*f (B y) ≤
      Real.log (inverseTrace M G (B w))-(C+1)*f (B w)
    rw [hw]
    exact ht.eventually hmax
  have ht := EllipticKernel.trace_potentialMatrix_nonpos_at_localMax
    (hlc.sub (contDiffAt_const.mul hfc)) hmaxc (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosDef.one
  rw [inv_one,one_mul,potentialMatrix_trace_sub_smul hlc hfc] at ht
  have hphi := trace_potential_in_frame B hB M G f w (hw ▸ hfs) (hw ▸ he) hM1
  rw [hphi,hw] at ht
  have hi := inverseTrace_log_inequality_frame hU B hB hM hp hclosed hG hGp hwU hM1
  rw [hw] at hi
  have hb := hbound (frameMatrix B)
  have hgram := inverseTrace_eq_frameGram B hB M G w hM1
  rw [hw] at hgram
  rw [← hgram] at hb
  exact scalar_trace_maximum hSpos (hb.trans hi) ht
end KaehlerCalculus

end
end

end OAI
