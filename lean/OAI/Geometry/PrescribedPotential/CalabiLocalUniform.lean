import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCutoffFrames
import OAI.Geometry.PrescribedPotential.CalabiCutoffPoint
import OAI.Geometry.PrescribedPotential.CalabiFrameScalars
import OAI.Geometry.PrescribedPotential.CalabiPointInequalities
import OAI.Geometry.PrescribedPotential.CalabiRicciFrames
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization

namespace OAI

/-! Calabi Local Uniform. -/

section

 

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma calabi_cutoff_max_uniform {Y : Type*} [TopologicalSpace Y]
    {P : Set Y} {L : Set (V n)} (G : V n → Matrix (Fin n) (Fin n) ℂ)
    (H : Y × V n → Matrix (Fin n) (Fin n) ℂ) (J : Y × V n → ConnectionTensor n)
    (χ : V n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {R K B C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hframe : ∀ z ∈ L, ∀ M C D : Matrix (Fin n) (Fin n) ℂ,
      ((R:ℂ) • M-G z).PosSemidef → ((K:ℂ) • G z-M).PosSemidef →
      C*D = 1 → Cᴴ*M*C = 1 → ‖C‖ ≤ B ∧ ‖D‖ ≤ B)
    (hcut : ∀ (b : V n →L[ℂ] V n) w, b w ∈ L → ‖frameMatrix b‖ ≤ B →
      -C ≤ (PotentialKaehler.potentialMatrix (fun y => (χ (b y))^2) w).trace.re ∧
      holGradientSquare (fun y => (χ (b y))^2) w ≤ C*(χ (b w))^2)
    (hric : ∀ x ∈ P ×ˢ L, ∀ p ∈ boundedFramePairs (n := n) B, ∀ T : ConnectionTensor n,
      -C*(1+tensorSquare T) ≤ calabiResidual (p.1ᴴ*H x*p.1) (frameRicciJet (J x) p.1) T ∧
      -C ≤ (p.2ᴴ*(p.1ᴴ*H x*p.1)*p.2).trace.re ∧
      δ*tensorSquare T ≤ rescueSquare p.2 T)
    (M : LocalKaehlerField n) {t : Y} (ht : t ∈ P) {z : V n} (hz : z ∈ L)
    (hzM : z ∈ M.domain)
    (hell : ((R:ℂ) • M.matrix z-G z).PosSemidef ∧ ((K:ℂ) • G z-M.matrix z).PosSemidef)
    (hH : M.ricciHessian z = H (t,z))
    (hJ : (fun i => mderiv (-Complex.I) (e i) M.ricciHessian z) = J (t,z))
    (hχ0 : 0 ≤ χ z) (hχ1 : χ z ≤ 1)
    (hmax : IsLocalMax (fun y => (χ y)^2*M.calabiNorm y+((6*C+1)/δ)*(M.matrix y).trace.re) z) :
    M.calabiNorm z ≤ C*(1+(6*C+1)/δ) := by
  obtain ⟨b,w,hb,hw,hnorm⟩ := normalized_frame M.matrix z (M.positive z hzM)
  let D := (frameMatrix b)⁻¹
  have hCD : frameMatrix b*D = 1 := Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hb)
  have hDC : D*frameMatrix b = 1 := Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hb)
  have hnorm' : (frameMatrix b)ᴴ*M.matrix z*frameMatrix b = 1 := by
    simpa only [pullMetric,hw] using hnorm
  obtain ⟨hbc,hdc⟩ := hframe z hz (M.matrix z) (frameMatrix b) D hell.1 hell.2 hCD hnorm'
  have hp : (frameMatrix b,D) ∈ boundedFramePairs B := ⟨hbc,hdc,hCD,hDC⟩
  have hwM : b w ∈ M.domain := hw ▸ hzM
  have hwL : b w ∈ L := hw ▸ hz
  have hS := M.pull_calabiNorm b hb hwM
  have hS' : tensorSquare (fun i => (M.pull b hb).connection i w) = M.calabiNorm z := by
    rw [← (M.pull b hb).calabiNorm_at_one hnorm,hS,hw]
  obtain ⟨hr1,hr2,hr3⟩ := hric (t,z) ⟨ht,hz⟩ (frameMatrix b,D) hp (fun i => (M.pull b hb).connection i w)
  have hh : (M.pull b hb).ricciHessian w = (frameMatrix b)ᴴ*H (t,z)*frameMatrix b := by
    rw [M.pull_ricciHessian b hb hwM]
    simp only [pullMetric,hw,hH]
  have hj : (fun i => mderiv (-Complex.I) (e i) (M.pull b hb).ricciHessian w) = frameRicciJet (J (t,z)) (frameMatrix b) := by
    rw [M.pull_ricciHessian_jet b hb hwM,hw,hJ]
  obtain ⟨hc1,hc2⟩ := hcut b w hwL hbc
  have hχs : ContDiffAt ℝ ∞ (fun y => (χ (b y))^2) w :=
    (hχ.contDiffAt.comp w (b.restrictScalars ℝ).contDiff.contDiffAt).pow 2
  have hχb1 : (χ (b w))^2 ≤ 1 := by rw [hw]; nlinarith
  have hnormM : (M.pull b hb).matrix w = 1 := hnorm
  have hhmax := M.pull_cutoff_max b hb hzM hw D hCD χ ((6*C+1)/δ) hmax
  have hbound := (M.pull b hb).calabi_cutoff_max_at_one hwM hnormM D hχs hC hδ
    (sq_nonneg _) hχb1 hc1 hc2
    (by rw [hh,hj,(M.pull b hb).calabiNorm_at_one hnormM]; exact hr1)
    (by rw [hh]; exact hr2)
    (by rw [(M.pull b hb).calabiNorm_at_one hnormM]; exact hr3) hhmax
  rwa [hS,hw] at hbound

 

theorem calabi_interior_uniform {Y : Type*} [TopologicalSpace Y]
    {P : Set Y} (hP : IsCompact P) {L : Set (V n)} (hL : IsCompact L)
    (G : V n → Matrix (Fin n) (Fin n) ℂ)
    (hG : ContinuousOn G L) (hGp : ∀ z ∈ L, (G z).PosDef)
    (H : Y × V n → Matrix (Fin n) (Fin n) ℂ) (J : Y × V n → ConnectionTensor n)
    (hH : ContinuousOn H (P ×ˢ L)) (hJ : ContinuousOn J (P ×ˢ L))
    (χ : V n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ z ∈ L, 0 ≤ χ z) (hχ1 : ∀ z ∈ L, χ z ≤ 1)
    (hχint : ∀ z ∈ L, χ z ≠ 0 → z ∈ interior L)
    {R K : ℝ} (hR : 0 ≤ R) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : LocalKaehlerField n) (t : Y),
      t ∈ P → L ⊆ M.domain →
      (∀ z ∈ L, ((R:ℂ) • M.matrix z-G z).PosSemidef ∧ ((K:ℂ) • G z-M.matrix z).PosSemidef) →
      (∀ z ∈ L, M.ricciHessian z = H (t,z)) →
      (∀ z ∈ L, (fun i => mderiv (-Complex.I) (e i) M.ricciHessian z) = J (t,z)) →
      ∀ z ∈ L, χ z = 1 → M.calabiNorm z ≤ C := by
  obtain ⟨B,hB,hframe⟩ := compact_normalizing_frames hL G hG hGp hR hK
  obtain ⟨C1,δ,hC1,hδ,hric⟩ := calabi_frame_uniform (hP.prod hL) H J hH hJ B
  obtain ⟨C2,hC2,hcut⟩ := cutoff_frame_bounds hL χ hχ B
  obtain ⟨Tb,hTb⟩ := hL.exists_bound_of_continuousOn (continuousOn_trace_re hG)
  let C := max C1 C2
  let T := K*max Tb 0
  let a := (6*C+1)/δ
  have hC : 0 ≤ C := hC1.trans (le_max_left _ _)
  have hT : 0 ≤ T := mul_nonneg hK (le_max_right _ _)
  have ha : 0 ≤ a := div_nonneg (by positivity) hδ.le
  refine ⟨C*(1+a)+a*T,by positivity,?_⟩
  intro M t ht hdom hell hRic hJet z hz hχz
  have htr (y) (hy : y ∈ L) : (M.matrix y).trace.re ≤ T := by
    exact (metric_trace_le (hell y hy).2).trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans ((hTb y hy).trans (le_max_left _ _))) hK)
  let F : V n → ℝ := fun y => (χ y)^2*M.calabiNorm y+a*(M.matrix y).trace.re
  have hFc : ContinuousOn F L :=
    ((hχ.continuous.continuousOn.pow 2).mul (M.calabiNorm_smooth.continuousOn.mono hdom)).add
      (continuousOn_const.mul (continuousOn_trace_re (M.smooth.continuousOn.mono hdom)))
  obtain ⟨y,hy,hmax⟩ := hL.exists_isMaxOn ⟨z,hz⟩ hFc
  have hFz : M.calabiNorm z ≤ F z := by
    dsimp only [F]
    rw [hχz,one_pow,one_mul]
    have ht0 := (Complex.nonneg_iff.mp (M.positive z (hdom hz)).posSemidef.trace_nonneg).1
    exact le_add_of_nonneg_right (mul_nonneg ha ht0)
  have hFzy := hmax hz
  have hFbound : F y ≤ C*(1+a)+a*T := by
    by_cases hzero : χ y = 0
    · dsimp only [F]
      rw [hzero,zero_pow (by decide),zero_mul,zero_add]
      exact (mul_le_mul_of_nonneg_left (htr y hy) ha).trans (le_add_of_nonneg_left (mul_nonneg hC (by positivity)))
    have hlocal : IsLocalMax F y := by
      filter_upwards [mem_interior_iff_mem_nhds.mp (hχint y hy hzero)] with v hv
      exact hmax hv
    have hcut' (b : V n →L[ℂ] V n) w (hw : b w ∈ L) (hb : ‖frameMatrix b‖ ≤ B) := hcut b w hw hb
    have hs : M.calabiNorm y ≤ C*(1+a) := by
      apply calabi_cutoff_max_uniform G H J χ hχ hC hδ hframe
        (fun b w hw hb => ⟨(neg_le_neg (le_max_right C1 C2)).trans (hcut' b w hw hb).1,
          (hcut' b w hw hb).2.trans (mul_le_mul_of_nonneg_right (le_max_right C1 C2) (sq_nonneg _))⟩)
        (fun x hx p hp U => ?_) M ht hy (hdom hy) (hell y hy) (hRic y hy) (hJet y hy)
        (hχ0 y hy) (hχ1 y hy) hlocal
      obtain ⟨h1,h2,h3⟩ := hric x hx p hp U
      refine ⟨?_,(neg_le_neg (le_max_left C1 C2)).trans h2,h3⟩
      have he : -C*(1+tensorSquare U) ≤ -C1*(1+tensorSquare U) := by
        simpa only [neg_mul] using (neg_le_neg (mul_le_mul_of_nonneg_right
          (le_max_left C1 C2) (add_nonneg zero_le_one (tensorSquare_nonneg U))))
      exact he.trans h1
    have hs0 := M.calabiNorm_nonneg (hdom hy)
    have hc : (χ y)^2 ≤ 1 := by nlinarith [hχ0 y hy,hχ1 y hy]
    have hh := (mul_le_mul_of_nonneg_right hc hs0).trans (by simpa using hs)
    exact add_le_add hh (mul_le_mul_of_nonneg_left (htr y hy) ha)
  exact hFz.trans (hFzy.trans hFbound)
end KaehlerCalculus

end
end

end OAI
