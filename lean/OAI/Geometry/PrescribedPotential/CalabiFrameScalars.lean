import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiFrameCalculus
import OAI.Geometry.PrescribedPotential.CalabiPointInequalities
import OAI.Geometry.PrescribedPotential.CalabiRicciFrames
import OAI.Geometry.PrescribedPotential.HolomorphicDirection
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization

namespace OAI

/-! Calabi Frame Scalars. -/

section

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

lemma calabiNorm_nonneg {z : V n} (hz : z ∈ K.domain) : 0 ≤ K.calabiNorm z := by
  obtain ⟨B,w,hB,hw,hM⟩ := normalized_frame K.matrix z (K.positive z hz)
  have hwU : B w ∈ K.domain := hw ▸ hz
  have h := K.pull_calabiNorm B hB hwU
  rw [hw] at h
  rw [← h,(K.pull B hB).calabiNorm_at_one hM]
  exact tensorSquare_nonneg _

lemma pull_weightedTrace_undo (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    (D : Matrix (Fin n) (Fin n) ℂ) (hCD : frameMatrix B*D = 1) (w : V n) :
    (K.pull B hB).weightedTrace D w = (K.matrix (B w)).trace.re := by
  change (Dᴴ*((frameMatrix B)ᴴ*K.matrix (B w)*frameMatrix B)*D).trace.re = _
  have he : Dᴴ*((frameMatrix B)ᴴ*K.matrix (B w)*frameMatrix B)*D =
      (frameMatrix B*D)ᴴ*K.matrix (B w)*(frameMatrix B*D) := by
    simp only [Matrix.conjTranspose_mul,mul_assoc]
  rw [he,hCD,Matrix.conjTranspose_one,one_mul,mul_one]

lemma pull_ricciHessian_jet (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {w : V n} (hw : B w ∈ K.domain) :
    (fun i => mderiv (-Complex.I) (e i) (K.pull B hB).ricciHessian w) =
      frameRicciJet (fun i => mderiv (-Complex.I) (e i) K.ricciHessian (B w)) (frameMatrix B) := by
  funext i
  rw [K.pull_ricciHessian_hol B hB hw,mderiv_hol_coordinates]
  rfl

lemma pull_cutoff_max (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {z w : V n} (hz : z ∈ K.domain) (hw : B w = z)
    (D : Matrix (Fin n) (Fin n) ℂ) (hCD : frameMatrix B*D = 1)
    (χ : V n → ℝ) (a : ℝ)
    (hmax : IsLocalMax (fun y => (χ y)^2*K.calabiNorm y+a*(K.matrix y).trace.re) z) :
    IsLocalMax (fun y => (χ (B y))^2*(K.pull B hB).calabiNorm y+a*(K.pull B hB).weightedTrace D y) w := by
  have ht : Tendsto B (𝓝 w) (𝓝 z) := hw ▸ B.continuous.continuousAt
  have hnormw := K.pull_calabiNorm B hB (show B w ∈ K.domain by rw [hw]; exact hz)
  have htracew := K.pull_weightedTrace_undo B hB D hCD w
  change ∀ᶠ y in 𝓝 w, _ ≤ _
  dsimp only
  rw [hnormw,htracew,hw]
  filter_upwards [ht.eventually hmax,ht.eventually (K.isOpen.mem_nhds hz)] with y hy hym
  rw [K.pull_calabiNorm B hB hym,K.pull_weightedTrace_undo B hB D hCD]
  exact hy
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
