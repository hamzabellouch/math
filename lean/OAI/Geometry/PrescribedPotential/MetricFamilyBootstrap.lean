import Mathlib
import OAI.Geometry.PrescribedPotential.CompactCoefficientBootstrap
import OAI.Geometry.PrescribedPotential.EncodedMetricEquation
import OAI.Geometry.PrescribedPotential.MatrixCoefficientSmooth
import OAI.Geometry.PrescribedPotential.MatrixRealFrames

namespace OAI

/-! Metric Family Bootstrap. -/

section

noncomputable section
open Set Filter Topology Matrix Metric Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open EllipticKernel FrozenPoisson HigherJet KaehlerCalculus
variable {n : ℕ} {α : Type*}
local instance bootstrapRealECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)
local instance bootstrapRealHMIP : InnerProductSpace ℝ (HM n) := InnerProductSpace.rclikeToReal ℂ (HM n)

lemma metric_family_bootstrap {U : Set (EC n)} (hU : IsOpen U)
    (M : α → LocalKaehlerField n) (r : α → EC n → HM n)
    (hdom : ∀ s x, x ∈ U → coordinateEquiv n x ∈ (M s).domain)
    (hr : ∀ s, ContDiffOn ℝ ∞ (r s) U)
    (hric : ∀ s x, x ∈ U → encode n ((M s).ricciHessian (coordinateEquiv n x)) = r s x)
    (hfirst : ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ s x, x ∈ K →
      ‖fderiv ℝ (fun y => encode n ((M s).matrix (coordinateEquiv n y))) x‖ ≤ C)
    (hframeBound : ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ s x, x ∈ K →
      ∀ C D : Mat n, C*D=1 → D*C=1 → Cᴴ*(M s).matrix (coordinateEquiv n x)*C=1 → ‖C‖ ≤ B ∧ ‖D‖ ≤ B)
    (hrbounds : ∀ m K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ j, j ≤ m → ∀ s x, x ∈ K →
      ‖iteratedFDeriv ℝ j (r s) x‖ ≤ C) :
    ∀ m, 1 ≤ m → ∀ K, IsCompact K → K ⊆ U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s x, x ∈ K →
        ‖iteratedFDeriv ℝ m (fun y => encode n ((M s).matrix (coordinateEquiv n y))) x‖ ≤ C := by
  classical
  let u : α → EC n → HM n := fun s y => encode n ((M s).matrix (coordinateEquiv n y))
  have hu : ∀ s, ContDiffOn ℝ ∞ (u s) U := by
    intro s x hx
    exact ((encode n).contDiff.contDiffAt.comp x
      (((M s).smooth.contDiffAt ((M s).isOpen.mem_nhds (hdom s x hx))).comp x
        (coordinateEquiv n).contDiff.contDiffAt)).contDiffWithinAt
  have hf (s : α) (x : EC n) : ∃ C D : Mat n, C*D=1 ∧ D*C=1 ∧
      (x ∈ U → Cᴴ*(M s).matrix (coordinateEquiv n x)*C=1) := by
    by_cases hx : x ∈ U
    · obtain ⟨C,hC,hN⟩ := whitening _ ((M s).positive _ (hdom s x hx))
      obtain ⟨Q,rfl⟩ := hC
      exact ⟨Q,↑Q⁻¹,Q.mul_inv,Q.inv_mul,fun _ => hN⟩
    · exact ⟨1,1,by simp,by simp,fun hh => (hx hh).elim⟩
  choose C D hCD hDC hN using hf
  let τ : α → EC n → EC n ≃L[ℝ] EC n := fun s x => frame (C s x) (D s x) (hCD s x) (hDC s x)
  let basis := stdOrthonormalBasis ℝ (EC n)
  apply quasilinear_compact_coefficient_bootstrap (principalBilinear basis) hU basis u r inverseCoefficient quadraticCoefficient τ hu hr
  · intro s x hx
    exact inverseCoefficient_smooth (by
      change ((M s).matrix (coordinateEquiv n x)).det ≠ 0
      exact ne_of_gt ((M s).positive _ (hdom s x hx)).det_pos)
  · intro s x hx
    exact quadraticCoefficient_smooth (by
      change ((M s).matrix (coordinateEquiv n x)).det ≠ 0
      exact ne_of_gt ((M s).positive _ (hdom s x hx)).det_pos)
  · intro s x hx
    exact (encoded_metric_equation basis (M s) (hdom s x hx)).trans (by rw [hric s x hx])
  · intro s x hx H
    exact frame_gram basis _ (C s x) (D s x) (hCD s x) (hDC s x) (hN s x hx) H
  · intro K hK hKU
    obtain ⟨B,hB,hbound⟩ := hframeBound K hK hKU
    obtain ⟨R,hR,hRbound⟩ := frame_uniform_bound (n := n) B
    refine ⟨R,hR,fun s x hx => ?_⟩
    obtain ⟨hc,hd⟩ := hbound s x hx (C s x) (D s x) (hCD s x) (hDC s x) (hN s x (hKU hx))
    exact hRbound _ _ hc hd _ _
  · intro K hK hKU
    obtain ⟨B,hB,hbound⟩ := hframeBound K hK hKU
    obtain ⟨J,hJ⟩ := hfirst K hK hKU
    let P : Set (HM n) := (fun p : Mat n × Mat n => encode n (p.2ᴴ*p.2)) '' boundedFramePairs B
    have hP : IsCompact P := (boundedFramePairs_compact B).image
      ((encode n).continuous.comp ((continuous_snd.matrix_conjTranspose).matrix_mul continuous_snd))
    have hpositive : ∀ p ∈ P, ((encode n).symm p).PosDef := by
      rintro p ⟨q,hq,rfl⟩
      rw [ContinuousLinearEquiv.symm_apply_apply]
      simpa only [mul_one] using Matrix.PosDef.one.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_iff_isUnit.mpr (boundedFramePairs_units hq).2)
    refine ⟨P ×ˢ closedBall (0:EC n →L[ℝ] HM n) J,hP.prod (isCompact_closedBall _ _),?_,?_⟩
    · intro s x hx
      refine ⟨?_,by simpa only [firstJet,mem_closedBall,dist_zero_right] using hJ s x hx⟩
      obtain ⟨hc,hd⟩ := hbound s x hx (C s x) (D s x) (hCD s x) (hDC s x) (hN s x (hKU hx))
      refine ⟨(C s x,D s x),⟨hc,hd,hCD s x,hDC s x⟩,?_⟩
      change encode n ((D s x)ᴴ*D s x) = encode n ((M s).matrix (coordinateEquiv n x))
      rw [unnormalize_matrix (hCD s x) (hN s x (hKU hx))]
    · intro p hp
      have hd := ne_of_gt (hpositive p.1 hp.1).det_pos
      exact ⟨inverseCoefficient_smooth hd,quadraticCoefficient_smooth hd⟩
  · exact hrbounds
end MetricSystem

end
end

end OAI
