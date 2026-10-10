import OAI.Geometry.NodalSets.Charts.ChartPushforward
import OAI.Geometry.NodalSets.Elliptic.LocalSpatialJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def inverseSpatialJet (p : QuadParam Coord) : (k : ℕ) → Coord → Coord [×k]→L[ℝ] Coord
  | 0, x => (continuousMultilinearCurryFin0 ℝ Coord Coord).symm x
  | k+1, x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ Coord) Coord).symm
      ((fderiv ℝ (inverseSpatialJet p k) x).comp
        (ContinuousLinearMap.inverse (fderiv ℝ (rawQuadratic p) x)))

theorem inverseSpatialJet_smooth_at (p : QuadParam Coord) (x : Coord)
    (J : Coord ≃L[ℝ] Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (k : ℕ) : ContDiffAt ℝ ∞ (fun z : QuadParam Coord × Coord ↦ inverseSpatialJet z.1 k z.2) (p,x) := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ Coord Coord).symm.contDiff.contDiffAt.comp
      (p,x) contDiffAt_snd
  | succ k ih =>
    have hi : ContDiffAt ℝ ∞
        (fun z : QuadParam Coord × Coord ↦ ContinuousLinearMap.inverse (fderiv ℝ (rawQuadratic z.1) z.2)) (p,x) := by
      have h := contDiffAt_map_inverse (n := ∞) J
      rw [← hJ] at h
      exact h.comp (p,x) (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).contDiffAt
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ Coord) Coord).symm.contDiff.contDiffAt.comp
      (p,x) ((smooth_spatial_fderiv_at (fun p x ↦ inverseSpatialJet p k x) p x ih).clm_comp hi)

theorem inverseSpatialJet_eq (p : QuadParam Coord)
    (F : OpenPartialHomeomorph Coord Coord) (hF : (F : Coord → Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (k : ℕ) (x : Coord) (hx : x ∈ F.source) :
    inverseSpatialJet p k x = iteratedFDeriv ℝ k (F.symm : Coord → Coord) (F x) := by
  induction k generalizing x with
  | zero =>
    simp only [inverseSpatialJet,iteratedFDeriv_zero_eq_comp,Function.comp_def,F.left_inv hx]
  | succ k ih =>
    obtain ⟨J,hJe⟩ := hJ x hx
    have hfd : DifferentiableAt ℝ (F : Coord → Coord) x := by
      rw [hF]
      exact (rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x
    have hId : DifferentiableAt ℝ (iteratedFDeriv ℝ k (F.symm : Coord → Coord)) (F x) :=
      (hInv.contDiffAt (F.open_target.mem_nhds (F.map_source hx))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show (k : ℕ∞) < ⊤ by simp))
    have he : inverseSpatialJet p k =ᶠ[𝓝 x]
        (iteratedFDeriv ℝ k (F.symm : Coord → Coord)) ∘ F := by
      filter_upwards [F.open_source.mem_nhds hx] with z hz
      exact ih z hz
    have hd : fderiv ℝ (inverseSpatialJet p k) x =
        fderiv ℝ ((iteratedFDeriv ℝ k (F.symm : Coord → Coord)) ∘ F) x := he.fderiv_eq
    rw [fderiv_comp x hId hfd] at hd
    have hFder : fderiv ℝ (F : Coord → Coord) x = J.toContinuousLinearMap := by rw [hF,hJe]
    rw [hFder] at hd
    simp only [inverseSpatialJet,hd,hJe,ContinuousLinearMap.inverse_equiv]
    rw [ContinuousLinearMap.comp_assoc]
    have hcancel : J.toContinuousLinearMap.comp J.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ Coord := by ext v; simp
    rw [hcancel,ContinuousLinearMap.comp_id]
    rfl

end
end Yau.Geometry

end OAI
