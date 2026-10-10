import OAI.Geometry.NodalSets.Hausdorff.LiteralNodalCertificate

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

theorem LiteralNodalCertificate.uniform_persistence
    {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {S : Coord → ℝ}
    {Q U : Set Coord} {n : ℕ} {f : Coord → ℝ} {M : ℝ}
    (h : LiteralNodalCertificate g S Q U n f M) :
    ∃ eps > 0, ∀ v : Coord → ℝ, Continuous v →
      (∀ x, |v x-f x| < eps) →
      ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
        ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | v y.1 = 0}) := by
  obtain ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hw,mu,hmu,hs,hp⟩ := h
  exact ⟨mu,hmu,fun v hv hclose ↦ hp v hv (fun x hx y hy ↦ hclose y)⟩

end
end Yau.Geometry

end OAI
