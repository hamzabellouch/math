import OAI.Geometry.RCD.Sobolev.CompactTorsionMassBound
import OAI.Geometry.RCD.Sobolev.InteriorTorsionLayer
import OAI.Geometry.RCD.Metric.EuclideanInteriorSmoothExtension

namespace OAI

/-! # Local harmonic square mass from a truncated boundary layer -/

open Set Metric Filter MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff Topology
noncomputable section
namespace RegularPointCoordinates

theorem harmonic_layer_mass_bound {n : ℕ} {R : ℝ} {f : Euclidean n → ℝ}
    (hR : 0<R) (hf : ContDiffOn ℝ ∞ f (ball 0 R))
    (hh : ∀ x∈ball (0:Euclidean n) R, (Δ f) x=0) :
    ∃ C : ℝ, 0<C ∧ ∀ δ : ℝ, 0<δ → 4*δ≤R → R*δ/4≤1 →
      ∃ b : ℝ, R-δ<b ∧ b<R ∧
        2*(n:ℝ)*(∫ x in ball (0:Euclidean n) (R-δ), (f x)^2)≤
          (C/δ)*(∫ x in ball 0 b \ ball 0 (R-δ), (f x)^2) := by
  obtain ⟨A,hA,hupper⟩ := euclideanInteriorTorsion_laplacian_upper n hR
  refine ⟨4*A/R,by positivity,?_⟩
  intro δ hδ hδR ht1
  obtain ⟨b,hab,hbR,hs,hcore⟩ := interior_torsion_layer (n:=n) hR hδ hδR
  have hb : 0<b := by linarith
  obtain ⟨F,hF,heq,_⟩ := exists_interior_smooth_extension hb hbR hf
  have ht : 0<R*δ/4 := by positivity
  have htR : R*δ/4<R^2 := by nlinarith
  have hT := euclideanInteriorTorsion_test (n:=n) hR ht htR
  have hFF : ∀ x∈tsupport (euclideanInteriorTorsion n R (R*δ/4)), (Δ F) x=0 := by
    intro x hx
    have hxb := hs hx
    have he : F=ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
      exact heq (ball_subset_closedBall hy)
    rw [(laplacian_congr_nhds he).self_of_nhds]
    exact hh x ((ball_subset_ball hbR.le) hxb)
  have hm := compact_torsion_mass_bound (c:=2*(n:ℝ)) hab.le
    (hF.1.of_le (by simp)) (hT.1.of_le (by simp)) hT.2.1 hs
    (euclideanInteriorTorsion_nonneg n R ht.le) hFF
    (by simpa only [neg_mul] using hcore) (hupper _ ht ht1)
  have he₁ : (∫ x in ball (0:Euclidean n) (R-δ), (F x)^2)=
      ∫ x in ball 0 (R-δ), (f x)^2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    change (F x)^2=(f x)^2
    rw [heq (ball_subset_closedBall ((ball_subset_ball hab.le) hx))]
  have he₂ : (∫ x in ball (0:Euclidean n) b \ ball 0 (R-δ), (F x)^2)=
      ∫ x in ball 0 b \ ball 0 (R-δ), (f x)^2 := by
    apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
    intro x hx
    change (F x)^2=(f x)^2
    rw [heq (ball_subset_closedBall hx.1)]
  have hec : A/(R*δ/4)=(4*A/R)/δ := by field_simp
  rw [he₁,he₂,hec] at hm
  exact ⟨b,hab,hbR,hm⟩

end RegularPointCoordinates

end

end OAI
