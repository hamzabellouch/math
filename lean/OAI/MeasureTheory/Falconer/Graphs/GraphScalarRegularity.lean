import OAI.MeasureTheory.Falconer.Graphs.GraphDensity
import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates

namespace OAI

/-! A dense small-projection graph transfers its planar ball bound to the
actual scalar reference set, with half the planar exponent. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_graph_ball_bound {δ t c M K Kreg ρ L : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (hK : 0 ≤ K) (hKreg : 1 ≤ Kreg) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (X Y : Finset ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hdegree : ∀ x ∈ X, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ X, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsize : (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ))
    (hsum : ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ)) :
    ∀ z r : ℝ, δ ≤ r →
      scalarBallMass X z r ≤
        Real.sqrt ((2*K*Kreg*L/ρ)*(1+4*M)^t)*r^(t/2)*(X.card:ℝ) := by
  classical
  intro z r hdr
  let F := X.filter fun x => |x-z| ≤ r
  have hr : 0 < r := hδ.trans_le hdr
  have hXpos : 0 < (X.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hKreg0 : 0 ≤ Kreg := zero_le_one.trans hKreg
  let C := (2*K*Kreg*L/ρ)*(1+4*M)^t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnonneg : 0 ≤ Real.sqrt C*r^(t/2) := by positivity
  by_cases hF : F.Nonempty
  · have hFsub : F ⊆ X := Finset.filter_subset _ _
    have hFsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image
        (Finset.add_subset_add hFsub (Finset.Subset.refl _))))).trans hsum
    have hrelative := scalar_graph_density_relative hδ hdr hc hM ht hKreg hK hXpos hρ
      F Y hF hY e G hreg
      (fun x hx y hy hne => hsep x (hFsub hx) y (hFsub hy) hne)
      (fun _ hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => hdegree x (hFsub hx)) (fun x hx => hgraph x (hFsub hx)) hsize hFsum
    rw [Real.mul_rpow (by positivity : 0 ≤ 1+4*M) hr.le] at hrelative
    have hrel : ((F.card:ℝ)/(X.card:ℝ))^2 ≤ C*r^t := by
      convert hrelative using 1; ring
    have he : (Real.sqrt C*r^(t/2))^2 = C*r^t := by
      rw [mul_pow,Real.sq_sqrt hC,← Real.rpow_mul_natCast hr.le]
      norm_num
    have hquot : (F.card:ℝ)/(X.card:ℝ) ≤ Real.sqrt C*r^(t/2) := by
      nlinarith
    exact (div_le_iff₀ hXpos).1 hquot
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
