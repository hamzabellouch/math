import OAI.MeasureTheory.Falconer.Graphs.GraphDensityRadius

namespace OAI

/-! Maximal-density normalization of the actual reference factor, retaining
the radius control supplied by its original planar graph. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_graph_reference_zoom {δ κ t c M K Kreg ρ L : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (hc : c ≠ 0) (hM : |c⁻¹| ≤ M) (hK : 0 ≤ K) (hKreg : 1 ≤ Kreg) (hρ : 0 < ρ)
    (X Y : Finset ℝ) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hbound : ∀ x ∈ X, |x| ≤ 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t Kreg G)
    (hdegree : ∀ x ∈ X, ρ*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ))
    (hgraph : ∀ x ∈ X, ∀ y ∈ Y, e x y → rowPoint x y ∈ G)
    (hsize : (G.card:ℝ) ≤ L*(X.card:ℝ)*(Y.card:ℝ))
    (hsum : ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ)) :
    ∃ z ∈ X, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧
      let F := X.filter fun x => |x-z| ≤ R
      let U := scalarZoom z R F
      U.Nonempty ∧ (R/2)^κ*(X.card:ℝ) ≤ (U.card:ℝ) ∧
      (∀ x ∈ U, |x| ≤ 1) ∧
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → δ/R ≤ |x-y|) ∧
      (∀ u r : ℝ, δ/R ≤ r → scalarBallMass U u r ≤ 2^κ*r^κ*(U.card:ℝ)) ∧
      1 ≤ ((2:ℝ)^(2*κ)*(2*K*Kreg*L/ρ)*(1+4*M)^t)*R^(t-2*κ) := by
  classical
  obtain ⟨z,hz,R,hRδ,hR2,hU,hmass,hUbound,hUsep,hUball⟩ :=
    scalar_maximal_density_zoom hδ hδ1 hκ X hX hbound hsep
  have hR : 0 < R := hδ.trans_le hRδ
  let F := X.filter fun x => |x-z| ≤ R
  have hFsub : F ⊆ X := Finset.filter_subset _ _
  have hF : F.Nonempty := Finset.image_nonempty.mp hU
  have hFsep := fun x hx y hy hne => hsep x (hFsub hx) y (hFsub hy) hne
  have hFlocal : ∀ x ∈ F, |x-z| ≤ R := fun _ hx => (Finset.mem_filter.mp hx).2
  have hFsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(X.card:ℝ) := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card
      (Finset.image_subset_image (Finset.add_subset_add hFsub (Finset.Subset.refl _))))) hsum
  have hrelative := scalar_graph_density_relative hδ hRδ hc hM ht hKreg hK
    (Nat.cast_pos.mpr (Finset.card_pos.mpr hX)) hρ F Y hF hY e G hreg hFsep hFlocal
    (fun x hx => hdegree x (hFsub hx)) (fun x hx => hgraph x (hFsub hx)) hsize hFsum
  have hm : (R/2)^κ*(X.card:ℝ) ≤ (F.card:ℝ) := by
    simpa only [scalarZoom_card hR.ne'] using hmass
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  rw [Real.mul_rpow (by positivity : 0 ≤ 1+4*M) hR.le] at hrelative
  have hrel : ((F.card:ℝ)/(X.card:ℝ))^2 ≤
      ((2*K*Kreg*L/ρ)*(1+4*M)^t)*R^t := by
    convert hrelative using 1; ring
  have hgap := scalar_density_graph_gap hR
    (Nat.cast_pos.mpr (Finset.card_pos.mpr hX)) hm hrel
  refine ⟨z,hz,R,hRδ,hR2,hU,hmass,hUbound,hUsep,hUball,?_⟩
  convert hgap using 1; ring

end Falconer

end OAI
