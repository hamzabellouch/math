import OAI.MeasureTheory.Falconer.Graphs.RoundedGraphCounts

namespace OAI

/-! The original planar point and projection counts determine all size
parameters in the rounded graph. -/
namespace Falconer

 theorem rounded_graph_size_bounds {δ σ a b L : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (U : Finset (Space 2)) (hU : U.Nonempty) (hsep : FiniteSeparatedAt δ U)
    (m P : ℕ) (hP : 0 < P) (hL : 0 ≤ L) (hm : δ ≤ (m:ℝ)*σ)
    (hpa : (projectionCells δ a U).card ≤ P) (hpb : (projectionCells δ b U).card ≤ P)
    (hlarge : (P:ℝ)^2 ≤ L*(U.card:ℝ)) :
    let G := U.image (roundedProjectionCoordinates σ a b)
    let X := G.image (fun p => p 0)
    let Y := G.image (fun p => p 1)
    let F : ℝ := 5*(2*(m:ℝ)+3)
    X.Nonempty ∧ Y.Nonempty ∧
      (X.card:ℝ) ≤ F*(P:ℝ) ∧ (Y.card:ℝ) ≤ F*(P:ℝ) ∧
      (X.card:ℝ) ≤ (L*F^2)*(Y.card:ℝ) ∧
      (P:ℝ) ≤ L*F*(X.card:ℝ) ∧
      (X.card:ℝ)*(Y.card:ℝ) ≤ (L*F^2)*(U.card:ℝ) := by
  classical
  dsimp only
  let G := U.image (roundedProjectionCoordinates σ a b)
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let F : ℝ := 5*(2*(m:ℝ)+3)
  have hX : X.Nonempty := (hU.image _).image _
  have hY : Y.Nonempty := (hU.image _).image _
  have hx : (X.card:ℝ) ≤ F*(P:ℝ) :=
    roundedProjectionCoordinates_coordinate_upper hδ hσ U m P hm hpa hpb 0
  have hy : (Y.card:ℝ) ≤ F*(P:ℝ) :=
    roundedProjectionCoordinates_coordinate_upper hδ hσ U m P hm hpa hpb 1
  have hc : G.card = U.card := roundedProjectionCoordinates_card hδ hσ hab ha hb hsmall U hsep
  have hg : (U.card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by
    rw [← hc]
    exact_mod_cast coordinate_graph_card_le X Y G (fun p hp =>
      ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩)
  obtain ⟨hxy,_,hpx,_,hprod⟩ := coordinate_graph_scaled_bounds
    (Nat.cast_pos.mpr hX.card_pos) (Nat.cast_pos.mpr hY.card_pos)
    (Nat.cast_pos.mpr hP) (by dsimp [F]; positivity) hL hx hy hg hlarge
  exact ⟨hX,hY,hx,hy,hxy,hpx,hprod⟩

 theorem rounded_graph_density_bound {δ σ a b ρ Q : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (U A : Finset (Space 2)) (hAU : A ⊆ U) (hsep : FiniteSeparatedAt δ U)
    (hρ : 0 ≤ ρ) (hQ : 0 < Q) (hdense : ρ*(U.card:ℝ) ≤ (A.card:ℝ))
    (hprod :
      (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 0)).card:ℝ)*
        (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 1)).card:ℝ) ≤ Q*(U.card:ℝ)) :
    (ρ/Q)*(((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 0)).card:ℝ)*
      (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 1)).card:ℝ) ≤
      ((A.image (roundedProjectionCoordinates σ a b)).card:ℝ) := by
  have hi := (roundedProjectionCoordinates_injOn hδ hσ hab ha hb hsmall U hsep).mono hAU
  rw [Finset.card_image_of_injOn hi]
  exact coordinate_graph_density hρ hQ hprod hdense

end Falconer

end OAI
