import OAI.MeasureTheory.Falconer.Graphs.RoundedGraphData
import OAI.MeasureTheory.Falconer.Graphs.CoordinateGraphObstruction
import OAI.MeasureTheory.Falconer.Geometry.ProjectionRatioBounds

namespace OAI

/-! The dense scalar obstruction applies to original planar sets and
large common slices. Every coordinate and graph hypothesis is derived. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rounded_planar_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (δ σ a b t K C L ρ : ℝ) (m q k M P : ℕ)
        (J : Finset ℝ) (U : Finset (Space 2)) (H : ℝ → Finset (Space 2)),
      let F : ℝ := 5*(2*(m:ℝ)+3)
      let Q := L*F^2
      let B : ℝ := (2*(k:ℝ)+3)*(2*(M:ℝ)+3)*(2*(q:ℝ)+3)
      0 < δ → 0 < σ → σ ≤ 1/2 → b ≠ a → |a| ≤ 1 → |b| ≤ 1 →
      4*σ < (δ/(4/|b-a|))/4 → 1 ≤ M → (M:ℝ) ≤ S → α*(M:ℝ) ≤ σ →
      δ ≤ (m:ℝ)*σ → δ ≤ (q:ℝ)*α → (1+(M:ℝ))*σ ≤ (k:ℝ)*α →
      1 ≤ C → (δ/(4/|b-a|))/4 ≤ C*α → 2*σ ≤ (C-1)*α →
      2*κ ≤ t → t ≤ 2 → 1 ≤ K → 0 ≤ L → 0 ≤ ρ →
      1 ≤ Q → Q ≤ S → S⁻¹ ≤ ρ/Q → B*L*F ≤ S →
      (K*(4/|b-a|)^t*4^t)*C^t ≤ S →
      0 < P → J.Nonempty → U.Nonempty →
      (∀ p ∈ U, ∀ i, |p i| ≤ 1) → FiniteSeparatedAt δ U →
      NormalizedFiniteBallBound δ t K U →
      (projectionCells δ a U).card ≤ P → (projectionCells δ b U).card ≤ P →
      (P:ℝ)^2 ≤ L*(U.card:ℝ) →
      (∀ j ∈ J, projectionRatio a b j ≠ 0 ∧ |projectionRatio a b j| ≤ M ∧ |(projectionRatio a b j)⁻¹| ≤ M) →
      (∀ j ∈ J, H j ⊆ U) → (∀ j ∈ J, ρ*(U.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, (projectionCells δ j (H j)).card ≤ P) →
      (∀ u r : ℝ, α ≤ r → r ≤ 1 → scalarBallMass (J.image (projectionRatio a b)) u r ≤
        S*r^(2*κ)*((J.image (projectionRatio a b)).card:ℝ)) →
      Real.log (F*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := coordinate_graph_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro δ σ a b t K C L ρ m q k M P J U H hδ hσ hσ1 hab ha hb hsmall
    hM hMS hασ hm hq hk hC hscale herror ht ht2 hK hL hρ hQ hQS hdensity
    hprojectioncost hregularcost hP hJ hU hUbound hUsep hUreg hpa hpb hlarge hc hHU hHlarge hHp hball hlog
  let α := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let f := roundedProjectionCoordinates σ a b
  let G := U.image f
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let F : ℝ := 5*(2*(m:ℝ)+3)
  let Q := L*F^2
  let B : ℝ := (2*(k:ℝ)+3)*(2*(M:ℝ)+3)*(2*(q:ℝ)+3)
  have hα : 0 < α := by positivity
  have hMR : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hασ' : α ≤ σ := by nlinarith
  have hF : 0 < F := by dsimp [F]; positivity
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨hX,hY,hXupper,_,hXY,hPX,hprod⟩ := rounded_graph_size_bounds
    hδ hσ hab ha hb hsmall U hU hUsep m P hP hL hm hpa hpb hlarge
  have hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → α ≤ |x-y| := by
    intro x hx y hy hne
    exact hασ'.trans (roundedProjectionCoordinates_coordinate_separated hσ U 0 x hx y hy hne)
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → α ≤ |x-y| := by
    intro x hx y hy hne
    exact hασ'.trans (roundedProjectionCoordinates_coordinate_separated hσ U 1 x hx y hy hne)
  have hXd : ∀ x ∈ X, |x| ≤ 1 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact roundedProjectionCoordinates_bound hσ hσ1 ha hb z (hUbound z hz) 0
  have hGregular : NormalizedFiniteBallBound α t S G := by
    have hr := roundedProjectionCoordinates_regular hδ hσ hα hC hab ha hb hscale herror
      hsmall ht0 hK U hUsep hUreg
    intro z r hr0 hr1
    have hh := mul_le_mul_of_nonneg_right hregularcost
      (mul_nonneg (Real.rpow_nonneg (hα.le.trans hr0) t) (Nat.cast_nonneg G.card))
    exact (hr z r hr0 hr1).trans (by simpa only [mul_assoc,G,f,S] using hh)
  have hdense : ∀ j ∈ J, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ((H j).image f).card := by
    intro j hj
    have hh := rounded_graph_density_bound hδ hσ hab ha hb hsmall U (H j)
      (hHU j hj) hUsep hρ hQpos (hHlarge j hj) hprod
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdensity
      (Nat.cast_nonneg X.card)) (Nat.cast_nonneg Y.card)).trans hh
  have hproj : ∀ j ∈ J,
      ((scalarCells α (((H j).image f).image (cartesianProjection (projectionRatio a b j)))).card:ℝ) ≤ S*(X.card:ℝ) := by
    intro j hj
    have hnorm := projectionRatio_normalizing_bound (projectionRatio_ne_pole (hc j hj).1)
      hMR (hc j hj).2.1
    have hgrid : (1+|(j-a)/(b-j)|)*σ ≤ (k:ℝ)*α := by
      have hcb : 1+|(j-a)/(b-j)| ≤ 1+(M:ℝ) := by
        have hcc := (hc j hj).2.1
        change |(j-a)/(b-j)| ≤ (M:ℝ) at hcc
        linarith
      have hh := mul_le_mul_of_nonneg_right hcb hσ.le
      exact hh.trans hk
    have hn := (roundedProjectionCoordinates_projection_cells hα hσ hδ hab
      (projectionRatio_ne_pole (hc j hj).1) (H j) k M q hgrid hnorm hq).trans
      (Nat.mul_le_mul_left _ (hHp j hj))
    have hcP : ((scalarCells α (((H j).image f).image
        (cartesianProjection (projectionRatio a b j)))).card:ℝ) ≤ B*(P:ℝ) := by
      have hnR : ((scalarCells α (((H j).image (roundedProjectionCoordinates σ a b)).image
          (cartesianProjection ((j-a)/(b-j))))).card:ℝ) ≤
          (((2*k+3)*(2*M+3)*(2*q+3)*P:ℕ):ℝ) := by exact_mod_cast hn
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,B,f,projectionRatio] using hnR
    have hmP := mul_le_mul_of_nonneg_left hPX (show 0 ≤ B by dsimp [B]; positivity)
    have hcost := mul_le_mul_of_nonneg_right hprojectioncost (Nat.cast_nonneg X.card)
    apply hcP.trans
    calc
      _ ≤ B*(L*F*(X.card:ℝ)) := hmP
      _ = (B*L*F)*(X.card:ℝ) := by ring
      _ ≤ S*(X.card:ℝ) := hcost
  have hlogX : Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 :=
    (Real.log_le_log (Nat.cast_pos.mpr hX.card_pos) hXupper).trans hlog
  apply hmain N hN M hM hMS Q hQ hQS t J (projectionRatio a b) G (fun j => (H j).image f)
    ht ht2 hJ (hU.image f) hXY hXd hXsep hYsep
  · intro j hj
    exact scalar_dilation_separated (by positivity : (0:ℝ) < M) hασ
      (hc j hj).1 (hc j hj).2.2 Y
      (roundedProjectionCoordinates_coordinate_separated hσ U 1)
  · exact hc
  · intro j hj
    exact Finset.image_subset_image (hHU j hj)
  · exact hdense
  · exact hproj
  · exact hGregular
  · exact hball
  · exact hlogX

end Falconer

end OAI
