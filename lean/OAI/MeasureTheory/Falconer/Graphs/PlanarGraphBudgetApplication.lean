import OAI.MeasureTheory.Falconer.Estimates.RoundedPlanarObstruction
import OAI.MeasureTheory.Falconer.Estimates.PlanarCommonBudget
import OAI.MeasureTheory.Falconer.Geometry.ProjectionRatioRegularity

namespace OAI

/-! Applying the original planar obstruction with one polynomial budget.
All coordinate, density and directional costs are now discharged. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planar_graph_budget_application {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (δ W ρ a b t : ℝ) (M P : ℕ)
        (I J : Finset ℝ) (U : Finset (Space 2)) (H : ℝ → Finset (Space 2)),
      0 < δ → δ ≤ 1 → 1 ≤ W → 0 < ρ → ρ⁻¹ ≤ W → 1 ≤ M →
      α = δ/(64*(M:ℝ)^2) → 4000000*W^5*(M:ℝ)^6 ≤ S →
      b ≠ a → |a| ≤ 1 → |b| ≤ 1 → 4/(M:ℝ) ≤ |b-a| →
      2*κ ≤ t → t ≤ 2 → 0 < P → J.Nonempty → U.Nonempty →
      (∀ p ∈ U, ∀ i, |p i| ≤ 1) → FiniteSeparatedAt δ U →
      NormalizedFiniteBallBound δ t W U →
      (projectionCells δ a U).card ≤ P → (projectionCells δ b U).card ≤ P →
      (P:ℝ)^2 ≤ W*(U.card:ℝ) →
      J ⊆ I → (I.card:ℝ) ≤ W*(J.card:ℝ) → (∀ i ∈ I, |i| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ W*r^(2*κ)*(I.card:ℝ)) →
      (∀ j ∈ J, 4/(M:ℝ) ≤ |j-a| ∧ 4/(M:ℝ) ≤ |j-b|) →
      (∀ j ∈ J, H j ⊆ U) → (∀ j ∈ J, ρ*(U.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, (projectionCells δ j (H j)).card ≤ P) →
      Real.log (655*(M:ℝ)*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := rounded_planar_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro δ W ρ a b t M P I J U H hδ hδ1 hW hρ hρW hM hcompat hbudget
    hab ha hb hgap ht ht2 hP hJ hU hUbound hUsep hUreg hpa hpb hlarge
    hJI hIJ hIbound hIball hJsep hHU hHsize hHproj hlog
  let α := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let MR : ℝ := M
  let σ := δ/(64*MR)
  let C := 128*MR^2
  let m : ℕ := 64*M
  let q : ℕ := 64*M^2
  let k : ℕ := 2*M^2
  let F : ℝ := 5*(2*(m:ℝ)+3)
  let Q := W*F^2
  let B : ℝ := (2*(k:ℝ)+3)*(2*MR+3)*(2*(q:ℝ)+3)
  have hMR : 1 ≤ MR := by
    change (1:ℝ) ≤ (M:ℝ)
    exact_mod_cast hM
  have hMRpos : 0 < MR := lt_of_lt_of_le zero_lt_one hMR
  have hα : 0 < α := by positivity
  have hS : 0 < S := Real.exp_pos _
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hmR : (m:ℝ) = 64*MR := by dsimp [m,MR]; push_cast; rfl
  have hqR : (q:ℝ) = 64*MR^2 := by dsimp [q,MR]; push_cast; rfl
  have hkR : (k:ℝ) = 2*MR^2 := by dsimp [k,MR]; push_cast; rfl
  have hFform : F = 5*(2*(64*MR)+3) := by dsimp [F]; rw [hmR]
  have hBform : B = (2*(2*MR^2)+3)*(2*MR+3)*(2*(64*MR^2)+3) := by
    dsimp [B]; rw [hkR,hqR]
  obtain ⟨hσ,hσ1,_,hs,hδσ,hδα,hC,hsmall,hscale,herror⟩ :=
    planar_grid_scale_bounds hδ hδ1 hMR hab ha hb hgap
  rw [← hcompat] at hs hδα hscale herror
  change σ = MR*α at hs
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := by
    dsimp [F]
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  have hQ1 : 1 ≤ Q := by
    have hF2 : 1 ≤ F^2 := by nlinarith only [hF1]
    dsimp [Q]
    nlinarith only [hW,hF2]
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hbasepos : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hbase2 : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith only [ha,hb])
  have hbase1 : 1 ≤ 4/|b-a| := (le_div_iff₀ hbasepos).2 (by linarith only [hbase2])
  have hbaseM : 4/|b-a| ≤ MR := by
    apply (div_le_iff₀ hbasepos).2
    have hh := (div_le_iff₀ hMRpos).1 hgap
    simpa only [mul_comm] using hh
  obtain ⟨hFbound,hQbound,hBbound,hRbound⟩ := planar_grid_polynomial_costs
    hMR hW0 hW0 hbase1 hbaseM (by linarith only [ht,hκ] : 0 ≤ t) ht2
  rw [← hFform] at hFbound hQbound hBbound
  rw [← hBform] at hBbound
  obtain ⟨hMb,hQb,hBb,hRb,hDb,hρb⟩ := planar_common_budget hW hMR
  have hMS : MR ≤ S := hMb.trans hbudget
  have hQS : Q ≤ S := hQbound.trans (hQb.trans hbudget)
  have hBC : B*W*F ≤ S := hBbound.trans (hBb.trans hbudget)
  have hRC : (W*(4/|b-a|)^t*4^t)*C^t ≤ S := hRbound.trans (hRb.trans hbudget)
  have hQρ : Q/ρ ≤ S := by
    have hh := mul_le_mul hQbound hρW (inv_nonneg.mpr hρ.le) (by positivity)
    have he : (429025*W*MR^2)*W = 429025*W^2*MR^2 := by ring
    rw [he] at hh
    have hstep : Q/ρ ≤ 429025*W^2*MR^2 := by simpa only [div_eq_mul_inv] using hh
    exact hstep.trans (hρb.trans hbudget)
  have hden : S⁻¹ ≤ ρ/Q := by
    apply (le_div_iff₀ hQpos).2
    have hh : Q ≤ S*ρ := (div_le_iff₀ hρ).1 hQρ
    have hi := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hS.le)
    have he : S⁻¹*(S*ρ) = ρ := by field_simp
    rw [he] at hi
    simpa only [mul_comm] using hi
  have hc : ∀ j ∈ J, projectionRatio a b j ≠ 0 ∧ |projectionRatio a b j| ≤ MR ∧
      |(projectionRatio a b j)⁻¹| ≤ MR := by
    intro j hj
    have hr : 0 < 4/MR := by positivity
    have hby : 4/MR ≤ |b-j| := by simpa only [abs_sub_comm] using (hJsep j hj).2
    obtain ⟨h0,h1,h2⟩ := planar_projection_ratio_bound hr ha hb (hIbound j (hJI hj))
      (hJsep j hj).1 hby
    have hh : 2/(4/MR) ≤ MR := by
      have he : 2/(4/MR) = MR/2 := by field_simp; norm_num
      rw [he]
      linarith only [hMR]
    exact ⟨h0,h1.trans hh,h2.trans hh⟩
  have hdirscale : δ ≤ (64*MR^2)*α := hδα.le
  have hdirsep : 8/|b-a| ≤ 64*MR^2 := by
    have he : 8/|b-a| = 2*(4/|b-a|) := by ring
    rw [he]
    nlinarith only [hbaseM,hMR]
  have hdircost : (W*W)*(64*MR^2)^(2*κ) ≤ S := by
    have hd := planar_direction_polynomial_cost hMR hW0 hW0 (by linarith only [hκ1] : 2*κ ≤ 2)
    calc
      _ ≤ 4096*W*W*MR^4 := hd
      _ = 4096*W^2*MR^4 := by ring
      _ ≤ _ := hDb.trans hbudget
  have hball : ∀ u r : ℝ, α ≤ r → r ≤ 1 →
      scalarBallMass (J.image (projectionRatio a b)) u r ≤ S*r^(2*κ)*((J.image (projectionRatio a b)).card:ℝ) := by
    intro u r hr _
    have hh := projectionRatio_ball_bound hα (by linarith only [hκ] : 0 ≤ 2*κ) hW
      (by positivity : 0 ≤ 64*MR^2) hW0 hab hb hdirscale hdirsep I J hJI
      (fun j hj => projectionRatio_ne_pole (hc j hj).1) hIbound hIJ hIball u r hr
    have hm := mul_le_mul_of_nonneg_right hdircost
      (mul_nonneg (Real.rpow_nonneg (hα.le.trans hr) (2*κ))
        (Nat.cast_nonneg (α := ℝ) (J.image (projectionRatio a b)).card))
    exact hh.trans (by simpa only [mul_assoc] using hm)
  have hlogF : Real.log (F*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 := by
    have hp : 0 < (P:ℝ) := Nat.cast_pos.mpr hP
    have hh := Real.log_le_log (mul_pos hFpos hp) (mul_le_mul_of_nonneg_right hFbound hp.le)
    exact hh.trans hlog
  apply hmain N hN δ σ a b t W C W ρ m q k M P J U H hδ hσ hσ1 hab ha hb hsmall hM hMS
  · change α*MR ≤ σ
    rw [hs,mul_comm]
  · rw [hmR]
    exact hδσ.le
  · rw [hqR]
    exact hδα.le
  · change (1+MR)*σ ≤ (k:ℝ)*α
    rw [hs,hkR]
    have hh : (1+MR)*MR ≤ 2*MR^2 := by nlinarith only [hMR]
    have hm := mul_le_mul_of_nonneg_right hh hα.le
    nlinarith only [hm]
  · exact hC
  · exact hscale
  · exact herror
  · exact ht
  · exact ht2
  · exact hW
  · exact hW0
  · exact hρ.le
  · exact hQ1
  · exact hQS
  · exact hden
  · exact hBC
  · exact hRC
  · exact hP
  · exact hJ
  · exact hU
  · exact hUbound
  · exact hUsep
  · exact hUreg
  · exact hpa
  · exact hpb
  · exact hlarge
  · exact hc
  · exact hHU
  · exact hHsize
  · exact hHproj
  · exact hball
  · exact hlogF

end Falconer

end OAI
