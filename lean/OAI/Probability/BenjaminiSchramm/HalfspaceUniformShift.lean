import OAI.Probability.BenjaminiSchramm.HalfspaceFiniteShiftProfile

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem halfspace_ceiling_shift_profile_uniform_rate [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1) :
    ∃ S : ℝ, 0 < S ∧ ∀ ρ q : ℝ, 0 ≤ q →
      (∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ 0})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ρ*k))) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ c})
        {v | -k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ -k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ρ*k+(S+abs ρ)*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_ascent_to_level
    hc hl hq μ hμ hstat hu R hR hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδlt : δ < 1 := (min_le_left _ _).trans_lt hp1
  let s := -Real.log δ
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hδ hδlt)
  let S := s*A
  refine ⟨S,by dsimp [S]; positivity,fun ρ q hq0 hprofile => ?_⟩
  obtain ⟨D,hD,hbound⟩ := hprofile
  refine ⟨D*ENNReal.ofReal (Real.exp (s*B+abs ρ*R)),
    ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top,fun k hk c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hylo,hyhi,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_ceiling_root_ascent hc hl a p k c R w hylo (fun v hv => (hw v hv).2) hq0
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδlt.le hlen hXY
  have hshift := hbound (k+G.orbitAdjustedHeight a x y) (by linarith) y
  apply hh.trans ((mul_le_mul' le_rfl hshift).trans ?_)
  have hheight : 0 ≤ G.orbitAdjustedHeight a x y := hc0.trans hylo
  have hr₁ := mul_le_mul_of_nonneg_right (le_abs_self ρ) hheight
  have hr₂ := mul_le_mul_of_nonneg_left hyhi (abs_nonneg ρ)
  have he : -Real.log δ*(A*c+B)+ρ*(k+G.orbitAdjustedHeight a x y) ≤
      (s*B+abs ρ*R)+(ρ*k+(S+abs ρ)*c) := by
    dsimp [s,S]
    nlinarith
  calc
    _ = D*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+ρ*(k+G.orbitAdjustedHeight a x y))) := by
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ D*ENNReal.ofReal (Real.exp ((s*B+abs ρ*R)+(ρ*k+(S+abs ρ)*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]

theorem halfspace_floor_shift_profile_uniform_rate [Fintype G.VertexOrbit] [Nontrivial V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ)
    (hu : ¬G.CombinatoriallyUnimodular) (R : ℝ) (hR : 0 ≤ R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp0 : (0 : ℝ) < p) (hp1 : (p : ℝ) < 1) :
    ∃ S : ℝ, 0 < S ∧ ∀ ρ q : ℝ, 0 ≤ q →
      (∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ k : ℝ, 0 ≤ k → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | 0 ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        D*ENNReal.ofReal (Real.exp (ρ*k))) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ, 0 ≤ c → ∀ x : V,
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {v | -c ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v})
        {v | k-R ≤ G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ∧
          G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) x v ≤ k+R} ω x)^q ∂G.law p) ≤
        C*ENNReal.ofReal (Real.exp (ρ*k+(S+abs ρ)*c)) := by
  let a := G.stationaryOrbitWeight μ
  obtain ⟨A,B,hA,hB,hpaths⟩ := G.stationaryOrbitHeight_bounded_descent_to_level
    hc hl hq μ hμ hstat hu R hR hjump
  let δ := min (p : ℝ) (1-p)
  have hδ : 0 < δ := lt_min hp0 (sub_pos.mpr hp1)
  have hδlt : δ < 1 := (min_le_left _ _).trans_lt hp1
  let s := -Real.log δ
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hδ hδlt)
  let S := s*A
  refine ⟨S,by dsimp [S]; positivity,fun ρ q hq0 hprofile => ?_⟩
  obtain ⟨D,hD,hbound⟩ := hprofile
  refine ⟨D*ENNReal.ofReal (Real.exp (s*B+abs ρ*R)),
    ENNReal.mul_lt_top hD ENNReal.ofReal_lt_top,fun k hk c hc0 x => ?_⟩
  obtain ⟨y,w,hlen,hylo,hyhi,hw⟩ := hpaths c hc0 x
  have hXY := G.fractional_floor_root_descent hc hl a p k c R w hyhi (fun v hv => (hw v hv).1) hq0
  have hh := finite_energy_cancel_length _ _ δ A B c w.length hδ hδlt.le hlen hXY
  have hshift := hbound (k-G.orbitAdjustedHeight a x y) (by linarith) y
  apply hh.trans ((mul_le_mul' le_rfl hshift).trans ?_)
  have hheight : 0 ≤ -G.orbitAdjustedHeight a x y := by linarith
  have hr₁ := mul_le_mul_of_nonneg_right (le_abs_self ρ) hheight
  have hr₂ := mul_le_mul_of_nonneg_left
    (show -G.orbitAdjustedHeight a x y ≤ c+R by linarith) (abs_nonneg ρ)
  have he : -Real.log δ*(A*c+B)+ρ*(k-G.orbitAdjustedHeight a x y) ≤
      (s*B+abs ρ*R)+(ρ*k+(S+abs ρ)*c) := by
    dsimp [s,S]
    nlinarith
  calc
    _ = D*ENNReal.ofReal (Real.exp (-Real.log δ*(A*c+B)+ρ*(k-G.orbitAdjustedHeight a x y))) := by
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ D*ENNReal.ofReal (Real.exp ((s*B+abs ρ*R)+(ρ*k+(S+abs ρ)*c))) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he))
    _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _),mul_assoc]

end CriticalPercolation.BondGraph

end

end OAI
