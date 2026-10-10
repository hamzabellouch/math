import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphStep
import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphAt

namespace OAI

/-! # Uniform graph reduction at the direct or high-prefix geometry -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem exists_policy_graph_step_at
    (hpublished : PublishedGnomonicSurface) (m K : ℕ)
    {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ := 0) :
    ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ (P : PolicyJetData m), P.σ = σ → P.J = J → P.Z = Z →
      N₀ ≤ P.N → P.i+1 ≤ P.J →
      ∀ geometry : P.GraphGeometry,
      P.envelope K L Ψ ≤ P.graphCoefficient geometry.p*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L geometry.p Ψ)+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨k,hmin,herr⟩ := exists_policy_graph_error_order m hσ (T+1) minOrder
  obtain ⟨B,Z,H,C,hB,hZ,hH,hC,hgraph⟩ := exists_jetState_graph_step hpublished
    (m+1) K k (by omega) φ Ψ hφ hΨ hpos hzero hW hΨW hsupp
    (by positivity : 0 < 20*σ) (T+1+(11*(m+3):ℕ))
  obtain ⟨Hcap,hHcap,hcaps⟩ := exists_controlled_cap_partition (m+1) k
  let c₀ : ℝ := 1/4
  let Cgeo : ℝ := 1+4*Real.sqrt (m+3:ℕ)
  let Cap : ℝ := (4*c₀⁻¹+5)^(m+3)
  let V : ℝ := 16*Cgeo*(4+c₀⁻¹)
  let E : ℝ := Cap^2*((H*(4^k*Hcap)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
    C*((sphereMeasure (m+3)).real univ)^2)
  obtain ⟨Nerr,hNerr⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) E
  obtain ⟨Nlarge,hNlarge⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 20*σ) (40*Real.sqrt (m+3:ℕ)+4*Real.pi)
  let Nlist := Classical.choose (eventual_descriptor_list_scale 3 hB hσ)
  let Nwidth := Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ)
  refine ⟨k,Z,max (max Nerr Nlarge) (max Nlist Nwidth),hmin,hZ,?_⟩
  intro P hσP hJP hZP hN hi geometry
  have hNerrP : Nerr ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNlargeP : Nlarge ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNlistP : Nlist ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNwidthP : Nwidth ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hpσ : 0 < P.σ := by simpa only [hσP] using hσ
  have hpJ : 0 < P.J := by simpa only [hJP] using hJ
  have hnlist : Classical.choose (eventual_descriptor_list_scale 3 hB hpσ) ≤ P.N := by
    simpa only [hσP] using hNlistP
  have hnwidth : Classical.choose (uniform_graph_parallel_width (m+3) hpσ hpJ) ≤ P.N := by
    simpa only [hσP,hJP] using hNwidthP
  have hlarge := hNlarge P.N hNlargeP
  have hlarge₁ : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*P.σ) := by
    rw [hσP]
    linarith [Real.pi_pos]
  have hlarge₂ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*P.σ) := by
    rw [hσP]
    linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hc₀ : 0 < c₀ := by norm_num [c₀]
  have hcsmall : c₀ ≤ 1/2 := by norm_num [c₀]
  have hCgeo : 1 ≤ Cgeo := by dsimp [Cgeo]; linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hCdim : 4*Real.sqrt (m+3:ℕ) ≤ Cgeo := by dsimp [Cgeo]; linarith
  have hpN : geometry.p ≤ P.N := geometry.pN
  have hscale := policy_graph_scale_data (m+3) P.N_pos hpσ hc₀ hcsmall hCgeo hCdim
    geometry.depth geometry.length geometry.frequency hlarge₁ hlarge₂
  obtain ⟨S,η,hcard,hone,hnonneg,hcontrol⟩ := hcaps
    (policyGraphRadius P.N P.a geometry.p P.σ c₀) hscale.1
    (hscale.2.1.trans (by norm_num))
  let G := P.graphDataAt k B hB hpσ hpJ hi hnlist hnwidth geometry c₀ Cgeo Hcap
    hc₀ hcsmall hCgeo hCdim hHcap hlarge₁ hlarge₂ S η hcontrol hnonneg hone
  have hGN : G.N = P.N := rfl
  have hcap : (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) :=
    policyGraphCap_count hpN hpσ.le hc₀ hcard
  have hratio : 16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) := by
    change 16*policyGraphScale P.N P.a geometry.p P.longest P.σ c₀ Cgeo /
      ((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N geometry.p P.σ) ≤ _
    simpa only [V,hσP,Real.rpow_natCast,hGN,neg_mul] using hscale.2.2.2.2.2.2.2.2
  have htN : G.v ≤ G.N := Nat.cast_le.mpr (P.base_right.trans P.base_N)
  have he := herr hH hC.le hW (show 0 ≤ Cap by dsimp [Cap]; positivity)
    (show 0 ≤ V by dsimp [V]; positivity) G htN hcap hratio
  have he' : G.error H C W (T+1+(11*(m+3):ℕ)) ≤ ((2:ℝ)^P.N)^(-T) := by
    apply he.trans
    change E*((2:ℝ)^P.N)^(-(T+1)) ≤ _
    calc
      _ ≤ ((2:ℝ)^P.N)^1*((2:ℝ)^P.N)^(-(T+1)) :=
        mul_le_mul_of_nonneg_right (hNerr P.N hNerrP) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]; congr 1; ring
  have hfinite := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hW hΨW
    (fun u hu => by
      by_contra hn
      exact (not_lt_of_ge hu.le) (hsupp u hn).2)
  rw [← hσP] at hgraph
  have hg := hgraph G hfinite
  rw [← hZP] at hg
  change P.envelope K k Ψ ≤ P.graphCoefficient geometry.p*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      P.graphChild K k geometry.p Ψ)+G.error H C W (T+1+(11*(m+3):ℕ)) at hg
  exact hg.trans (add_le_add le_rfl he')

end Falconer

end OAI
