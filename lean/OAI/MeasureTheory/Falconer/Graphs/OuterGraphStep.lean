import OAI.MeasureTheory.Falconer.Graphs.OuterGraphData
import OAI.MeasureTheory.Falconer.Graphs.TwoGraphScales
import OAI.MeasureTheory.Falconer.Estimates.TwoPolicyEnergy

namespace OAI

/-! # The actual two-profile graph step at the common entry depth -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

namespace PolicyJetData
variable {m : ℕ}

noncomputable def outerCoefficient (P Q : PolicyJetData m) (c : ℕ) : ℝ :=
  2*11^(m+3)*((2:ℝ)^P.N)^(
    -(profileExcess (d := m+3) P.profile P.N c-profileExcess (d := m+3) P.profile P.N P.a)-
    (profileExcess (d := m+3) Q.profile Q.N c-profileExcess (d := m+3) Q.profile Q.N Q.a)+
    min (PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a c)
      (PlanarFalconer.height (profileExcess (d := m+3) Q.profile Q.N) Q.a c)+
    (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*P.σ+4*(((m+3:ℕ):ℝ)+1)*P.lam)

end PolicyJetData

theorem exists_outer_policy_graph_step
    (hpublished : PublishedGnomonicSurface) (m K : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1/100)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ := 0) :
    ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = Q.lam →
      P.σ = σ → Q.σ = σ → P.J = J → Q.J = J → P.Z = Z → Q.Z = Z →
      P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N →
      N₀ ≤ P.N → P.i+1 ≤ P.J → Q.i+1 ≤ Q.J →
      ∀ c : ℕ, 4*c ≤ P.N →
      (∀ b ∈ P.outerList c, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b ∈ Q.outerList c, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      ∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
        (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
      independentAngularEnergy P.a P.t Ψ
        (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
          (profileModelMass P.profile P.N P.a)
          (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
        (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
          (profileModelMass Q.profile Q.N Q.a)
          (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤
      P.outerCoefficient Q c*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          Real.sqrt ((P.diagonal P.X P.X_length).graphChild K L c Ψ*
            (Q.diagonal Q.X Q.X_length).graphChild K L c Ψ)) + ((2:ℝ)^P.N)^(-T) := by
  obtain ⟨k,hmin,herr⟩ := exists_two_graph_error_order m hσ (T+1) minOrder
  obtain ⟨B,Z,A,C,hB,hZ,hA,hC,hgraph⟩ := exists_two_profile_graph_step hpublished
    (m+1) K k (by omega) φ Ψ hφ hΨ hpos hzero hW hΨW hsupp
    (by positivity : 0 < 20*σ) (T+1+(11*(m+3):ℕ))
  obtain ⟨Hcap,hHcap,hcaps⟩ := exists_controlled_cap_partition (m+1) k
  let c₀ : ℝ := 1/4
  let Cgeo : ℝ := 1+4*Real.sqrt (m+3:ℕ)
  let Cap : ℝ := (4*c₀⁻¹+5)^(m+3)
  let V : ℝ := 16*Cgeo*(4+c₀⁻¹)
  let E : ℝ := Cap^2*((A*(4^k*Hcap)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
    C*((sphereMeasure (m+3)).real univ)^2)
  obtain ⟨Nerr,hNerr⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) E
  obtain ⟨Nlarge,hNlarge⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 20*σ) (40*Real.sqrt (m+3:ℕ)+4*Real.pi)
  let Nlist := Classical.choose (eventual_descriptor_list_scale 4 hB hσ)
  let Nwidth := Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ)
  refine ⟨k,Z,max (max Nerr Nlarge) (max Nlist Nwidth),hmin,hZ,?_⟩
  intro P Q hNsame hLsame hσP hσQ hJP hJQ hZP hZQ haP haQ htP htQ hN hiP hiQ c hc hsepP hsepQ f g
  have hlarge := hNlarge P.N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hlarge₁ : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*σ) := by linarith [Real.pi_pos]
  have hlarge₂ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*σ) := by linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hpσ : 0 < P.σ := by simpa only [hσP] using hσ
  have hqσ : 0 < Q.σ := by simpa only [hσQ] using hσ
  have hpJ : 0 < P.J := by simpa only [hJP] using hJ
  have hqJ : 0 < Q.J := by simpa only [hJQ] using hJ
  have hlistP : Classical.choose (eventual_descriptor_list_scale 4 hB hpσ) ≤ P.N := by
    simpa only [hσP] using (le_max_left Nlist Nwidth).trans ((le_max_right _ _).trans hN)
  have hlistQ : Classical.choose (eventual_descriptor_list_scale 4 hB hqσ) ≤ Q.N := by
    simpa only [hσQ,← hNsame] using (le_max_left Nlist Nwidth).trans ((le_max_right _ _).trans hN)
  have hwidthP : Classical.choose (uniform_graph_parallel_width (m+3) hpσ hpJ) ≤ P.N := by
    simpa only [hσP,hJP] using (le_max_right Nlist Nwidth).trans ((le_max_right _ _).trans hN)
  have hwidthQ : Classical.choose (uniform_graph_parallel_width (m+3) hqσ hqJ) ≤ Q.N := by
    simpa only [hσQ,hJQ,← hNsame] using (le_max_right Nlist Nwidth).trans ((le_max_right _ _).trans hN)
  have hc₀ : 0 < c₀ := by norm_num [c₀]
  have hcsmall : c₀ ≤ 1/2 := by norm_num [c₀]
  have hCgeo : 1 ≤ Cgeo := by dsimp [Cgeo]; linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hCdim : 4*Real.sqrt (m+3:ℕ) ≤ Cgeo := by dsimp [Cgeo]; linarith
  have hscaleP := policy_graph_scale_data (m+3) P.N_pos hpσ hc₀ hcsmall hCgeo hCdim
    (P.outer_geometry haP htP hc hpσ.le (by simpa only [hσP] using hσsmall)).1
    (P.outer_geometry haP htP hc hpσ.le (by simpa only [hσP] using hσsmall)).2.1
    (P.outer_geometry haP htP hc hpσ.le (by simpa only [hσP] using hσsmall)).2.2
    (by simpa only [hσP] using hlarge₁) (by simpa only [hσP] using hlarge₂)
  have hcQ : 4*c ≤ Q.N := by simpa only [← hNsame] using hc
  have hscaleQ := policy_graph_scale_data (m+3) Q.N_pos hqσ hc₀ hcsmall hCgeo hCdim
    (Q.outer_geometry haQ htQ hcQ hqσ.le (by simpa only [hσQ] using hσsmall)).1
    (Q.outer_geometry haQ htQ hcQ hqσ.le (by simpa only [hσQ] using hσsmall)).2.1
    (Q.outer_geometry haQ htQ hcQ hqσ.le (by simpa only [hσQ] using hσsmall)).2.2
    (by simpa only [hσQ,← hNsame] using hlarge₁) (by simpa only [hσQ,← hNsame] using hlarge₂)
  obtain ⟨S,η,hcard,hone,hnonneg,hcontrol⟩ := hcaps
    (policyGraphRadius P.N P.a c P.σ c₀) hscaleP.1 (hscaleP.2.1.trans (by norm_num))
  have hcontrolQ : ∀ w ∈ S, ChartCapControl k (η w) (w : Space (m+3))
      (policyGraphRadius Q.N Q.a c Q.σ c₀) Hcap := by
    simpa only [← hNsame,haP,haQ,hσP,hσQ] using hcontrol
  let G₀ := P.outerGraphData σ hσP k B hB hpσ hpJ hiP hlistP hwidthP c haP htP hc
    (by simpa only [hσP] using hσsmall) hsepP c₀ Cgeo Hcap hc₀ hcsmall hCgeo hCdim hHcap
    (by simpa only [hσP] using hlarge₁) (by simpa only [hσP] using hlarge₂) S η hcontrol hnonneg hone
  let H₀ := Q.outerGraphData σ hσQ k B hB hqσ hqJ hiQ hlistQ hwidthQ c haQ htQ hcQ
    (by simpa only [hσQ] using hσsmall) hsepQ c₀ Cgeo Hcap hc₀ hcsmall hCgeo hCdim hHcap
    (by simpa only [hσQ,← hNsame] using hlarge₁) (by simpa only [hσQ,← hNsame] using hlarge₂)
    S η hcontrolQ hnonneg hone
  let D := max G₀.Dgraph H₀.Dgraph
  let G := G₀.withGraphScale D (le_max_left _ _)
  let H := H₀.withGraphScale D (le_max_right _ _)
  have hsame : JetGraphAlignment G H := {
    N := hNsame.symm, a := haQ.trans haP.symm, p := rfl, lam := hLsame.symm,
    σ := hσQ.trans hσP.symm, v := congrArg (fun n : ℕ => (n:ℝ)) (htQ.trans (hNsame.symm.trans htP.symm)),
    τ := by change policyGraphWidth Q.N c Q.σ = policyGraphWidth P.N c P.σ; rw [hNsame,hσP,hσQ]
    δ := by change policyGraphRadius Q.N Q.a c Q.σ c₀ = policyGraphRadius P.N P.a c P.σ c₀
            rw [hNsame,haP,haQ,hσP,hσQ]
    Dgraph := rfl }
  have hcap : (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) :=
    policyGraphCap_count (by omega : c ≤ P.N) hpσ.le hc₀ hcard
  have hratioP : 16*G₀.Dgraph/((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N c P.σ) ≤
      V*((2:ℝ)^P.N)^(-(26*σ)) := by
    change 16*policyGraphScale P.N P.a c (P.outerLongest c) P.σ c₀ Cgeo /
      ((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N c P.σ) ≤ _
    simpa only [V,hσP,Real.rpow_natCast,neg_mul] using hscaleP.2.2.2.2.2.2.2.2
  have hratioQ : 16*H₀.Dgraph/((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N c P.σ) ≤
      V*((2:ℝ)^P.N)^(-(26*σ)) := by
    change 16*policyGraphScale Q.N Q.a c (Q.outerLongest c) Q.σ c₀ Cgeo /
      ((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N c P.σ) ≤ _
    simpa only [V,hσP,hσQ,htQ,htP,← hNsame,Real.rpow_natCast,neg_mul] using hscaleQ.2.2.2.2.2.2.2.2
  have hratio : 16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) := by
    change 16*max G₀.Dgraph H₀.Dgraph/((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N c P.σ) ≤ _
    rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 16)]
    apply (div_le_iff₀ (by unfold policyGraphWidth; positivity)).mpr
    exact max_le ((div_le_iff₀ (by unfold policyGraphWidth; positivity)).mp hratioP)
      ((div_le_iff₀ (by unfold policyGraphWidth; positivity)).mp hratioQ)
  have he := herr hA hC.le hW (show 0 ≤ Cap by dsimp [Cap]; positivity)
    (show 0 ≤ V by dsimp [V]; positivity) G H hsame (by change (P.t:ℝ) ≤ P.N; rw [htP]) hcap hratio
  have he' : G.twoProfileError H A C W (T+1+(11*(m+3):ℕ)) ≤ ((2:ℝ)^P.N)^(-T) := by
    apply he.trans
    change E*((2:ℝ)^P.N)^(-(T+1)) ≤ _
    calc
      _ ≤ ((2:ℝ)^P.N)^1*((2:ℝ)^P.N)^(-(T+1)) :=
        mul_le_mul_of_nonneg_right (hNerr P.N ((le_max_left _ _).trans ((le_max_left _ _).trans hN))) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]; congr 1; ring
  have hfinite := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hW hΨW
    (fun u hu => by by_contra hn; exact (not_lt_of_ge hu.le) (hsupp u hn).2)
  have hg := hgraph G H hsame hfinite f g
  have hchildrenP : G.selfChildMaximum K Z Ψ = (P.diagonal P.X P.X_length).graphChild K k c Ψ := by
    change childJetStateMaximum (m+1) K k 1
      ((P.outerList c).filter (fun b => c < PlanarFalconer.descriptorAnchor b))
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks Z
      P.X P.X (c-P.a) (profileModelMass P.profile P.N c) c P.t Ψ = _
    change _ = childJetStateMaximum (m+1) K k 1
      (P.list.filter (fun b => c < PlanarFalconer.descriptorAnchor b))
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z
      P.X P.X (c-P.a) (profileModelMass P.profile P.N c) c P.t Ψ
    rw [P.outerList_drop (by omega)]
    rw [show P.list.filter (fun b => c < PlanarFalconer.descriptorAnchor b) =
      PlanarFalconer.remainingPolicyDescriptors P.policy P.N P.q P.a₀ P.t₀ c from
        PlanarFalconer.remainingPolicyDescriptors_drop P.policy P.N P.q P.a₀ P.t₀ (by omega),hZP]
  have hchildrenQ : H.selfChildMaximum K Z Ψ = (Q.diagonal Q.X Q.X_length).graphChild K k c Ψ := by
    change childJetStateMaximum (m+1) K k 1
      ((Q.outerList c).filter (fun b => c < PlanarFalconer.descriptorAnchor b))
      Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Z
      Q.X Q.X (c-Q.a) (profileModelMass Q.profile Q.N c) c Q.t Ψ = _
    change _ = childJetStateMaximum (m+1) K k 1
      (Q.list.filter (fun b => c < PlanarFalconer.descriptorAnchor b))
      Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z
      Q.X Q.X (c-Q.a) (profileModelMass Q.profile Q.N c) c Q.t Ψ
    rw [Q.outerList_drop (by omega)]
    rw [show Q.list.filter (fun b => c < PlanarFalconer.descriptorAnchor b) =
      PlanarFalconer.remainingPolicyDescriptors Q.policy Q.N Q.q Q.a₀ Q.t₀ c from
        PlanarFalconer.remainingPolicyDescriptors_drop Q.policy Q.N Q.q Q.a₀ Q.t₀ (by omega),hZQ]
  rw [hchildrenP,hchildrenQ] at hg
  apply (le_trans ?_ (add_le_add le_rfl he'))
  convert hg using 1 <;> first | rfl | simp only [hZP,hZQ,G,H,G₀,H₀,
    JetStateGraphData.withGraphScale,PolicyJetData.outerGraphData,JetStateGraphData.symbol]

end Falconer

end OAI
