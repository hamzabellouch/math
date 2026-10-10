import OAI.MeasureTheory.Falconer.Estimates.OuterRootGain

namespace OAI

/-! # Uniform two-profile angular bound from the actual recursive estimates -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def outerEntryExponent {m : ℕ} (P Q : PolicyJetData m) (c : ℕ) (κ : ℝ) : ℝ :=
  min (PlanarFalconer.height P.policy 0 c) (PlanarFalconer.height Q.policy 0 c)-
    (PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
      PlanarFalconer.potential Q.policy c Q.t (10*sourcePolicyBlock Q.N κ))/2

theorem exists_uniform_outer_angular_bound
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = lam → Q.lam = lam →
      P.σ = σ → Q.σ = σ → P.J = sourceSmoothingLevels σ κ → Q.J = sourceSmoothingLevels σ κ →
      P.q = sourcePolicyBlock P.N κ → Q.q = sourcePolicyBlock Q.N κ →
      P.Z = Z → Q.Z = Z → P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N →
      N₀ ≤ P.N → P.i = 0 → Q.i = 0 →
      P.policy = profileExcess (d := m+3) P.profile P.N →
      Q.policy = profileExcess (d := m+3) Q.profile Q.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Q.masks b,
        dist w c ≤ descriptorMaskRadius Q.N Q.σ b/2) →
      ∀ c : ℕ, 4*c ≤ P.N → c+100*P.q < P.N →
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
      ((2:ℝ)^P.N)^(outerEntryExponent P Q c κ+outerRootLoss m lam σ κ η+
        outerGraphLoss m lam σ+ε)+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨K,Lr,Zr,Nr,hK,hZr,hNr,hroot⟩ := exists_flexible_graph_child
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  have hJ := PlanarFalconer.sourceSmoothingLevels_pos hσ hκ
  have hσsmall : σ ≤ 1/100 := by linarith
  obtain ⟨L,Z,Ng,hL,hZ,hgraph⟩ := exists_outer_policy_graph_step hgnomonic m K
    hσ hσsmall hJ T φ Ψ hφ hΨ hpos hzero hV hΨV hsupp Lr
  let C : ℝ := (Zr/Z)^4*(2*4^(sourceSmoothingLevels σ κ+1))
  let D : ℝ := 2*11^(m+3)*(((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)*C
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed hε D
  obtain ⟨Nq,hNq⟩ := exists_nat_gt (1/κ)
  refine ⟨K,L,Z,max (max Nr Ng) (max Nc Nq),hK,hZ,by omega,?_⟩
  intro P Q hN hLamP hLamQ hσP hσQ hJP hJQ hqP hqQ hZP hZQ haP haQ htP htQ
    hlarge hiP hiQ hprofileP hprofileQ hcoverP hcoverQ c hc hwide hsepP hsepQ f g
  have hNrP : Nr ≤ P.N := by omega
  have hNrQ : Nr ≤ Q.N := by omega
  have hNgP : Ng ≤ P.N := by omega
  have hNcP : Nc ≤ P.N := by omega
  have hNqP : Nq ≤ P.N := by omega
  have hNP : (0:ℝ) < P.N := Nat.cast_pos.mpr P.N_pos
  have hkn : 1 < κ*(P.N:ℝ) := by
    have hh := (div_lt_iff₀ hκ).mp (hNq.trans_le (Nat.cast_le.mpr hNqP))
    linarith
  have hqratioP : (sourcePolicyBlock P.N κ:ℝ)/P.N ≤ 2*κ := by
    have hh : (sourcePolicyBlock P.N κ:ℝ) < κ*P.N+1 := Nat.ceil_lt_add_one (by positivity)
    exact (div_le_iff₀ hNP).mpr (by linarith)
  have hqratioQ : (sourcePolicyBlock Q.N κ:ℝ)/Q.N ≤ 2*κ := by simpa only [← hN] using hqratioP
  have hwP : c+100*P.q < P.t := by simpa only [htP] using hwide
  have hwQ : c+100*Q.q < Q.t := by simpa only [htQ,hqQ,← hN,← hqP] using hwide
  have hbaseP : (P.t₀:ℝ) ≤ P.t+P.σ*P.N := by
    rw [htP,hσP]
    exact (Nat.cast_le.mpr P.base_N).trans (le_add_of_nonneg_right (by positivity))
  have hbaseQ : (Q.t₀:ℝ) ≤ Q.t+Q.σ*Q.N := by
    rw [htQ,hσQ]
    exact (Nat.cast_le.mpr Q.base_N).trans (le_add_of_nonneg_right (by positivity))
  let Pd := P.diagonal P.X P.X_length
  let Qd := Q.diagonal Q.X Q.X_length
  have hbP := hroot K L le_rfl hL Pd hLamP hσP hJP hqP hNrP hiP hprofileP hcoverP hbaseP c
    (by change P.a ≤ c; omega) hwP
  have hbQ := hroot K L le_rfl hL Qd hLamQ hσQ hJQ hqQ hNrQ hiQ hprofileQ hcoverQ hbaseQ c
    (by change Q.a ≤ c; omega) hwQ
  have heP := P.rootExponentAt_nonneg c hσ.le hκ hη.le
    (by simpa only [hLamP] using hlam) hqP hwP hqratioP hprofileP
  have heQ := Q.rootExponentAt_nonneg c hσ.le hκ hη.le
    (by simpa only [hLamQ] using hlam) hqQ hwQ hqratioQ hprofileQ
  have hp : Pd.graphChild K L c Ψ ≤ C*((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η) := by
    change Pd.graphChild K L c Ψ ≤ (Zr/P.Z)^4*P.rootBoundAt c σ κ η at hbP
    rw [hZP] at hbP
    apply hbP.trans
    calc
      _ ≤ (Zr/Z)^4*((2*4^(sourceSmoothingLevels σ κ+1))*((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η)) :=
        mul_le_mul_of_nonneg_left (P.rootBoundAt_le_single_power c σ κ η heP) (by positivity)
      _ = _ := by dsimp [C]; ring
  have hq : Qd.graphChild K L c Ψ ≤ C*((2:ℝ)^Q.N)^(Q.rootExponentAt c σ κ η) := by
    change Qd.graphChild K L c Ψ ≤ (Zr/Q.Z)^4*Q.rootBoundAt c σ κ η at hbQ
    rw [hZQ] at hbQ
    apply hbQ.trans
    calc
      _ ≤ (Zr/Z)^4*((2*4^(sourceSmoothingLevels σ κ+1))*((2:ℝ)^Q.N)^(Q.rootExponentAt c σ κ η)) :=
        mul_le_mul_of_nonneg_left (Q.rootBoundAt_le_single_power c σ κ η heQ) (by positivity)
      _ = _ := by dsimp [C]; ring
  have hp0 : 0 ≤ Pd.graphChild K L c Ψ := childJetStateMaximum_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ
  have hq0 : 0 ≤ Qd.graphChild K L c Ψ := childJetStateMaximum_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ
  have hg := hgraph P Q hN (hLamP.trans hLamQ.symm) hσP hσQ hJP hJQ hZP hZQ
    haP haQ htP htQ hNgP (by rw [hiP,hJP]; exact hJ) (by rw [hiQ,hJQ]; exact hJ)
    c hc hsepP hsepQ f g
  have hgain := outer_coefficient_two_root_gain (K := K) P Q hN (hLamP.trans hLamQ.symm)
    haP haQ hprofileP hprofileQ c σ κ η 0 (outerEntryExponent P Q c κ) C
    (Pd.graphChild K L c Ψ) (Qd.graphChild K L c Ψ) hσP hC hp0 hq0 hp hq (by simp [outerEntryExponent])
  apply hg.trans
  apply add_le_add _ le_rfl
  apply hgain.trans
  simp only [neg_zero,zero_add,hLamP]
  change D*((2:ℝ)^P.N)^(outerEntryExponent P Q c κ+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ) ≤ _
  calc
    _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(outerEntryExponent P Q c κ+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ) :=
      mul_le_mul_of_nonneg_right (hNc P.N hNcP) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
