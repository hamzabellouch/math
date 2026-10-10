import OAI.MeasureTheory.Falconer.Recursion.OuterEntryGain

namespace OAI

/-! # Power decay at a proved common entry depth of the original profiles -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_uniform_outer_angular_decay
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    {χ β : ℝ} (hχ : 0 < χ) (hβ : 0 < β)
    (hκsmall : κ ≤ 1/1000) (hTβ : β/2 ≤ T)
    (hentrySmall : β+((m+3:ℕ)+4)*lam < χ/4)
    (hdecay : ((m+3:ℕ)+4)*lam+outerRootLoss m lam σ κ η+outerGraphLoss m lam σ ≤ β/8)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.lam = lam → Q.lam = lam →
      P.s = (m+3:ℕ)/2+χ → Q.s = (m+3:ℕ)/2+χ →
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
      (∀ b, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
        β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      ∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
        (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
      independentAngularEnergy P.a P.t Ψ
        (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
          (profileModelMass P.profile P.N P.a)
          (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
        (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
          (profileModelMass Q.profile Q.N Q.a)
          (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤
      ((2:ℝ)^P.N)^(-β/4) := by
  obtain ⟨K,L,Z,Nb,hK,hZ,hNb,hbound⟩ := exists_uniform_outer_angular_bound
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet (by positivity : 0 < β/8)
  obtain ⟨Nmass,hNmass⟩ := exists_nat_gt (8*((m+3:ℕ):ℝ)/β)
  obtain ⟨Nq,hNq⟩ := exists_nat_gt (1/κ)
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < β/4) 2
  refine ⟨K,L,Z,max (max Nb Nmass) (max Nq Nc),hK,hZ,by omega,?_⟩
  intro P Q hN hLamP hLamQ hsP hsQ hσP hσQ hJP hJQ hqP hqQ hZP hZQ
    haP haQ htP htQ hlarge hiP hiQ hprofileP hprofileQ hcoverP hcoverQ hsepP hsepQ
  have hNbP : Nb ≤ P.N := by omega
  have hNmP : Nmass ≤ P.N := by omega
  have hNqP : Nq ≤ P.N := by omega
  have hNcP : Nc ≤ P.N := by omega
  have hNP : (0:ℝ) < P.N := Nat.cast_pos.mpr P.N_pos
  have hmass : 8*((m+3:ℕ):ℝ) < β*P.N := by
    simpa only [mul_comm] using (div_lt_iff₀ hβ).mp (hNmass.trans_le (Nat.cast_le.mpr hNmP))
  have hmass' : 2*((m+3:ℕ):ℝ)/P.N ≤ β/4 :=
    (div_le_iff₀ hNP).mpr (by linarith)
  have hkn : 1 < κ*(P.N:ℝ) := by
    have hh := (div_lt_iff₀ hκ).mp (hNq.trans_le (Nat.cast_le.mpr hNqP))
    linarith
  have hqr : (P.q:ℝ) ≤ 2*κ*P.N := by
    rw [hqP]
    have hh : (sourcePolicyBlock P.N κ:ℝ) < κ*P.N+1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hsmallq : 400*P.q ≤ P.N := by
    have hh : 400*(P.q:ℝ) ≤ P.N := by
      have hk := mul_le_mul_of_nonneg_right hκsmall hNP.le
      linarith
    exact_mod_cast hh
  obtain ⟨c,hc,hwide,hclo,htailP,htailQ,hentry⟩ := exists_policy_profile_entry P Q
    hχ hβ hlam hentrySmall hN hLamP hLamQ hsP hsQ htP htQ hprofileP hprofileQ hqP
    (by linarith : 2*((m+3:ℕ):ℝ) ≤ β*P.N) hsmallq
  refine ⟨c,hc,hwide,hclo,?_⟩
  intro f g
  have hb := hbound P Q hN hLamP hLamQ hσP hσQ hJP hJQ hqP hqQ hZP hZQ
    haP haQ htP htQ hNbP hiP hiQ hprofileP hprofileQ hcoverP hcoverQ
    c hc hwide (fun b _ => hsepP b) (fun b _ => hsepQ b) f g
  have hexp : outerEntryExponent P Q c κ+outerRootLoss m lam σ κ η+
      outerGraphLoss m lam σ+β/8 ≤ -β/2 := by linarith
  have hR : 1 ≤ (2:ℝ)^P.N := one_le_pow₀ (by norm_num)
  calc
    _ ≤ ((2:ℝ)^P.N)^(outerEntryExponent P Q c κ+outerRootLoss m lam σ κ η+
        outerGraphLoss m lam σ+β/8)+((2:ℝ)^P.N)^(-T) := hb
    _ ≤ ((2:ℝ)^P.N)^(-β/2)+((2:ℝ)^P.N)^(-β/2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hR hexp)
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith))
    _ = 2*((2:ℝ)^P.N)^(-β/2) := by ring
    _ ≤ ((2:ℝ)^P.N)^(β/4)*((2:ℝ)^P.N)^(-β/2) :=
      mul_le_mul_of_nonneg_right (hNc P.N hNcP) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
