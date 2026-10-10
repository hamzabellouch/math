import OAI.MeasureTheory.Falconer.Angular.OuterAngularDecay
import OAI.MeasureTheory.Falconer.Estimates.OuterScalarConversion

namespace OAI

/-! # Power decay of the scalar shell for the original two regularized classes -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_regular_outer_shell
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
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ (Z : ℝ) (N₀ : ℕ), 1 ≤ Z ∧ 0 < N₀ ∧
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
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier), δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier),
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
        β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)),
        ‖charFun (P.outerDistance Q c) r‖^2) ≤ ((2:ℝ)^P.N)^(-β/16) := by
  have hσsmall : σ ≤ 1/100 := by linarith
  obtain ⟨Ks,hscalar⟩ := exists_outer_scalar_conversion hgnomonic hquadratic m hσ hσsmall
    (by positivity : 0 < β/8) (β/8) δ W hδ hW Ψ hΨ hpos hzero hone hV hΨV hsupp
  obtain ⟨K,L,Z,Na,hK,hZ,hNa,hangular⟩ := exists_uniform_outer_angular_decay
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    hχ hβ hκsmall hTβ hentrySmall hdecay φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp Ks
  obtain ⟨Ns,hscalar⟩ := hscalar L Z (zero_lt_one.trans_le hZ)
  obtain ⟨Nc,hNc⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < β/16) 2
  refine ⟨Z,max Na (max Ns Nc),hZ,by omega,?_⟩
  intro P Q hN hLamP hLamQ hsP hsQ hσP hσQ hJP hJQ hqP hqQ hZP hZQ
    haP haQ htP htQ hlarge hiP hiQ hprofileP hprofileQ hcoverP hcoverQ hsepP hsepQ hsep hnear
  have hNaP : Na ≤ P.N := by omega
  have hNsP : Ns ≤ P.N := by omega
  have hNcP : Nc ≤ P.N := by omega
  obtain ⟨c,hc,hw,hclo,henergy⟩ := hangular P Q hN hLamP hLamQ hsP hsQ hσP hσQ hJP hJQ hqP hqQ
    hZP hZQ haP haQ htP htQ hNaP hiP hiQ hprofileP hprofileQ hcoverP hcoverQ hsepP hsepQ
  refine ⟨c,hc,hw,hclo,?_⟩
  have hb := hscalar P Q hN hσP hσQ (hJP.trans hJQ.symm) hiP hiQ hZP hZQ
    haP haQ htP htQ hNsP c (by omega) (fun b _ => hsepP b) (fun b _ => hsepQ b)
    hsep hnear (((2:ℝ)^P.N)^(-β/4)) (by positivity) (by
      intro f g
      exact henergy (f.relax hK le_rfl (by norm_num) le_rfl)
        (g.relax hK le_rfl (by norm_num) le_rfl))
  calc
    _ ≤ ((2:ℝ)^P.N)^(β/8)*((2:ℝ)^P.N)^(-β/4)+((2:ℝ)^P.N)^(-(β/8)) := hb
    _ = 2*((2:ℝ)^P.N)^(-β/8) := by
      rw [← Real.rpow_add (by positivity),show β/8+-β/4 = -β/8 by ring]
      ring_nf
    _ ≤ ((2:ℝ)^P.N)^(β/16)*((2:ℝ)^P.N)^(-β/8) :=
      mul_le_mul_of_nonneg_right (hNc P.N hNcP) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer

end OAI
