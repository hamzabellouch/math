import OAI.MeasureTheory.Falconer.Estimates.PolicyScalarConversion
import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphAtRecurrence

namespace OAI

/-! # The actual high-prefix shell reduces to retained-mask child states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem directWeight_shift (P : PolicyJetData m) (p : ℕ) (lam σ ε δ : ℝ) :
    ((2:ℝ)^P.N)^δ*P.directWeight p lam σ ε = P.directWeight p lam σ (ε+δ) := by
  unfold directWeight
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
  congr 1
  ring

end PolicyJetData

theorem exists_policy_prefix_shell_recurrence
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ (P : PolicyJetData m) (hσP : P.σ = σ), P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (hleft : P.a₀ = P.a) (hwide : P.a+100*P.q < P.t₀)
        (hq : P.σ*(P.N:ℝ) ≤ P.q) (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N),
      ∀ hprefix : 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀,
      let geometry := P.prefixGeometry (by simpa only [hσP] using hσ)
        hleft hwide hq hhigh hprefix
      ∀ M : ℝ, 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
        P.directWeight geometry.p lam σ ε *
          (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M) →
      ∀ w₀ : Sphere (m+3),
      (2:ℝ)^(-(P.a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
          ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
            P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
      M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨K,_hminJet,hconversion⟩ := exists_policy_scalar_conversion hgnomonic hquadratic m hσ hσ1
    (half_pos hε) lam (T+1) δ W hδ hW Ψ hΨ hpos hzero hone hV hΨV hsupp
  obtain ⟨L,Z,Ng,hL,hZ,hgraph⟩ := exists_policy_graph_recurrence_at hgnomonic m K hlam hσ
    (half_pos hε) hJ (T+1+ε/2) φ Ψ hφ hΨ hpos hzero hV hΨV hsupp minOrder
  obtain ⟨Nc,hconvert⟩ := hconversion L Z (zero_lt_one.trans_le hZ)
  refine ⟨K,L,Z,max 1 (max Ng Nc),hL,hZ,?_⟩
  intro P hσP hLam hJP hZP hN hi hcover hsep hcenter hleft hwide hq hhigh hprefix
  let geometry := P.prefixGeometry (by simpa only [hσP] using hσ) hleft hwide hq hhigh hprefix
  dsimp only
  intro M hM hchildren w₀
  let c : ℝ := ((2:ℝ)^P.N)^(ε/2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hinverse := policy_prefix_inverse_scales P (by simpa only [hσP] using hσ)
    hleft hwide hq hhigh
  have hs := hconvert P hσP hLam hZP
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    hcover hsep hcenter hinverse.1 hinverse.2 w₀
  have hchild : ∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
      P.directWeight geometry.p lam σ (ε/2)*
        (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M/c := by
    intro row hrow
    apply (le_div_iff₀ hc).mpr
    have he : c*P.directWeight geometry.p lam σ (ε/2) = P.directWeight geometry.p lam σ ε := by
      dsimp [c]
      rw [P.directWeight_shift]
      congr 1
      ring
    calc
      _ = (c*P.directWeight geometry.p lam σ (ε/2))*
          (P.child geometry.p geometry.ap row hrow).envelope K L Ψ := by ring
      _ ≤ M := by rw [he]; exact hchildren row hrow
  have hg := hgraph P hLam hσP hJP hZP
    ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) hi geometry
    (M/c) (div_nonneg hM hc.le) hchild
  have hbase : 2 ≤ (2:ℝ)^P.N := le_self_pow₀ (by norm_num) (by
    have hh : 1 ≤ P.N := (le_max_left _ _).trans hN
    omega)
  have herr : c*((2:ℝ)^P.N)^(-(T+1+ε/2))+((2:ℝ)^P.N)^(-(T+1)) ≤
      ((2:ℝ)^P.N)^(-T) := by
    have hpower : c*((2:ℝ)^P.N)^(-(T+1+ε/2)) = ((2:ℝ)^P.N)^(-(T+1)) := by
      dsimp [c]
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    rw [hpower]
    have heq : ((2:ℝ)^P.N)^(-T) = (2:ℝ)^P.N*((2:ℝ)^P.N)^(-(T+1)) := by
      symm
      calc
        _ = (((2:ℝ)^P.N)^1)*((2:ℝ)^P.N)^(-(T+1)) := by rw [Real.rpow_one]
        _ = ((2:ℝ)^P.N)^(1+(-(T+1))) := (Real.rpow_add (by positivity) _ _).symm
        _ = _ := by congr 1; ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hbase
      (show 0 ≤ ((2:ℝ)^P.N)^(-(T+1)) by positivity)]
  calc
    _ ≤ c*P.envelope K L Ψ+((2:ℝ)^P.N)^(-(T+1)) := hs
    _ ≤ c*(M/c+((2:ℝ)^P.N)^(-(T+1+ε/2)))+((2:ℝ)^P.N)^(-(T+1)) := by gcongr
    _ = M+(c*((2:ℝ)^P.N)^(-(T+1+ε/2))+((2:ℝ)^P.N)^(-(T+1))) := by
      rw [mul_add,mul_div_cancel₀ _ hc.ne']
      ring
    _ ≤ _ := add_le_add le_rfl herr

end Falconer

end OAI
