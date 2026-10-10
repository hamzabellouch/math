import OAI.MeasureTheory.Falconer.Shells.PolicyPositiveBand
import OAI.MeasureTheory.Falconer.Shells.PolicyPrefixShell
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

/-! # The positive prefix branch on actual retained child states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

theorem exists_policy_positive_prefix_recurrence
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
      P.σ*(P.N:ℝ) ≤ P.q →
      2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
          (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
      (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
        ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
        P.directWeight p lam σ ε *
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
      P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  let δ : ℝ := 100*(((m+3:ℕ):ℝ)+1)
  let W : ℝ := 2002*(((m+3:ℕ):ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  obtain ⟨K,L,Z,Nshell,hL,hZ,hshell⟩ := exists_policy_prefix_shell_recurrence
    hgnomonic hquadratic m hlam hσ hσ1 (half_pos hε) hJ (T+ε/2) δ W hδ hW
    φ Ψ hφ hΨ hpos hzero hone hV hΨV hsupp minOrder
  obtain ⟨C,hC,Nband,hband⟩ := exists_policy_positive_band_bound m hσ hJ
  obtain ⟨Ncost,hcost⟩ := PlanarFalconer.fixed_linear_subpower C hC.le (half_pos hε)
  refine ⟨K,L,Z,max Nshell (max Nband Ncost),hL,hZ,?_⟩
  intro P hσP hLam hJP hZP hN hi hleft hright hwide hq hprefix hcover hlo hhi w₀ M hM hfloor hlow hchildren
  let := P.regular.probability
  let R : ℝ := (2:ℝ)^P.N
  let c : ℝ := R^(ε/2)
  have hc : 0 < c := by dsimp [c,R]; positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hsep : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
      (P.ρ.restrict (P.Q.descendant P.Y).carrier),
      δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (P.Q.descendant P.X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
    exact separated_cell_distance_bounds P.Q P.unit P.a P.X P.Y
      P.X_length P.Y_length hlo hhi hx hy
  have hD : 0 ≤ M/c := div_nonneg hM hc.le
  have hlow' : ∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
      (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
        P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M/c := by
    intro v hv hg
    apply (le_div_iff₀ hc).mpr
    have hp : c ≤ R^ε := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
    exact (mul_le_mul_of_nonneg_left hp ENNReal.toReal_nonneg).trans
      (by simpa only [mul_comm] using hlow v hv hg)
  have hhigh' : ∀ v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
      (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)),
        ‖charFun (P.maskedLaw w₀) r‖^2) ≤ M/c+R^(-(T+ε/2)) := by
    intro v hv hg
    let P' := P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)
    have hhigh : (P'.t₀:ℝ) ≤ P'.t+P'.σ*P'.N := by
      change (P.t₀:ℝ) ≤ (v:ℝ)+P.σ*P.N
      rw [hright,hσP]
      linarith
    have hwide' : P'.a+100*P'.q < P'.t₀ := by change P.a+100*P.q < P.t₀; rwa [hright]
    have hprefix' : 2*policyDepth P'.policy P'.N P'.q P'.a P'.t₀ ≤ P'.a+P'.t₀ := by
      change 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀
      rwa [hright]
    let geometry := P'.prefixGeometry (by change 0 < P.σ; rwa [hσP]) hleft hwide' hq hhigh hprefix'
    have hh : ∀ row, ∀ hrow : row ∈
        (P'.Q.descendant P'.X).occupiedPaths P'.ρ (geometry.p-P'.a) ×ˢ
          (P'.Q.descendant P'.Y).occupiedPaths P'.ρ (geometry.p-P'.a),
        P'.directWeight geometry.p lam σ (ε/2)*
          (P'.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M/c := by
      intro row hrow
      apply (le_div_iff₀ hc).mpr
      have hp : geometry.p = policyDepth P.policy P.N P.q P.a P.t := by
        change policyDepth P.policy P.N P.q P.a P.t₀ = _
        rw [hright]
      have hw : c*P'.directWeight geometry.p lam σ (ε/2) = P.directWeight geometry.p lam σ ε := by
        change ((2:ℝ)^P'.N)^(ε/2)*P'.directWeight geometry.p lam σ (ε/2) = _
        rw [P'.directWeight_shift]
        have he : ε/2+ε/2 = ε := by ring
        rw [he]
        rfl
      calc
        _ = (c*P'.directWeight geometry.p lam σ (ε/2))*
            (P'.child geometry.p geometry.ap row hrow).envelope K L Ψ := by ring
        _ ≤ M := by rw [hw]; exact hchildren v hv hg geometry.p hp geometry.ap row hrow
    exact hshell P' hσP hLam hJP hZP ((le_max_left _ _).trans hN) hi hcover hsep hlo
      hleft hwide' hq hhigh hprefix' (M/c) hD hh w₀
  have hF : R^(4*(((m+3:ℕ):ℝ)+1)*P.lam) ≤ M/c := by
    apply (le_div_iff₀ hc).mpr
    calc
      _ = R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε/2) := by
        rw [hLam,← Real.rpow_add hRpos]
      _ ≤ R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) :=
        Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      _ ≤ M := hfloor
  have hb := hband P hσP hJP ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    hleft hright (by omega) hcover hlo hhi w₀ (M/c) (M/c+R^(-(T+ε/2))) hD
    (by positivity) hlow' hhigh'
  have hcost' := hcost P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have herr : c*R^(-(T+ε/2)) = R^(-T) := by
    dsimp [c]
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  calc
    _ ≤ C*(1+2*(P.N:ℝ))*(3*(M/c)+R^(-(T+ε/2))) := by
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      change R^(4*(((m+3:ℕ):ℝ)+1)*P.lam)+M/c+(M/c+R^(-(T+ε/2))) ≤ _
      linarith
    _ ≤ c*(3*(M/c)+R^(-(T+ε/2))) :=
      mul_le_mul_of_nonneg_right hcost' (by positivity)
    _ = 3*M+R^(-T) := by
      rw [mul_add,herr]
      congr 1
      field_simp

end Falconer

end OAI
