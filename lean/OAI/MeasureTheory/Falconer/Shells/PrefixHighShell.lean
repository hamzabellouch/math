import OAI.MeasureTheory.Falconer.Recursion.PrefixInverseSupremum
import OAI.MeasureTheory.Falconer.Shells.ActualHighShellEquation21

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem prefix_shell_power_absorption {R eta E T C H : ℝ}
    (hR : 2 ≤ R) (heta : 0 < eta) (hC : C ≤ R^eta) (hH : 0 ≤ H) :
    R^eta*(C*R^(E+eta)*H+R^(-(T+eta+1)))+R^(-(T+eta+1)) ≤
      R^(E+3*eta)*H+R^(-T) := by
  have hRp : 0 < R := by linarith
  have hp : 1 ≤ R^eta := Real.one_le_rpow (by linarith) heta.le
  have herr : R^eta*R^(-(T+eta+1))+R^(-(T+eta+1)) ≤ R^(-T) := by
    have hsmall : R^(-(T+eta+1)) ≤ R^eta*R^(-(T+eta+1)) := by nlinarith [Real.rpow_pos_of_pos hRp (-(T+eta+1))]
    have he : R^eta*R^(-(T+eta+1)) = R^(-T)/R := by
      rw [← Real.rpow_add hRp]
      rw [show eta+ -(T+eta+1) = -T-1 by ring,Real.rpow_sub hRp,Real.rpow_one]
    rw [he] at hsmall ⊢
    have hdiv : 2*(R^(-T)/R) ≤ R^(-T) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hRp).mpr
      nlinarith [Real.rpow_pos_of_pos hRp (-T)]
    linarith
  calc
    _ ≤ R^eta*(R^eta*R^(E+eta)*H+R^(-(T+eta+1)))+R^(-(T+eta+1)) := by gcongr
    _ = R^(E+3*eta)*H+(R^eta*R^(-(T+eta+1))+R^(-(T+eta+1))) := by
      have he : R^eta*(R^eta*R^(E+eta)) = R^(E+3*eta) := by
        rw [← mul_assoc,← Real.rpow_add hRp,← Real.rpow_add hRp]
        congr 1
        ring
      nlinarith [he]
    _ ≤ _ := add_le_add (le_refl _) herr

namespace PositiveDistanceData

theorem uniform_prefix_high_shell {sig kap lam T eps : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-sig*d.N < (v:ℝ) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)), ‖charFun d.weightedDistance r‖^2) ≤
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T) := by
  let eta := eps/3
  have heta : 0 < eta := by dsimp [eta]; positivity
  let U := T+eta+1
  obtain ⟨n,N₁,h₁⟩ := uniform_high_shell_equation21 (lam := lam) (T := U) hsig heta
  obtain ⟨N₂,h₂⟩ := uniform_prefix_inverse_supremum hsig hgap hlam
    (show 0 ≤ U by dsimp [U]; linarith) heta n hJ hΨ hpos hs
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed heta ((symbolDerivativeConstant (2*n)^(2*n))^4)
  refine ⟨2*n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref v hv hvhigh
  have hN1 : N₁ ≤ d.N := by omega
  have hN2 : N₂ ≤ d.N := by omega
  have hN3 : N₃ ≤ d.N := by omega
  let := hprof.probability
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have hsep' := d.stronglySeparated_of_unit hQ hX hY hlo hsep
  have hqs : d.sig*d.N ≤ (d.q:ℝ) := by
    rw [hdSig]
    exact (mul_le_mul_of_nonneg_right (by linarith : sig ≤ kap) (Nat.cast_nonneg _)).trans hblock
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hvt : (v:ℝ) ≤ d.t := by exact_mod_cast (Finset.mem_Ioc.mp hv).2
  have hlow := h₁ d B δ hprof hN1 hdSig hdLam hQpos hsep' hq hqs hw ht hX hY
    v (by simpa only [hdSig] using hvhigh.le) hvt Ψ hΨ.continuous.measurable hpos hs W hW
    (fun x => (le_abs_self _).trans (hWb x)) hone
  have hhigh := h₂ d hdSig hdLam hdJ hN2 hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep hpref v hv hvhigh
  have hsup0 := (d.prefixSuccessorSupremum_majorizes hQpos (2*n) p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  have hR : 2 ≤ (2:ℝ)^d.N := by
    calc
      (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have habs := prefix_shell_power_absorption
    (E := -2*(A p-A d.a)+height A d.a p+4000*(lam+sig)) (T := T)
    hR heta (h₃ d.N hN3) hsup0
  have h := hlow.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hhigh (by positivity : 0 ≤ ((2:ℝ)^d.N)^eta)) (le_refl _)).trans habs)
  simpa only [show 3*eta = eps by dsimp [eta]; ring] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
