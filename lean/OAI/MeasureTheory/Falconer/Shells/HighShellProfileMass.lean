import OAI.MeasureTheory.Falconer.Shells.HighShellFourierError
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem normalized_cellPair_mass (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.levelMass^(-2:ℤ)*d.cellPair.real univ =
      ((d.ρ (d.Q.descendant d.X).carrier).toReal/d.levelMass)*
      ((d.ρ (d.Q.descendant d.Y).carrier).toReal/d.levelMass) := by
  have hp : d.cellPair univ =
      d.ρ (d.Q.descendant d.X).carrier*d.ρ (d.Q.descendant d.Y).carrier := by
    unfold cellPair
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  rw [measureReal_def,hp,ENNReal.toReal_mul]
  simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  ring

theorem normalized_cellPair_profile_mass (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.levelMass^(-2:ℤ)*d.cellPair.real univ ≤ ((2:ℝ)^d.N)^(6*d.lam) := by
  let := hd.probability
  rw [d.normalized_cellPair_mass]
  have h := mul_le_mul (hd.normalized_cell_mass_le ha hX)
    (hd.normalized_cell_mass_le ha hY) (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)] at h
  convert h using 1
  congr 1
  ring_nf

theorem uniform_high_shell_profile_error {sig lam T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ‖charFun d.weightedDistance r-d.normalizedHighShellF n v r‖ ≤ ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_high_shell_fourier_error (T := T+6*lam) hsig
  refine ⟨n,N₀,?_⟩
  intro d B δ hd hN hsig' hlam hQ hs hq hqs hw ht hX hY v r hv hr
  let := hd.probability
  have he := h₀ d hN hsig' hQ hs hq hqs hw ht v r hv hr
  have hm := d.normalized_cellPair_profile_mass hd (by omega) hX hY
  rw [hlam] at hm
  apply he.trans
  apply (mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ ((2:ℝ)^d.N)^(-(T+6*lam)))).trans_eq
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)]
  congr 1
  ring

end PositiveDistanceData

end PlanarFalconer

end OAI
