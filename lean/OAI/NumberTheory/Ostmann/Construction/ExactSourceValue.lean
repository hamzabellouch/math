import OAI.NumberTheory.Ostmann.Construction.ActualTests
import OAI.NumberTheory.Ostmann.Construction.BroadBandBalance

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def exactSourceValue (d : Decomposition) (p : ℕ) : ℝ :=
  (1-Supply.residueDensityTotal d p)/
    Real.sqrt (Supply.residueDensityTotal d p*(1-Supply.residueDensityTotal d p))

theorem exactSourceValue_pos (d : Decomposition) {p : ℕ} (hp : p.Prime) :
    0<exactSourceValue d p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  unfold exactSourceValue
  rw [Supply.residueDensityTotal_eq]
  have hlo : 0<Supply.density (d.residueSupport p) := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_pos p hp
  have hhi : Supply.density (d.residueSupport p)<1 := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_lt_one p hp
  exact div_pos (sub_pos.mpr hhi) (Real.sqrt_pos.mpr (mul_pos hlo (sub_pos.mpr hhi)))

theorem exactSourceValue_balanced_lower (d : Decomposition) {p : ℕ}
    (_hp : p.Prime) (hbal : Supply.balancedDensity d p) :
    (1/2:ℝ) ≤ exactSourceValue d p := by
  obtain ⟨hlo,hhi⟩ := hbal
  let σ := Supply.residueDensityTotal d p
  have hs0 : 0<σ := by dsimp [σ]; linarith
  have hs1 : σ<1 := by dsimp [σ]; linarith
  have hvar : 0<σ*(1-σ) := mul_pos hs0 (sub_pos.mpr hs1)
  have hsqrt := Real.sq_sqrt hvar.le
  have hsqrtn := Real.sqrt_nonneg (σ*(1-σ))
  have hsbound : Real.sqrt (σ*(1-σ)) ≤ 2*(1-σ) := by
    have hσ : σ≤(2/3:ℝ) := hhi
    nlinarith
  change (1/2:ℝ) ≤ (1-σ)/Real.sqrt (σ*(1-σ))
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hvar)).mpr
  linarith

theorem exactSourceValue_indicator_lower (d : Decomposition) {p : ℕ} (hp : p.Prime) :
    (1/2:ℝ)*balancedPrimeIndicator d p ≤ exactSourceValue d p := by
  classical
  unfold balancedPrimeIndicator
  split_ifs with h
  · simpa only [mul_one] using exactSourceValue_balanced_lower d hp h
  · simpa only [mul_zero] using (exactSourceValue_pos d hp).le

theorem residueTest_on_summand (d : Decomposition) {p a : ℕ} (hp : p.Prime)
    (ha : a∈d.A) (hlarge : p+d.cutoff<a) :
    residueTest d p (a:ZMod p)=(exactSourceValue d p:ℂ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hmem := (d.mem_residueSupport p (a:ZMod p)).mpr ⟨a,ha,hlarge,rfl⟩
  rw [residueTest_eq]
  unfold Supply.normalizedIndicator Supply.centeredIndicator exactSourceValue
  rw [ite_eq_left hmem,Supply.residueDensityTotal_eq]

end Ostmann.Construction

end

end OAI
