import OAI.NumberTheory.TotientAsymptotic.LocalResidualLayers
import OAI.NumberTheory.TotientAsymptotic.LocalNormalityReciprocalMass
import OAI.NumberTheory.TotientAsymptotic.LocalSquareReciprocalMass
import OAI.NumberTheory.TotientAsymptotic.LocalResidualDecay

namespace OAI

/-! The two exceptional witness classes have summable reciprocal mass at
the actual geometric residual scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_nonnormal_residual_mass {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (d q L : ℕ) (hd : 0 < d) :
    ∀ᶠ h : ℕ in atTop,∀ (R Q : Finset ℕ) (F : ℕ → ℕ),Q ⊆ R →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
        c*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ r ∈ R,∀ p : ℕ,p.Prime → p ∣ r → IsNormalPrime (localNormalityScale h) p) →
      (∀ p : ℕ,p.Prime → p ∣ q → IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ R,(∃ s ∈ R,s≠r ∧ s.totient=r.totient) → ∃ s ∈ R,F r=s*q) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p ∣ F r ∧ ¬IsNormalPrime (localNormalityScale h) p) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  obtain ⟨D,hD,hlayers⟩ := local_residual_layer_bounds hc hA L
  let C : ℝ := 12*d/Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [hlayers 256,local_nonnormal_witness_mass_rate hD.le 3,
    local_residual_mass_decay hA.le hC L] with h hdata hmass hdecay
  intro R Q F hQR hvalues hR hq hbranch hbad hF
  let U := localPrimeHeight A L h
  let J := discardExponent U
  have hpoint (r) (hr : r∈Q) :
      1<d*r.totient ∧ d*r.totient≤2^J ∧
      let z := (2:ℝ)^(Nat.clog 2 (d*r.totient))
      max 256 256 ≤ z ∧ (c/2)*(rho^h)⁻¹≤B z ∧ 0≤B z ∧
        Real.log (B z+4)≤D*h ∧ (localSquareCutoff z:ℝ)≤localNormalityScale h := by
    obtain ⟨p,hp,hpv,hgeo,hu⟩ := hvalues r hr
    exact hdata p (d*r.totient) hp hpv hgeo hu
  have hm := hmass d q J hd R Q F hQR
    (fun r hr => ⟨(hpoint r hr).1,by exact_mod_cast (hpoint r hr).2.1⟩)
    (fun r hr => ⟨by simpa only [max_self] using (hpoint r hr).2.2.1,
      (hpoint r hr).2.2.2.2.1,(hpoint r hr).2.2.2.2.2.1⟩)
    hR hq hbranch hbad hF
  have hU := localPrimeHeight_ge_two hA.le L h
  have hJ : 1+Real.log J ≤ 3*U := by
    have hh := (discardExponent_bounds hU).2
    dsimp only [J]
    linarith only [hh,hU]
  calc
    _ ≤ (4*d/Real.log 2)*rho^(3*h)*(1+Real.log J) := hm
    _ ≤ (4*d/Real.log 2)*rho^(3*h)*(3*U) :=
      mul_le_mul_of_nonneg_left hJ
        (mul_nonneg (by positivity) (pow_pos rho_pos _).le)
    _ = C*U*rho^(3*h) := by dsimp [C]; ring
    _ ≤ rho^h := hdecay

theorem local_square_residual_mass {c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (d L : ℕ) (hd : 0 < d) :
    ∀ᶠ h : ℕ in atTop,∀ (Q : Finset ℕ) (F : ℕ → ℕ),Set.InjOn F (Q : Set ℕ) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ p-1 ≤ d*r.totient ∧
        c*(rho^h)⁻¹ ≤ B p ∧ ((d*r.totient:ℕ):ℝ) ≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ r ∈ Q,0<F r ∧ (F r).totient=d*r.totient) →
      (∀ r ∈ Q,∃ p : ℕ,p.Prime ∧ localNormalityScale h<p ∧
        (p^2 ∣ F r ∨ p^2 ∣ (F r).totient)) →
      (∑ r ∈ Q,(r.totient:ℝ)⁻¹) ≤ rho^h := by
  obtain ⟨D,hD,hlayers⟩ := local_residual_layer_bounds hc hA L
  obtain ⟨z₀,hz₀,hmass⟩ := local_square_witness_mass 4
  let K : ℝ := ((c/2)^4)⁻¹
  let C : ℝ := (12*d/Real.log 2)*K
  have hC : 0 ≤ C := by dsimp [C,K]; positivity
  filter_upwards [hlayers z₀,local_residual_mass_decay hA.le hC L]
    with h hdata hdecay
  intro Q F hinj hvalues hF hbad
  let U := localPrimeHeight A L h
  let J := discardExponent U
  let T := (c/2)*(rho^h)⁻¹
  have hT : 0 < T := mul_pos (half_pos hc) (inv_pos.mpr (pow_pos rho_pos h))
  have hpoint (r) (hr : r∈Q) :
      1<d*r.totient ∧ d*r.totient≤2^J ∧
      let z := (2:ℝ)^(Nat.clog 2 (d*r.totient))
      max 256 z₀ ≤ z ∧ (c/2)*(rho^h)⁻¹≤B z ∧ 0≤B z ∧
        Real.log (B z+4)≤D*h ∧ (localSquareCutoff z:ℝ)≤localNormalityScale h := by
    obtain ⟨p,hp,hpv,hgeo,hu⟩ := hvalues r hr
    exact hdata p (d*r.totient) hp hpv hgeo hu
  have hm := hmass d h J T hT Q F hinj
    (fun r hr => ⟨(hpoint r hr).1,by exact_mod_cast (hpoint r hr).2.1⟩)
    (fun r hr => ⟨(le_max_right _ _).trans (hpoint r hr).2.2.1,
      (hpoint r hr).2.2.2.1,(hpoint r hr).2.2.2.2.2.2⟩) hF hbad
  have hU := localPrimeHeight_ge_two hA.le L h
  have hJ : 1+Real.log J ≤ 3*U := by
    have hh := (discardExponent_bounds hU).2
    dsimp only [J]
    linarith only [hh,hU]
  have hpow : T^(-4:ℝ) ≤ K*rho^(3*h) := by
    have hh := local_geometric_inverse_fourth (half_pos hc) (le_refl T)
    apply hh.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le (by omega : 3*h≤4*h))
      (inv_nonneg.mpr (pow_nonneg (half_pos hc).le 4))
  calc
    _ ≤ (4*d/Real.log 2)*T^(-(4:ℝ))*(1+Real.log J) := hm
    _ ≤ (4*d/Real.log 2)*T^(-4:ℝ)*(3*U) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ ≤ (4*d/Real.log 2)*(K*rho^(3*h))*(3*U) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by have hu : 0≤U := by dsimp only [U]; linarith only [hU]
            positivity)
    _ = C*U*rho^(3*h) := by dsimp [C]; ring
    _ ≤ rho^h := hdecay

end TotientAsymptotic

end

end OAI
