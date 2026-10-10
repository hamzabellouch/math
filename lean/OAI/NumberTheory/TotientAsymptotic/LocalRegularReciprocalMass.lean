import OAI.NumberTheory.TotientAsymptotic.LocalExceptionalResidualMass

namespace OAI

/-! Integrate an actual regular-residual counting estimate over its occupied
layers. Only the fourth inverse power of the local double logarithm is needed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem residual_fourth_power_mass (d J : ℕ) {T : ℝ} (hT : 0<T)
    (Q : Finset ℕ)
    (hrange : ∀ r∈Q,1<d*r.totient ∧ ((d*r.totient:ℕ):ℝ)≤(2:ℝ)^J)
    (hlower : ∀ r∈Q,T≤B ((2:ℝ)^(Nat.clog 2 (d*r.totient))))
    (hcount : ∀ k∈Finset.Icc 1 J,
      (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty →
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (2:ℝ)^k/Real.log ((2:ℝ)^k)*(B ((2:ℝ)^k))^(-4:ℝ)) :
    (∑ r∈Q,(r.totient:ℝ)⁻¹) ≤
      (4*d/Real.log 2)*T^(-4:ℝ)*(1+Real.log J) := by
  classical
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0≤T^(-4:ℝ)/Real.log 2 := by positivity
  have hc (k : ℕ) (hk : k∈Finset.Icc 1 J) :
      ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
        (T^(-4:ℝ)/Real.log 2)*(2:ℝ)^k/k := by
    by_cases hQ : (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty
    · obtain ⟨r,hr⟩ := hQ
      obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
      have hlo := hlower r hr
      rw [he] at hlo
      have hpow := Real.rpow_le_rpow_of_nonpos hT hlo (by norm_num : (-4:ℝ)≤0)
      have hkpos : (0:ℝ)<k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hfac : 0≤(2:ℝ)^k/Real.log ((2:ℝ)^k) := by
        rw [dyadic_endpoint_log]
        positivity
      apply ((hcount k hk ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩).trans
        (mul_le_mul_of_nonneg_left hpow hfac)).trans_eq
      rw [dyadic_endpoint_log]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  apply (residual_dyadic_mass Q d J hcoef hrange hc).trans_eq
  ring

theorem local_residual_mass_of_fourth_power_count {c A : ℝ}
    (hc : 0<c) (hA : 0<A) (d L : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ Q : Finset ℕ,
      (∀ r∈Q,∃ p : ℕ,p.Prime ∧ p-1≤d*r.totient ∧
        c*(rho^h)⁻¹≤B p ∧ ((d*r.totient:ℕ):ℝ)≤
          Real.exp (Real.exp (localPrimeHeight A L h))) →
      (∀ k∈Finset.Icc 1 (discardExponent (localPrimeHeight A L h)),
        (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty →
        ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
          (2:ℝ)^k/Real.log ((2:ℝ)^k)*(B ((2:ℝ)^k))^(-4:ℝ)) →
      (∑ r∈Q,(r.totient:ℝ)⁻¹)≤rho^h := by
  obtain ⟨D,_hD,hlayers⟩ := local_residual_layer_bounds hc hA L
  let K : ℝ := ((c/2)^4)⁻¹
  let C : ℝ := (12*d/Real.log 2)*K
  have hC : 0≤C := by dsimp [C,K]; positivity
  filter_upwards [hlayers 256,local_residual_mass_decay hA.le hC L] with h hdata hdecay
  intro Q hvalues hcount
  let U := localPrimeHeight A L h
  let J := discardExponent U
  let T := (c/2)*(rho^h)⁻¹
  have hT : 0<T := mul_pos (half_pos hc) (inv_pos.mpr (pow_pos rho_pos h))
  have hpoint (r) (hr : r∈Q) :
      1<d*r.totient ∧ d*r.totient≤2^J ∧
      let z := (2:ℝ)^(Nat.clog 2 (d*r.totient))
      max 256 256≤z ∧ (c/2)*(rho^h)⁻¹≤B z ∧ 0≤B z ∧
        Real.log (B z+4)≤D*h ∧ (localSquareCutoff z:ℝ)≤localNormalityScale h := by
    obtain ⟨p,hp,hpv,hgeo,hu⟩ := hvalues r hr
    exact hdata p (d*r.totient) hp hpv hgeo hu
  have hm := residual_fourth_power_mass d J hT Q
    (fun r hr => ⟨(hpoint r hr).1,by exact_mod_cast (hpoint r hr).2.1⟩)
    (fun r hr => (hpoint r hr).2.2.2.1) hcount
  have hU := localPrimeHeight_ge_two hA.le L h
  have hJ : 1+Real.log J≤3*U := by
    have hh := (discardExponent_bounds hU).2
    dsimp only [J]
    linarith only [hh,hU]
  have hpow : T^(-4:ℝ)≤K*rho^(3*h) := by
    have hh := local_geometric_inverse_fourth (half_pos hc) (le_refl T)
    apply hh.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le (by omega : 3*h≤4*h))
      (inv_nonneg.mpr (pow_nonneg (half_pos hc).le 4))
  calc
    _ ≤ (4*d/Real.log 2)*T^(-4:ℝ)*(1+Real.log J) := hm
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
