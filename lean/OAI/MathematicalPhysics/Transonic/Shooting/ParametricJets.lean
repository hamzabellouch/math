import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section

namespace SepticProfile.ParametricJets
open Polynomial

variable {K : Type*} [CommRing K]

/-- The literal normalized source polynomial residual, expanded about z=1. -/
def residualP (sigma kappa c : K) (u : Polynomial K) : Polynomial K :=
  (1+X)*(1-C sigma*(1+X)^2)*(1-u^2)*u.derivative -
    (1-C c*u^2)*(C kappa*(1+X)*(1-u^2)+3*((1+X)-u))

 theorem coe_residualP (sigma kappa c : K) (u : Polynomial K) :
    (residualP sigma kappa c u : PowerSeries K) = Formal.residual sigma kappa c u := by
  simp only [residualP, Formal.residual, Formal.den, Formal.prefactor, Formal.z,
    Formal.r, Formal.t, coe_sub, coe_mul, coe_add, coe_pow, coe_one, coe_X, coe_C,
    ← PowerSeries.derivative_coe]
  have h3 : ((3 : Polynomial K) : PowerSeries K) = 3 := by
    rw [show (3 : Polynomial K) = 1+1+1 by ring, coe_add, coe_add, coe_one]
    ring
  rw [h3]

 theorem coeff_residual_one (sigma kappa c : K) {u : PowerSeries K} {s : K}
    (hu0 : PowerSeries.constantCoeff u=1) (hu1 : PowerSeries.coeff 1 u=s) :
    PowerSeries.coeff 1 (Formal.residual sigma kappa c u) =
      -2*(1-sigma)*s^2+(1-c)*(2*kappa+3)*s-3*(1-c) := by
  have hd : PowerSeries.constantCoeff (PowerSeries.derivative u)=s := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simpa using hu1
  simp only [Formal.residual, Formal.den, Formal.prefactor, Formal.z, Formal.r,
    Formal.t, map_sub, map_add, map_mul, map_pow, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_one_pow, PowerSeries.constantCoeff_C, map_ofNat, hu0, hu1, hd]
  norm_num
  ring

 theorem constantCoeff_residual (sigma kappa c : K) {u : PowerSeries K}
    (hu0 : PowerSeries.constantCoeff u=1) :
    PowerSeries.constantCoeff (Formal.residual sigma kappa c u) = 0 := by
  simp [Formal.residual, Formal.den, Formal.prefactor, Formal.z, Formal.r,
    Formal.t, hu0]

/-- Construct all required finite sonic jets at a nonresonant weak slope.
There is no assumed formal series. The zero multiplier at a resonance is
explicitly excluded; this is why the resonant parameter cannot be used as a
selected analytic profile parameter. -/
 theorem exists_finite_jet (sigma kappa c s : K)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (N : ℕ)
    (hne : ∀ n < N, IsUnit ((1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3))) :
    ∃ p : Polynomial K, p.coeff 0=1 ∧ p.coeff 1=s ∧
      ∀ i ≤ N+1, (residualP sigma kappa c p).coeff i=0 := by
  induction N with
  | zero =>
    let p : Polynomial K := 1+C s*X
    have hp0 : p.coeff 0=1 := by simp [p]
    have hp1 : p.coeff 1=s := by simp [p, Polynomial.coeff_one]
    have hp0' : PowerSeries.constantCoeff (p : PowerSeries K)=1 := by simpa using hp0
    have hp1' : PowerSeries.coeff 1 (p : PowerSeries K)=s := by simpa using hp1
    refine ⟨p,hp0,hp1,?_⟩
    intro i hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · rw [← Polynomial.coeff_coe, coe_residualP, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact constantCoeff_residual sigma kappa c hp0'
    · rw [← Polynomial.coeff_coe, coe_residualP, coeff_residual_one sigma kappa c hp0' hp1']
      linear_combination -hs
  | succ n ih =>
    obtain ⟨p,hp0,hp1,hp⟩ := ih (fun i hi => hne i (by omega))
    let d : K := (1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3)
    obtain ⟨u,hu⟩ := hne n (by omega)
    have hu' : (u : K)=d := hu
    have hd : d*(↑(u⁻¹):K)=1 := by rw [← hu']; simp
    let a : K := -(residualP sigma kappa c p).coeff (n+2)*(↑(u⁻¹):K)
    let q : Polynomial K := p+C a*X^(n+2)
    have hq0 : q.coeff 0=1 := by simp [q,hp0]
    have hq1 : q.coeff 1=s := by simp [q,hp1]
    have hp0' : PowerSeries.constantCoeff (p : PowerSeries K)=1 := by simpa using hp0
    have hp1' : PowerSeries.coeff 1 (p : PowerSeries K)=s := by simpa using hp1
    have hq0' : PowerSeries.constantCoeff (q : PowerSeries K)=1 := by simpa using hq0
    have hag : Formal.Agree (n+1) (q : PowerSeries K) (p : PowerSeries K) := by
      intro i hi
      simp only [Polynomial.coeff_coe]
      simp [q, show ¬i=n+2 by omega]
    refine ⟨q,hq0,hq1,?_⟩
    intro i hi
    by_cases hi' : i=n+2
    · subst i
      have he := Formal.coefficient_step sigma kappa c (p : PowerSeries K) s hp0' hp1' n a
      have hq : (q : PowerSeries K) = (p : PowerSeries K)+PowerSeries.C a*PowerSeries.X^(n+2) := by
        simp [q]
      rw [← hq, ← coe_residualP, ← coe_residualP, Polynomial.coeff_coe,
        Polynomial.coeff_coe] at he
      rw [he]
      change (residualP sigma kappa c p).coeff (n+2) + d * a = 0
      dsimp only [a]
      calc
        _ = (residualP sigma kappa c p).coeff (n+2)*(1-d*(↑(u⁻¹):K)) := by ring
        _ = 0 := by rw [hd]; ring
    · have he := Formal.residual_agree sigma kappa c hag hq0' hp0' i (by omega)
      rw [← coe_residualP, ← coe_residualP, Polynomial.coeff_coe,
        Polynomial.coeff_coe] at he
      exact he.trans (hp i (by omega))

 theorem exists_finite_jet_divisible (sigma kappa c s : K)
    (hs : 2*(1-sigma)*s^2-(1-c)*(2*kappa+3)*s+3*(1-c)=0)
    (N : ℕ)
    (hne : ∀ n < N, IsUnit ((1-c)*(2*kappa+3)-2*(1-sigma)*s*(n+3))) :
    ∃ p : Polynomial K, p.coeff 0=1 ∧ p.coeff 1=s ∧
      (X : Polynomial K)^(N+2) ∣ residualP sigma kappa c p := by
  obtain ⟨p,hp0,hp1,hp⟩ := exists_finite_jet sigma kappa c s hs N hne
  exact ⟨p,hp0,hp1,X_pow_dvd_iff.mpr (fun i hi => hp i (by omega))⟩

end SepticProfile.ParametricJets

end
end

end OAI
