import OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z delta theta g s Hc eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(s+4*eta)) :
    correlatedSecondRadius p d G E L (Z^(Hc+12*eta+tau)) (Z^tau) ≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G ≤ Z^(theta-g+2*eta) := by
    calc
      _ ≤ Z^(theta+eta)/Z^(g-eta) := div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ ≤ Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*
        Z^tau/Z^(Hc+12*eta+tau) := by
      unfold correlatedSecondRadius
      gcongr
    _ = _ := by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem second_correlated_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z M r ell V delta A B j t g theta eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    correlatedSecondRadius p d G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau) ≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb := second_correlated_radius_bound p hp d G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hd hE hG hL
  convert hb using 1; congr 1
  unfold childM decrease firstPhysicalHeight
  ring

end
end SevenEighths.InverseMoment

end OAI
