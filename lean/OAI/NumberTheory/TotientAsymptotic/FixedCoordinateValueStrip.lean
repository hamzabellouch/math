import OAI.NumberTheory.TotientAsymptotic.FixedCoordinateTerminalMass
import OAI.NumberTheory.TotientAsymptotic.TerminalPrefixMassCount

namespace OAI

/-! A fixed bad coordinate remains exponentially rare when distinct smooth
residual totients are attached to a terminal prime-prefix strip. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_value_strip (H : ℕ) :
    ∃ C a c : ℝ,0 < C ∧ 0 < a ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+3+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ k : ℕ,2 ≤ k → ∀ Q : Finset ℕ,∀ n : ℕ→ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      N+3 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
      ∀ j < N+3,fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤ 
        xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
    (∀ v∈Q,(k:ℝ) ≤ fordPrimeCoordinate (n v) (N+3) ∧
      fordPrimeCoordinate (n v) (N+3) ≤ (k:ℝ)+1) →
    (∀ v∈Q,primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
      (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*
      Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨A,a,c,hA,ha,hc,hmass⟩ := fixed_coordinate_terminal_mass (H+1)
  obtain ⟨D,hD,hcount⟩ := terminal_prefix_mass_count
  refine ⟨D*A,a,c,mul_pos hD hA,ha,hc,?_⟩
  filter_upwards [hmass] with P hP
  filter_upwards [hP,hcount,eventually_gt_atTop (1:ℝ)] with x hx hcount hx1
  intro N hN i hi k hk Q n hQ hstrip hbad
  let Z:=Q.image (fun v => fordPrefixPrimes (n v) (N+2))
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hpre (v) (hv : v∈Q) :
      (∀ j,(fordPrefixPrimes (n v) (N+2) j).Prime) ∧
      primePrefixCoord (fordPrefixPrimes (n v) (N+2))∈
        enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes (n v) (N+2)) (Fin.last (N+1)) := by
    have ho := ford_coordinate_antitone (n v) (show N+2 ≤ N+3 by omega)
    have hprev : 1 < fordPrimeCoordinate (n v) (N+2) := by
      linarith only [ho,(hstrip v hv).1,hk']
    have hh := terminal_prefix_conditions (j:=N+3) (L:=N+3) (by omega) le_rfl
      (by norm_num : (1/100:ℝ) ≤ 1) hprev (hQ v hv).2.2.2.2.2.2
    exact ⟨hh.1,hh.2.1,hh.2.2 (Fin.last (N+1)) (by simp)⟩
  have hlast (v) (hv : v∈Q) :
      primePrefixCoord (fordPrefixPrimes (n v) (N+2)) (Fin.last (N+1))=
        fordPrimeCoordinate (n v) (N+2) := by
    have ho := ford_coordinate_antitone (n v) (show N+2 ≤ N+3 by omega)
    have hp : 0 < fordPrimeCoordinate (n v) (N+2) := by
      linarith only [ho,(hstrip v hv).1,hk']
    exact (fordPrimeCoordinate_eq_raw_of_pos hp).symm
  have hm : (∑ p∈Z,reciprocalShiftWeight p) ≤ A*G x (N+2)*
      Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N (by omega) i hi k (by positivity) Z
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(hpre v hv).1,(hpre v hv).2.1,(hpre v hv).2.2,?_,hbad v hv⟩
    rw [hlast v hv]
    exact (hstrip v hv).1.trans (ford_coordinate_antitone (n v) (by omega))
  have hh := hcount (N+2) k Q n (by
    intro v hv
    obtain ⟨hn,hφ,hhead,hvx,hlen,hgap,_hrows⟩ := hQ v hv
    exact ⟨hn,hφ,hhead,hvx,hlen,hgap,(hstrip v hv).2⟩)
  have hnorm : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (mul_nonneg hD.le hnorm))
    (Real.exp_pos (10*(Real.log ((k:ℝ)+5))^2)).le
  have he : Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ))*
      Real.exp (10*(Real.log ((k:ℝ)+5))^2) =
      terminalMassWeight a k*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    unfold terminalMassWeight
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  apply hh.trans
  apply hs.trans_eq
  change D*(x/Real.log x)*(A*G x (N+2)*Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ)))*
    Real.exp (10*(Real.log ((k:ℝ)+5))^2)=_
  calc
    _ = D*A*(x/Real.log x)*G x (N+2)*
        (Real.exp (-a*(k:ℝ)-c*(N+2-(i.val+1):ℕ))*Real.exp (10*(Real.log ((k:ℝ)+5))^2)) := by ring
    _ = _ := by rw [he]; ring

end TotientAsymptotic

end

end OAI
