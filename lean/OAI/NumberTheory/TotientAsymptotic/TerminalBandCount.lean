import OAI.NumberTheory.TotientAsymptotic.FixedTerminalMass
import OAI.NumberTheory.TotientAsymptotic.SmoothTerminalMassBound
import OAI.NumberTheory.TotientAsymptotic.TerminalMassSeries
import OAI.NumberTheory.TotientAsymptotic.PrefixResidualCount
import OAI.NumberTheory.TotientAsymptotic.SmallTerminalPrefix

namespace OAI

/-! Count actual values in a terminal-coordinate strip through distinct residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem terminal_band_value_count (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+2+H=m x → ∀ k : ℕ,2 ≤ k →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      N+2 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (N+2) < fordPrime (n v) (N+1) ∧
      (k:ℝ) ≤ fordPrimeCoordinate (n v) (N+2) ∧
      fordPrimeCoordinate (n v) (N+2) ≤ (k:ℝ)+1 ∧
      ∀ i < N+2,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+1)*terminalMassWeight c k := by
  classical
  obtain ⟨A,c,hA,hc,hmass⟩ := fixed_terminal_prime_mass (H+1)
  obtain ⟨D,hD,hres⟩ := smooth_terminal_mass_bound
  refine ⟨64*A*D,c,by positivity,hc,?_⟩
  filter_upwards [hmass,large_prime_product_value_count,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hm hcount hx hB
  intro N hNm k hk Q n hQ
  let P := Q.image (fun v => fordPrefixPrimes (n v) (N+1))
  let R := Q.image (fun v => (fordCofactor (n v) (N+2)).totient)
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hpre (v) (hv : v ∈ Q) :
      (∀ i,(fordPrefixPrimes (n v) (N+1) i).Prime) ∧
      primePrefixCoord (fordPrefixPrimes (n v) (N+1)) ∈
        enlargedSimplex (N+1) (B x) (xi x 0) (fun i => xi x (i.val+1)) ∧
      (1/100:ℝ) ≤ primePrefixCoord (fordPrefixPrimes (n v) (N+1)) (Fin.last N) := by
    have ho := ford_coordinate_antitone (n v) (show N+1 ≤ N+2 by omega)
    have hprev : 1 < fordPrimeCoordinate (n v) (N+1) := by
      linarith only [ho,(hQ v hv).2.2.2.2.2.2.1,hk']
    have hh := terminal_prefix_conditions (j:=N+2) (L:=m x) (by omega) (by omega)
      (by norm_num : (1/100:ℝ) ≤ 1) hprev (hQ v hv).2.2.2.2.2.2.2.2
    exact ⟨hh.1,hh.2.1,hh.2.2 (Fin.last N) (by simp)⟩
  have hlast (v) (hv : v ∈ Q) :
      primePrefixCoord (fordPrefixPrimes (n v) (N+1)) (Fin.last N)=
        fordPrimeCoordinate (n v) (N+1) := by
    have ho := ford_coordinate_antitone (n v) (show N+1 ≤ N+2 by omega)
    have hpos : 0 < fordPrimeCoordinate (n v) (N+1) := by
      linarith only [ho,(hQ v hv).2.2.2.2.2.2.1,hk']
    change primeDoubleLog (n v) (N+1)=fordPrimeCoordinate (n v) (N+1)
    exact (fordPrimeCoordinate_eq_raw_of_pos hpos).symm
  have hPmass : (∑ p ∈ P,reciprocalShiftWeight p) ≤
      A*G x (N+1)*Real.exp (-c*(k:ℝ)) := by
    apply hm N (by omega) k (by positivity) P
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(hpre v hv).1,?_,(hpre v hv).2.2,?_⟩
    · simpa only [xi_eq_simplexBoxError,Nat.sub_zero] using (hpre v hv).2.1
    · rw [hlast v hv]
      exact ((hQ v hv).2.2.2.2.2.2.1).trans
        (ford_coordinate_antitone (n v) (by omega))
  have hRpos (d) (hd : d ∈ R) : 0 < d := by
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.totient_pos.mpr (fordCofactor_pos _ _)
  have hRmass : (∑ d ∈ R,(d:ℝ)⁻¹) ≤ D*Real.exp (10*(Real.log ((k:ℝ)+5))^2) := by
    apply hres k (by positivity) R
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    exact ⟨⟨fordCofactor (n v) (N+2),fordCofactor_pos _ _,rfl⟩,
      small_terminal_smooth (by positivity) (hQ v hv).2.2.2.2.2.2.2.1⟩
  have hh := hcount (N+1) P R Q (by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    exact (hpre v hv).1) hRpos (by
      intro v hv
      obtain ⟨hn,hφ,hhead,hvx,hlen,hgap,_,_,_⟩ := hQ v hv
      refine ⟨n v,fordPrime (n v) 0,hn,hφ,fordPrime_prime (by omega),?_,hhead,hvx,?_⟩
      · have he := fordCofactor_step (n v) 0
        rw [fordCofactor_zero hn] at he
        exact ⟨fordCofactor (n v) 1,he⟩
      · apply Finset.mem_image.mpr
        refine ⟨(fordPrefixPrimes (n v) (N+1),(fordCofactor (n v) (N+2)).totient),
          Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,
            Finset.mem_image.mpr ⟨v,hv,rfl⟩⟩,?_⟩
        exact (strict_gap_residual_totient hn (by omega) hlen hgap).symm)
  have hnon : 0 ≤ 64*x/Real.log x := by
    have hl := Real.log_pos hx
    positivity
  have hsum := mul_le_mul hPmass hRmass
    (Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    (by have hG := G_pos hB (N+1); positivity)
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left hsum hnon
  rw [←mul_assoc] at hmul
  apply hmul.trans_eq
  unfold terminalMassWeight
  rw [show 10*(Real.log ((k:ℝ)+5))^2-c*k=(-c*(k:ℝ))+10*(Real.log ((k:ℝ)+5))^2 by ring,Real.exp_add]
  ring

end TotientAsymptotic

end

end OAI
