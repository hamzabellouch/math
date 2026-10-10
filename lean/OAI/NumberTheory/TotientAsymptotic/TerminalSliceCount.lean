import OAI.NumberTheory.TotientAsymptotic.TerminalBandCount

namespace OAI

/-! Sum the actual terminal-coordinate strips using their finite residual masses. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem terminal_slice_value_count (H : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+2+H=m x →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      N+2 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (N+2) < fordPrime (n v) (N+1) ∧
      2 < fordPrimeCoordinate (n v) (N+2) ∧
      ∀ i < N+2,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+1) := by
  classical
  obtain ⟨A,c,hA,hc,hcount⟩ := terminal_band_value_count H
  let T := ∑' k : ℕ,terminalMassWeight c k
  have hT : 0 ≤ T := tsum_nonneg (fun k => (terminalMassWeight_pos c k).le)
  refine ⟨A*(T+1),by positivity,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm Q n hQ
  let key : ℕ → ℕ := fun v => ⌊fordPrimeCoordinate (n v) (N+2)⌋₊
  let I := Q.image key
  let R (k : ℕ) := Q.filter (fun v => key v=k)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨key v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
      Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ k ∈ I,((R k).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (k : ℕ) (hk : k ∈ I) : ((R k).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+1)*terminalMassWeight c k := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    have hk2 : 2 ≤ key v := Nat.le_floor (hQ v hv).2.2.2.2.2.2.1.le
    apply hx N hNm (key v) hk2 (R (key v)) n
    intro w hw
    obtain ⟨hw,hkey⟩ := Finset.mem_filter.mp hw
    obtain ⟨hn,hφ,hhead,hwx,hlen,hgap,hlarge,hrows⟩ := hQ w hw
    refine ⟨hn,hφ,hhead,hwx,hlen,hgap,?_,?_,hrows⟩
    · rw [← hkey]
      exact Nat.floor_le (le_max_left _ _)
    · rw [← hkey]
      exact (Nat.lt_floor_add_one _).le
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+1) := by
    have hlog := Real.log_pos hx1
    have hG := G_pos hB (N+1)
    positivity
  calc
    _ ≤ ∑ k ∈ I,((R k).card:ℝ) := hcard
    _ ≤ ∑ k ∈ I,A*(x/Real.log x)*G x (N+1)*terminalMassWeight c k :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+1))*(∑ k ∈ I,terminalMassWeight c k) := by
      rw [Finset.mul_sum]
    _ ≤ (A*(x/Real.log x)*G x (N+1))*T :=
      mul_le_mul_of_nonneg_left (finite_terminal_mass_bound hc I) hfac
    _ ≤ (A*(x/Real.log x)*G x (N+1))*(T+1) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
