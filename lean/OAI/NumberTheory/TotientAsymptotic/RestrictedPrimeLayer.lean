import OAI.NumberTheory.TotientAsymptotic.NormalRemainderLayer

namespace OAI

/-! One coordinate restriction in an arbitrary finite family of basic
remainders. The initial segment is charged to its projected simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma restricted_prime_layer_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (RemainderDatum (L x H))) (n j : ℕ),
      n ≤ R x H → n < j → j ≤ L x H →
      ∀ U V : Finset ℕ,
      (∀ η ∈ S, IsBasicRemainder x H η) →
      (∀ η ∈ S, ∀ l ∈ Finset.Icc (n+1) (L x H), remainderPrime η l ∈ U) →
      (∀ η ∈ S, remainderPrime η j ∈ V) →
      (∑ η ∈ S, remainderReciprocalWeight η) ≤
        (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1) := by
  filter_upwards [basic_prime_initial_mass hbox hren,eventually_ge_atTop 2] with H hpre hH
  filter_upwards [hpre,theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hp hs hHm hB
  intro S n j hn hj hjL U V hS hU hV
  have hPH := P_lt_self hH
  have hnL : n ≤ L x H := by omega
  let Q := S.image RemainderDatum.primes
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  let k : Fin (L x H-n) := ⟨j-(n+1),by omega⟩
  have hk : n+k.val+1=j := by dsimp [k]; omega
  have hall : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ U := by
    intro p hp l
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder]
    exact hU η hη _ (Finset.mem_Icc.mpr ⟨by omega,by have := l.isLt; omega⟩)
  have hbad : ∀ p ∈ Q, primeFinal p n k ∈ V := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder,hk]
    exact hV η hη
  have hm := prime_mass_one_exception hnL Q k U V hall hbad
  have hb := hp n hn hnL Q hQ
  have hw : 0 ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ((∑ p ∈ Q.image (fun p => primeInitial p n hnL), reciprocalShiftWeight p)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1)) := mul_le_mul_of_nonneg_left hm hw
    _ ≤ _ := by
      have hnonneg : 0 ≤ (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
          (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hb hnonneg
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul hw

end TotientAsymptotic

end

end OAI
