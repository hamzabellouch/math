import OAI.NumberTheory.TotientAsymptotic.RestrictedPrimeLayer

namespace OAI

/-! Two distinct restricted coordinates in the short suffix. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prime_mass_two_exceptions {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (j k : Fin (N-n)) (hjk : j ≠ k) (U V W : Finset ℕ)
    (hU : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ U)
    (hV : ∀ p ∈ Q, primeFinal p n j ∈ V)
    (hW : ∀ p ∈ Q, primeFinal p n k ∈ W) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
  classical
  let F := fun l : Fin (N-n) => ∑ q ∈ (if l=j then V else if l=k then W else U), ((q-1 : ℕ) : ℝ)⁻¹
  have hh := prime_mass_split hn Q (fun l => if l=j then V else if l=k then W else U) (by
    intro p hp l
    split_ifs with hj hk
    · subst l; exact hV p hp
    · subst l; exact hW p hp
    · exact hU p hp l)
  have hjmem : j ∈ (Finset.univ : Finset (Fin (N-n))) := Finset.mem_univ j
  have hkmem : k ∈ (Finset.univ : Finset (Fin (N-n))).erase j := by simp [Ne.symm hjk]
  have he : (∏ l, F l) =
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
    rw [← Finset.mul_prod_erase _ _ hjmem,← Finset.mul_prod_erase _ _ hkmem]
    have hr : (∏ l ∈ ((Finset.univ : Finset (Fin (N-n))).erase j).erase k, F l) =
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
      calc
        _ = ∏ _l ∈ ((Finset.univ : Finset (Fin (N-n))).erase j).erase k,
            ∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹ := by
          apply Finset.prod_congr rfl
          intro l hl
          have hlk := (Finset.mem_erase.mp hl).1
          have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
          simp only [F,ite_eq_right hlj,ite_eq_right hlk]
        _ = _ := by simp [Finset.card_erase_of_mem hkmem,Nat.sub_sub]
    rw [hr]
    simp only [F,ite_true,ite_eq_right (Ne.symm hjk)]
    ring
  change _ ≤ _*(∏ l, F l) at hh
  rw [he] at hh
  simpa only [mul_assoc] using hh

lemma restricted_two_prime_layer_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (RemainderDatum (L x H))) (n j k : ℕ),
      n ≤ R x H → n < j → j ≤ L x H → n < k → k ≤ L x H → j ≠ k →
      ∀ U V W : Finset ℕ,
      (∀ η ∈ S, IsBasicRemainder x H η) →
      (∀ η ∈ S, ∀ l ∈ Finset.Icc (n+1) (L x H), remainderPrime η l ∈ U) →
      (∀ η ∈ S, remainderPrime η j ∈ V) → (∀ η ∈ S, remainderPrime η k ∈ W) →
      (∑ η ∈ S, remainderReciprocalWeight η) ≤
        (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-2) := by
  filter_upwards [basic_prime_initial_mass hbox hren,eventually_ge_atTop 2] with H hpre hH
  filter_upwards [hpre,theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H)] with x hp hs hHm
  intro S n j k hn hj hjL hk hkL hjk U V W hS hU hV hW
  have hPH := P_lt_self hH
  have hnL : n ≤ L x H := by omega
  let Q := S.image RemainderDatum.primes
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  let j' : Fin (L x H-n) := ⟨j-(n+1),by omega⟩
  let k' : Fin (L x H-n) := ⟨k-(n+1),by omega⟩
  have hj' : n+j'.val+1=j := by dsimp [j']; omega
  have hk' : n+k'.val+1=k := by dsimp [k']; omega
  have hjk' : j' ≠ k' := by intro h; have hh := congrArg Fin.val h; dsimp [j',k'] at hh; omega
  have hall : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ U := by
    intro p hp l
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder]
    exact hU η hη _ (Finset.mem_Icc.mpr ⟨by omega,by have := l.isLt; omega⟩)
  have hbadV : ∀ p ∈ Q, primeFinal p n j' ∈ V := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder,hj']
    exact hV η hη
  have hbadW : ∀ p ∈ Q, primeFinal p n k' ∈ W := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder,hk']
    exact hW η hη
  have hm := prime_mass_two_exceptions hnL Q j' k' hjk' U V W hall hbadV hbadW
  have hb := hp n hn hnL Q hQ
  have hw : 0 ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹ := by positivity
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ((∑ p ∈ Q.image (fun p => primeInitial p n hnL), reciprocalShiftWeight p)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-2)) := mul_le_mul_of_nonneg_left hm hw
    _ ≤ _ := by
      have hnonneg : 0 ≤ (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
          (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-2) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hb hnonneg
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul hw

end TotientAsymptotic

end

end OAI
