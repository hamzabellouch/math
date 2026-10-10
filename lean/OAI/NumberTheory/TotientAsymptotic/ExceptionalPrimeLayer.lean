import OAI.NumberTheory.TotientAsymptotic.PrimeMassSplit

namespace OAI

/-! A restricted coordinate in a late layer costs its own reciprocal mass;
the initial segment retains the projected simplex saving. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prime_mass_one_exception {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (j : Fin (N-n)) (U V : Finset ℕ)
    (hU : ∀ p ∈ Q, ∀ k, primeFinal p n k ∈ U)
    (hV : ∀ p ∈ Q, primeFinal p n j ∈ V) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
  classical
  have hh := prime_mass_split hn Q (fun k => if k=j then V else U) (by
    intro p hp k
    split_ifs with hk
    · subst k; exact hV p hp
    · exact hU p hp k)
  have he : (∏ k : Fin (N-n), ∑ q ∈ (if k=j then V else U), ((q-1 : ℕ) : ℝ)⁻¹) =
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true]
    congr 1
    calc
      _ = ∏ _k ∈ (Finset.univ.erase j), ∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [ite_eq_right (Finset.mem_erase.mp hk).1]
      _ = _ := by simp
  rw [he] at hh
  simpa only [mul_assoc] using hh

theorem basic_prime_initial_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ (n : ℕ) (_hn : n ≤ R x H) (hnL : n ≤ L x H),
    ∀ Q : Finset (Fin (L x H) → ℕ), Q ⊆ fullPrimeTuples x H →
      (∑ p ∈ Q.image (fun p => primeInitial p n hnL),
        reciprocalShiftWeight p) ≤ G x (m x) := by
  filter_upwards [projected_mass_le_G hbox hren,eventually_ge_atTop 2] with H hH hH2
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hHm
  intro n hn hnL Q hQ
  have hPH := P_lt_self hH2
  have hL : 0 < L x H := by unfold L; omega
  let K := m x-n
  have hHK : H ≤ K := by dsimp [K]; unfold R at hn; omega
  have hKm : K ≤ m x := Nat.sub_le _ _
  have hd : R x K=n := by unfold R K; omega
  have hKL : R x K ≤ L x H := by rw [hd]; unfold R L at *; omega
  have hh := hx K hHK hKm (Q.image (fun p => primeInitial p (R x K) hKL)) (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp (hQ hq)
    exact remainderInitial_geometry hKL hL (mem_basicRemainderFinset.mp hη))
  revert hh hKL
  rw [hd]
  intro _ hh
  exact hh

end TotientAsymptotic

end

end OAI
