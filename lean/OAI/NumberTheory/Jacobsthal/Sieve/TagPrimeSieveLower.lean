import OAI.NumberTheory.Jacobsthal.Paths.TagAffineConditions

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve

open _root_.Filter
open scoped Topology
open ErdosUnitLifts Erdos970Dependency.SiegelWalfisz

theorem tag_prime_sieve_lower (Cs K rho xi gamma : ℝ)
    (hCs : 0 ≤ Cs) (hK : 0 < K) (hrho : 1 < rho) (hxi : 0 < xi) (hgamma : 0 < gamma) :
    ∃ w₀ : ℝ,3 ≤ w₀ ∧ ∀ w P R V : ℝ,w₀ ≤ w →
      Real.exp (K*(Real.log w)^3) ≤ P → P ≤ Real.exp ((rho*K)*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      xi/(16*w^(2*Cs+10)) ≤ V/R → V/R ≤ w^(-(2*Cs+10)) →
      ∀ D : ℕ,0 < D → (D:ℝ) ≤ w^Cs → ∀ A : ℤ,A.natAbs.Coprime D →
      ∀ residue : ℕ → ℤ,∀ q d0 ell : ℕ,∀ m : ℤ,
      (∀ t∈smallPrimeSet P,q.Coprime t) → 0 < d0 →
      (∀ t∈d0.primeFactors,t∈unalignedPrimes P D A residue) →
      ell.Prime → P<(ell:ℝ) → m.natAbs=d0*ell →
      (1-gamma)*(((intervalPrimes R V 1 0).card:ℝ)/(D:ℝ))*
        eulerWeight (restrictedPrimes P D A residue d0) ≤
        ((actualSurvivorPrimes P R V D A ((q:ℤ)*m) residue).card:ℝ) := by
  have hcap : 0 ≤ rho*K := mul_nonneg (by linarith) hK.le
  obtain ⟨WC,hWC⟩ := eventually_atTop.mp
    (unit_lift_sieve_lower_eventually Cs (rho*K) xi gamma hCs hcap hxi hgamma)
  obtain ⟨WD,hWD⟩ := eventually_atTop.mp (eventually_cutoff_dominates (max Cs 1) K hK)
  obtain ⟨WT,hWT⟩ := eventually_atTop.mp (eventually_cutoff_le_subbin (rho*K))
  refine ⟨max 3 (max WC (max WD WT)),le_max_left _ _,?_⟩
  intro w P R V hw hPlow hPup hR hlo hhi D hD hDw A hAc residue q d0 ell m hq hd0 hsupport hell hellP hm
  have hwAll : max WC (max WD WT) ≤ w := (le_max_right _ _).trans hw
  have hCore := hWC w ((le_max_left _ _).trans hwAll)
  have hwDt : max WD WT ≤ w := (le_max_right _ _).trans hwAll
  have hDom := hWD w ((le_max_left _ _).trans hwDt)
  have hTag := hWT w ((le_max_right _ _).trans hwDt)
  have hw3 := hCore.1
  have hw1 : 1 ≤ w := by linarith
  have hPow : w ≤ w^(max Cs 1) := Real.self_le_rpow_of_one_le hw1 (le_max_right _ _)
  have hwP : w<P := hPow.trans_lt (hDom.2.trans_le hPlow)
  have hP3 : 3 ≤ P := by linarith
  have hDpow : w^Cs ≤ w^(max Cs 1) := Real.rpow_le_rpow_of_exponent_le hw1 (le_max_left _ _)
  have hDP : (D:ℝ)<P := (hDw.trans hDpow).trans_lt (hDom.2.trans_le hPlow)
  have hPR : P ≤ R := hTag.2 P R hPup hR
  let B : ℤ := (q:ℤ)*m
  have hprofile : ∀ t∈smallPrimeSet P,t∣B.natAbs ↔ t∣d0 :=
    signed_coefficient_profile P q d0 ell m hq hell hellP hm
  have hBc : B.natAbs.Coprime D := denominator_coefficient_coprime P D hD hDP A B residue d0 hd0 hsupport hprofile
  have hAu : IsUnit (A:ZMod D) := intCast_isUnit_of_natAbs_coprime D A hAc
  have hBu : IsUnit (B:ZMod D) := intCast_isUnit_of_natAbs_coprime D B hBc
  let S := restrictedPrimes P D A residue d0
  let bad := forbiddenClass D A B residue
  have hInfo : ∀ t∈S,t.Prime ∧ (t:ℝ) ≤ P ∧ ¬t∣D := by
    intro t ht
    have he := (Finset.mem_filter.mp ht).1
    obtain ⟨htS,htD,_⟩ := Finset.mem_filter.mp he
    have hh := (mem_smallPrimeSet P t).mp htS
    exact ⟨hh.1,hh.2.le,htD⟩
  have hCount := hCore.2 P R V hP3 hPup hR hlo hhi D hD hDw A B residue hAu hBu S bad
    (fun t ht => (hInfo t ht).1) (fun t ht => (hInfo t ht).2.1)
    (fun t ht => (hInfo t ht).2.2)
    (fun t ht => forbiddenClass_ne_zero P D A B residue d0 hprofile t ht)
  have hEq := actualSurvivorPrimes_eq_sieve P R V hPR D hD hDP A B residue d0 hd0 hsupport hprofile
  rw [← hEq] at hCount
  exact hCount

lemma natAbs_of_signed_prime_multiple (d0 ell : ℕ) (m : ℤ)
    (hm : m=(d0:ℤ)*ell ∨ m= -((d0:ℤ)*ell)) : m.natAbs=d0*ell := by
  rcases hm with rfl | rfl
  · rw [← Nat.cast_mul]
    exact Int.natAbs_natCast _
  · rw [Int.natAbs_neg,← Nat.cast_mul]
    exact Int.natAbs_natCast _

noncomputable def boundedSurvivorPrimes (Y : ℕ) (P R V : ℝ) (D : ℕ) (A B : ℤ)
    (residue : ℕ → ℤ) : Finset ℕ :=
  (actualSurvivorPrimes P R V D A B residue).filter
    (fun p => 1 ≤ actualN D A B p ∧ actualN D A B p ≤ (Y:ℤ))

theorem boundedSurvivorPrimes_eq (Y : ℕ) (P R V : ℝ) (D : ℕ) (A B : ℤ) (residue : ℕ → ℤ)
    (hRange : ∀ p∈intervalPrimes R V 1 0,(D:ℤ)∣A+B*p →
      1 ≤ actualN D A B p ∧ actualN D A B p ≤ (Y:ℤ)) :
    boundedSurvivorPrimes Y P R V D A B residue=actualSurvivorPrimes P R V D A B residue := by
  apply Finset.filter_eq_self.mpr
  intro p hp
  obtain ⟨hp,hInt,_⟩ := Finset.mem_filter.mp hp
  exact hRange p hp hInt

end ErdosStoppedTagSieve


end Erdos970

end OAI
