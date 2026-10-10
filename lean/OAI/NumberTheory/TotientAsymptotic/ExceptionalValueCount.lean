import OAI.NumberTheory.TotientAsymptotic.LargeNonNormalValues
import OAI.NumberTheory.TotientAsymptotic.SmallPrimeValueCount

namespace OAI

/-! The complete non-normal-prime contribution to Ford's nice-value exception.
All fibers are handled by finite value covers, without multiplicity weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma totient_div_prime_le {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (n/p).totient ≤ n.totient := by
  have hp1 : 1 ≤ p-1 := by have := hp.two_le; omega
  rcases totient_prime_extension_cases hp hpn with h|h
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp1
  · rw [h]
    simpa using Nat.mul_le_mul_right (n/p).totient hp.one_le

/-- A finite, uniform form of the non-normal-prime part of Ford Lemma 2.8.
The two numeric inequalities select any cutoff between the fourth-root and
square-root scales. -/
theorem non_normal_value_count_split : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S x : ℝ) (N J : ℕ),2 < S → 0 ≤ B S → 4 ≤ N → 16 ≤ x →
    (N:ℝ)^2 ≤ x → x^(1/4:ℝ) ≤ N → 1 ≤ J → x ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
      (v:ℝ) ≤ x ∧ ¬IsNormalPrime S p) →
    (Q.card:ℝ) ≤
      C*dyadicTotientEnvelope J*x/Real.log x*
        (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*
          (Real.log S)^(-1/6:ℝ) +
      (D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ))*
        (1+4*dyadicTotientEnvelope J*(1+Real.log J)) := by
  obtain ⟨C,hC,hsmall⟩ := small_non_normal_value_count
  obtain ⟨D,hD,hlarge⟩ := large_non_normal_value_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S x N J hS hBS hN hx hNx hroot hJ hxJ Q hQ
  let A := Q.filter (fun v => ∃ n p : ℕ,0 < n ∧ n.totient=v ∧ p.Prime ∧ p ∣ n ∧
    (v:ℝ) ≤ x ∧ p ≤ N ∧ ¬IsNormalPrime S p)
  let T := Q\A
  have hsmall' := hsmall S x N J hS hBS hN hx hNx hxJ A
    (fun v hv => (Finset.mem_filter.mp hv).2)
  have hres (d : ℕ) (hd : d ∈ totientValues x) :
      IsTotient d ∧ (d:ℝ) ≤ (2:ℝ)^J := by
    obtain ⟨hd,ht⟩ := Finset.mem_filter.mp hd
    exact ⟨ht,(Nat.floor_le (by linarith : 0 ≤ x)).trans' (Nat.cast_le.mpr (Finset.mem_Icc.mp hd).2) |>.trans hxJ⟩
  have hlarge' := hlarge S x hS (by linarith) (totientValues x) T
    (fun d hd => isTotient_pos (hres d hd).1) (by
      intro v hv
      obtain ⟨hvQ,hvA⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨n,p,hn,hφ,hp,hpn,hvx,hbad⟩ := hQ v hvQ
      have hpN : N < p := by
        by_contra hh
        exact hvA (Finset.mem_filter.mpr ⟨hvQ,n,p,hn,hφ,hp,hpn,hvx,by omega,hbad⟩)
      have hd : 0 < (n/p).totient := Nat.totient_pos.mpr
        (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos)
      have hdx : ((n/p).totient:ℝ) ≤ x :=
        (Nat.cast_le.mpr (totient_div_prime_le hp hpn)).trans (by rwa [hφ])
      refine ⟨n,p,hn,hφ,hp,hpn,by omega,hroot.trans (by exact_mod_cast hpN.le),hvx,hbad,?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd,Nat.le_floor hdx⟩,⟨n/p,
        Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos,rfl⟩⟩)
  have hB : 0 ≤ B (2*x) := by
    have hh : B 4 ≤ B (2*x) := Real.log_le_log
      (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) (by linarith))
    exact (doubleLog_nat_pos (n:=4) (by norm_num)).le.trans hh
  have hcoef : 0 ≤ D*x/Real.log x*(B (2*x))^5*(Real.log S)^(-1/6:ℝ) := by
    have := Real.log_pos (show 1 < x by linarith)
    have := Real.log_pos (show 1 < S by linarith)
    positivity
  have hmass := dyadic_totient_reciprocal_mass hJ (totientValues x) hres
  have hcard : (Q.card:ℝ) = (A.card:ℝ)+(T.card:ℝ) := by
    have hsubset : A ⊆ Q := Finset.filter_subset _ _
    have hh := Finset.card_sdiff_add_card_eq_card hsubset
    dsimp only [T]
    exact_mod_cast (show Q.card=A.card+(Q\A).card by omega)
  rw [hcard]
  exact add_le_add hsmall' (hlarge'.trans (mul_le_mul_of_nonneg_left hmass hcoef))

end TotientAsymptotic

end

end OAI
