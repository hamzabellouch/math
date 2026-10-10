import OAI.NumberTheory.TotientAsymptotic.TwoBandCount
import OAI.NumberTheory.TotientAsymptotic.RegularValueCount

namespace OAI

/-! Sum the two-band estimate over a finite grid of actual cutoff pairs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem two_band_union_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ S X : ℕ,2 ≤ S → 0 ≤ B S → 1 ≤ B X → ∀ H T : ℝ,
    ∀ P : Finset (ℕ×ℕ),
    (∀ q ∈ P,S ≤ q.2 ∧ q.2 ≤ q.1 ∧ B q.1 ≤ H ∧
      Real.log q.1 ≤ Real.log X/(20*B X) ∧ T ≤ a 1*B q.1+a 2*B q.2) →
    ∀ Q : Finset ℕ,
    (∀ v ∈ Q,v ≤ X ∧ CountingRegular S X v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧ 3 ≤ n.primeFactorsList.length ∧
        ∃ q ∈ P,q.1 < fordPrime n 1 ∧ q.2 < fordPrime n 2) →
    (Q.card:ℝ) ≤ C*X*P.card*Real.exp (-T+4*B S+5*D+8*Real.sqrt (B S*H)) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := ford_two_band_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X hS hBS hBX H T P hP Q hQ
  let F := fun q : ℕ×ℕ => Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧
    3 ≤ n.primeFactorsList.length ∧ q.1 < fordPrime n 1 ∧ q.2 < fordPrime n 2)
  have hcover : Q ⊆ P.biUnion F := by
    intro v hv
    obtain ⟨hvX,hreg,n,hn,hφ,hlen,q,hq,hq1,hq2⟩ := hQ v hv
    exact Finset.mem_biUnion.mpr ⟨q,hq,Finset.mem_filter.mpr ⟨hv,n,hn,hφ,hlen,hq1,hq2⟩⟩
  have hcell (q : ℕ×ℕ) (hq : q ∈ P) :
      ((F q).card:ℝ) ≤ C*X*Real.exp (-T+4*B S+5*D+8*Real.sqrt (B S*H)) := by
    obtain ⟨hSq,horder,hBH,hlog,hT⟩ := hP q hq
    have hh := hbound S X q.1 q.2 hS hSq horder hBS hBX hlog (F q) (by
      intro v hv
      obtain ⟨hv,n,hn,hφ,hlen,hq1,hq2⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvX,hreg,_⟩ := hQ v hv
      have hr := hreg.2.2 n hn hφ
      exact ⟨n,hn,hφ,hvX,hreg.1,hreg.2.1,hr.1,hr.2,hlen,hq1,hq2⟩)
    have hsqrt : Real.sqrt (B S*B q.1) ≤ Real.sqrt (B S*H) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hBH hBS)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ ((P.biUnion F).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ q ∈ P,((F q).card:ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (P.biUnion F).card ≤ ∑ q ∈ P,(F q).card)
    _ ≤ ∑ _q ∈ P,C*X*Real.exp (-T+4*B S+5*D+8*Real.sqrt (B S*H)) := Finset.sum_le_sum hcell
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end TotientAsymptotic

end

end OAI
