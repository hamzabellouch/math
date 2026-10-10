import OAI.NumberTheory.TotientAsymptotic.ExceptionalValueCount
import OAI.NumberTheory.TotientAsymptotic.HeavyOmegaTail
import OAI.NumberTheory.TotientAsymptotic.SquarePreimageCount

namespace OAI

/-! The concrete regular-value exception used in the Ford counting bootstrap. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- These are exactly the regularity conditions used in the band count;
the preimage conditions hold for every preimage of the value. -/
def CountingRegular (S : ℕ) (X : ℝ) (v : ℕ) : Prop :=
  (v.primeFactorsList.length:ℝ) ≤ 5*B X ∧ SquarefreeAbove v S ∧
    ∀ n : ℕ,0 < n → n.totient=v → SquarefreeAbove n S ∧
      ∀ p ∈ n.primeFactors,IsNormalPrime S p

def nonNormalValues (S x : ℝ) : Finset ℕ :=
  (totientValues x).filter (fun v => ∃ n p : ℕ,0 < n ∧ n.totient=v ∧
    p.Prime ∧ p ∣ n ∧ ¬IsNormalPrime S p)

theorem regular_value_exception_count : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (S X : ℕ),4 ≤ X → Real.exp (Real.exp 1) ≤ X → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬CountingRegular S X v) →
    (Q.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ)+
      (2*X+D*X*B X)/(S+1:ℕ)+((nonNormalValues S X).card:ℝ) := by
  obtain ⟨C,hC,hheavy⟩ := heavy_factor_tail_count
  obtain ⟨D,hD,hsquare⟩ := square_preimage_exception_count
  refine ⟨C,D,hC,hD,?_⟩
  intro S X hX hx Q hQ
  let A := Q.filter (fun v => ¬(v.primeFactorsList.length:ℝ) ≤ 5*B X)
  let Vsq := Q.filter (fun v => ¬SquarefreeAbove v S)
  let Psq := Q.filter (fun v => ∃ n : ℕ,0 < n ∧ n.totient=v ∧ ¬SquarefreeAbove n S)
  have hA : (A.card:ℝ) ≤ C*X*(Real.log X)^(-5/4:ℝ) :=
    hheavy X hX A (by
      intro v hv
      obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
      exact ⟨isTotient_pos (hQ v hv).1,(hQ v hv).2.1,le_of_lt (lt_of_not_ge hbad)⟩)
  have hVsq : (Vsq.card:ℝ) ≤ 2*X/(S+1:ℕ) :=
    large_square_count X S Vsq (by
      intro v hv
      obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
      unfold SquarefreeAbove at hbad
      push Not at hbad
      obtain ⟨p,hp,hSp,hpv⟩ := hbad
      exact ⟨isTotient_pos (hQ v hv).1,(hQ v hv).2.1,p,by exact_mod_cast hSp,hpv⟩)
  have hPsq : (Psq.card:ℝ) ≤ D*X*B X/(S+1:ℕ) :=
    hsquare X hx S Psq (by
      intro v hv
      obtain ⟨hv,n,hn,hφ,hbad⟩ := Finset.mem_filter.mp hv
      unfold SquarefreeAbove at hbad
      push Not at hbad
      obtain ⟨p,hp,hSp,hpn⟩ := hbad
      exact ⟨n,hn,hφ,by exact_mod_cast (hQ v hv).2.1,p,by exact_mod_cast hSp,hpn⟩)
  have hcover : Q ⊆ A ∪ Vsq ∪ Psq ∪ nonNormalValues S X := by
    intro v hv
    by_cases hA' : (v.primeFactorsList.length:ℝ) ≤ 5*B X
    · by_cases hV : SquarefreeAbove v S
      · by_cases hP : ∀ n : ℕ,0 < n → n.totient=v → SquarefreeAbove n S
        · have hbad : ¬∀ n : ℕ,0 < n → n.totient=v → ∀ p ∈ n.primeFactors,IsNormalPrime S p := by
            intro hh
            exact (hQ v hv).2.2 ⟨hA',hV,fun n hn hφ => ⟨hP n hn hφ,hh n hn hφ⟩⟩
          push Not at hbad
          obtain ⟨n,hn,hφ,p,hp,hbad⟩ := hbad
          have hp' := Nat.mem_primeFactors.mp hp
          have hvX : v ∈ totientValues X := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨isTotient_pos (hQ v hv).1,by simpa using (hQ v hv).2.1⟩,(hQ v hv).1⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvX,n,p,hn,hφ,hp'.1,hp'.2.1,hbad⟩)
        · push Not at hP
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hP⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hv,hV⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hA'⟩)))
  have hcard : (Q.card:ℝ) ≤ A.card+Vsq.card+Psq.card+(nonNormalValues S X).card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  calc
    _ ≤ (A.card:ℝ)+Vsq.card+Psq.card+(nonNormalValues S X).card := hcard
    _ ≤ C*X*(Real.log X)^(-5/4:ℝ)+2*X/(S+1:ℕ)+D*X*B X/(S+1:ℕ)+
        (nonNormalValues S X).card := by linarith only [hA,hVsq,hPsq]
    _ = _ := by ring

/-- The complete regular-value exception bound, with every arithmetic input
proved and the remaining scale parameters explicit. -/
theorem regular_value_envelope_bound : ∃ A D C E : ℝ,
    0 < A ∧ 0 < D ∧ 0 < C ∧ 0 < E ∧
    ∀ (S X N J : ℕ),2 < (S:ℝ) → 0 ≤ B S → 16 ≤ X →
    Real.exp (Real.exp 1) ≤ X → 4 ≤ N → (N:ℝ)^2 ≤ X →
    (X:ℝ)^(1/4:ℝ) ≤ N → 1 ≤ J → (X:ℝ) ≤ (2:ℝ)^J →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧ ¬CountingRegular S X v) →
    (Q.card:ℝ) ≤ A*X*(Real.log X)^(-5/4:ℝ)+(2*X+D*X*B X)/(S+1:ℕ)+
      C*dyadicTotientEnvelope J*X/Real.log X*
        (B ((2:ℝ)^(Nat.clog 2 N)))^5*(1+Real.log (Nat.clog 2 N))*(Real.log S)^(-1/6:ℝ)+
      (E*X/Real.log X*(B (2*X))^5*(Real.log S)^(-1/6:ℝ))*
        (1+4*dyadicTotientEnvelope J*(1+Real.log J)) := by
  obtain ⟨A,D,hA,hD,hreg⟩ := regular_value_exception_count
  obtain ⟨C,E,hC,hE,hnorm⟩ := non_normal_value_count_split
  refine ⟨A,D,C,E,hA,hD,hC,hE,?_⟩
  intro S X N J hS hBS hX hx hN hNX hroot hJ hXJ Q hQ
  have hr := hreg S X (by omega) hx Q hQ
  have hn := hnorm S X N J hS hBS hN (by exact_mod_cast hX) hNX hroot hJ hXJ
    (nonNormalValues S X) (by
      intro v hv
      obtain ⟨hv,n,p,hn,hφ,hp,hpn,hbad⟩ := Finset.mem_filter.mp hv
      have hvX := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
      refine ⟨n,p,hn,hφ,hp,hpn,?_,hbad⟩
      exact_mod_cast (by simpa using hvX : v ≤ X))
  linarith only [hr,hn]

end TotientAsymptotic

end

end OAI
